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
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__2;
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
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__22_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_(){
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2____boxed(lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_();
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(lean_object* v_u_130_, lean_object* v_00_u03c3s_131_, lean_object* v_H_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___y_139_; uint8_t v___y_140_; lean_object* v_a_145_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = l_Lean_Expr_consumeMData(v_H_132_);
v___x_149_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v___x_148_);
lean_dec_ref(v___x_148_);
if (lean_obj_tag(v___x_149_) == 1)
{
lean_object* v_val_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_189_; 
v_val_150_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_189_ == 0)
{
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_189_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_val_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_189_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v_snd_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_187_; 
v_snd_154_ = lean_ctor_get(v_val_150_, 1);
v_isSharedCheck_187_ = !lean_is_exclusive(v_val_150_);
if (v_isSharedCheck_187_ == 0)
{
lean_object* v_unused_188_; 
v_unused_188_ = lean_ctor_get(v_val_150_, 0);
lean_dec(v_unused_188_);
v___x_156_ = v_val_150_;
v_isShared_157_ = v_isSharedCheck_187_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_snd_154_);
lean_dec(v_val_150_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_187_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v_snd_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_185_; 
v_snd_158_ = lean_ctor_get(v_snd_154_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v_snd_154_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; 
v_unused_186_ = lean_ctor_get(v_snd_154_, 0);
lean_dec(v_unused_186_);
v___x_160_ = v_snd_154_;
v_isShared_161_ = v_isSharedCheck_185_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_snd_158_);
lean_dec(v_snd_154_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_185_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v_fst_162_; lean_object* v_snd_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_184_; 
v_fst_162_ = lean_ctor_get(v_snd_158_, 0);
v_snd_163_ = lean_ctor_get(v_snd_158_, 1);
v_isSharedCheck_184_ = !lean_is_exclusive(v_snd_158_);
if (v_isSharedCheck_184_ == 0)
{
v___x_165_ = v_snd_158_;
v_isShared_166_ = v_isSharedCheck_184_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_snd_163_);
lean_inc(v_fst_162_);
lean_dec(v_snd_158_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_184_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_167_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4));
v___x_168_ = lean_box(0);
if (v_isShared_157_ == 0)
{
lean_ctor_set_tag(v___x_156_, 1);
lean_ctor_set(v___x_156_, 1, v___x_168_);
lean_ctor_set(v___x_156_, 0, v_u_130_);
v___x_170_ = v___x_156_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_u_130_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_168_);
v___x_170_ = v_reuseFailAlloc_183_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_171_ = l_Lean_mkConst(v___x_167_, v___x_170_);
v___x_172_ = l_Lean_mkAppB(v___x_171_, v_00_u03c3s_131_, v_H_132_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 1, v___x_172_);
lean_ctor_set(v___x_165_, 0, v_snd_163_);
v___x_174_ = v___x_165_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_snd_163_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v___x_172_);
v___x_174_ = v_reuseFailAlloc_182_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_176_; 
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_174_);
lean_ctor_set(v___x_160_, 0, v_fst_162_);
v___x_176_ = v___x_160_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_fst_162_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v___x_174_);
v___x_176_ = v_reuseFailAlloc_181_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_178_; 
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_176_);
v___x_178_ = v___x_152_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_176_);
v___x_178_ = v_reuseFailAlloc_180_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_179_; 
v___x_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
return v___x_179_;
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
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v___x_149_);
v___x_190_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5));
v___x_191_ = lean_box(0);
v___x_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_192_, 0, v_u_130_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
lean_inc_ref(v___x_192_);
v___x_193_ = l_Lean_mkConst(v___x_190_, v___x_192_);
lean_inc_ref(v_00_u03c3s_131_);
v___x_194_ = l_Lean_Expr_app___override(v___x_193_, v_00_u03c3s_131_);
v___x_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
v___x_196_ = 0;
v___x_197_ = lean_box(0);
lean_inc_ref(v___x_195_);
v___x_198_ = l_Lean_Meta_mkFreshExprMVar(v___x_195_, v___x_196_, v___x_197_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_200_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_199_);
lean_dec_ref(v___x_198_);
v___x_200_ = l_Lean_Meta_mkFreshExprMVar(v___x_195_, v___x_196_, v___x_197_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_227_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_227_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_227_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_227_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_205_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7));
lean_inc_ref(v___x_192_);
v___x_206_ = l_Lean_mkConst(v___x_205_, v___x_192_);
lean_inc(v_a_201_);
lean_inc(v_a_199_);
lean_inc_ref(v_H_132_);
lean_inc_ref(v_00_u03c3s_131_);
v___x_207_ = l_Lean_mkApp4(v___x_206_, v_00_u03c3s_131_, v_H_132_, v_a_199_, v_a_201_);
v___x_208_ = lean_box(0);
v___x_209_ = l_Lean_Meta_synthInstance(v___x_207_, v___x_208_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_225_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_225_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_225_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_225_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_214_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9));
v___x_215_ = l_Lean_mkConst(v___x_214_, v___x_192_);
lean_inc(v_a_201_);
lean_inc(v_a_199_);
v___x_216_ = l_Lean_mkApp5(v___x_215_, v_00_u03c3s_131_, v_H_132_, v_a_199_, v_a_201_, v_a_210_);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v_a_201_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v_a_199_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
if (v_isShared_204_ == 0)
{
lean_ctor_set_tag(v___x_203_, 1);
lean_ctor_set(v___x_203_, 0, v___x_218_);
v___x_220_ = v___x_203_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_224_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_222_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_220_);
v___x_222_ = v___x_212_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
else
{
lean_object* v_a_226_; 
lean_del_object(v___x_203_);
lean_dec(v_a_201_);
lean_dec(v_a_199_);
lean_dec_ref(v___x_192_);
lean_dec_ref(v_H_132_);
lean_dec_ref(v_00_u03c3s_131_);
v_a_226_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_226_);
lean_dec_ref(v___x_209_);
v_a_145_ = v_a_226_;
goto v___jp_144_;
}
}
}
else
{
lean_object* v_a_228_; 
lean_dec(v_a_199_);
lean_dec_ref(v___x_192_);
lean_dec_ref(v_H_132_);
lean_dec_ref(v_00_u03c3s_131_);
v_a_228_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_228_);
lean_dec_ref(v___x_200_);
v_a_145_ = v_a_228_;
goto v___jp_144_;
}
}
else
{
lean_object* v_a_229_; 
lean_dec_ref(v___x_195_);
lean_dec_ref(v___x_192_);
lean_dec_ref(v_H_132_);
lean_dec_ref(v_00_u03c3s_131_);
v_a_229_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_229_);
lean_dec_ref(v___x_198_);
v_a_145_ = v_a_229_;
goto v___jp_144_;
}
}
v___jp_138_:
{
if (v___y_140_ == 0)
{
lean_object* v___x_141_; lean_object* v___x_142_; 
lean_dec_ref(v___y_139_);
v___x_141_ = lean_box(0);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
else
{
lean_object* v___x_143_; 
v___x_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_143_, 0, v___y_139_);
return v___x_143_;
}
}
v___jp_144_:
{
uint8_t v___x_146_; 
v___x_146_ = l_Lean_Exception_isInterrupt(v_a_145_);
if (v___x_146_ == 0)
{
uint8_t v___x_147_; 
lean_inc_ref(v_a_145_);
v___x_147_ = l_Lean_Exception_isRuntime(v_a_145_);
v___y_139_ = v_a_145_;
v___y_140_ = v___x_147_;
goto v___jp_138_;
}
else
{
v___y_139_ = v_a_145_;
v___y_140_ = v___x_146_;
goto v___jp_138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___boxed(lean_object* v_u_230_, lean_object* v_00_u03c3s_231_, lean_object* v_H_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(v_u_230_, v_00_u03c3s_231_, v_H_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal(lean_object* v_u_247_, lean_object* v_goals_248_, lean_object* v_00_u03c3s_249_, lean_object* v_T_250_, lean_object* v_Q_251_, lean_object* v_H_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v___x_258_; lean_object* v_fst_259_; lean_object* v_snd_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_300_; 
lean_inc_ref(v_H_252_);
lean_inc_ref(v_Q_251_);
lean_inc_ref(v_00_u03c3s_249_);
lean_inc(v_u_247_);
v___x_258_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_247_, v_00_u03c3s_249_, v_Q_251_, v_H_252_);
v_fst_259_ = lean_ctor_get(v___x_258_, 0);
v_snd_260_ = lean_ctor_get(v___x_258_, 1);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_300_ == 0)
{
v___x_262_ = v___x_258_;
v_isShared_263_ = v_isSharedCheck_300_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_snd_260_);
lean_inc(v_fst_259_);
lean_dec(v___x_258_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_300_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v_goal_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
lean_inc_ref(v_T_250_);
lean_inc(v_fst_259_);
lean_inc_ref(v_00_u03c3s_249_);
lean_inc(v_u_247_);
v_goal_264_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_goal_264_, 0, v_u_247_);
lean_ctor_set(v_goal_264_, 1, v_00_u03c3s_249_);
lean_ctor_set(v_goal_264_, 2, v_fst_259_);
lean_ctor_set(v_goal_264_, 3, v_T_250_);
v___x_265_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_264_);
v___x_266_ = lean_box(0);
v___x_267_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_265_, v___x_266_, v_a_253_, v_a_254_, v_a_255_, v_a_256_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_291_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_291_ == 0)
{
v___x_270_ = v___x_267_;
v_isShared_271_ = v_isSharedCheck_291_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_291_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_272_ = lean_st_ref_take(v_goals_248_);
v___x_273_ = l_Lean_Expr_mvarId_x21(v_a_268_);
v___x_274_ = lean_array_push(v___x_272_, v___x_273_);
v___x_275_ = lean_st_ref_set(v_goals_248_, v___x_274_);
v___x_276_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1));
v___x_277_ = lean_box(0);
lean_inc_n(v_u_247_, 2);
v___x_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_278_, 0, v_u_247_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = l_Lean_mkConst(v___x_276_, v___x_278_);
lean_inc_ref(v_T_250_);
lean_inc_ref(v_H_252_);
lean_inc_ref(v_Q_251_);
lean_inc_ref_n(v_00_u03c3s_249_, 2);
v___x_280_ = l_Lean_mkApp7(v___x_279_, v_00_u03c3s_249_, v_fst_259_, v_Q_251_, v_H_252_, v_T_250_, v_snd_260_, v_a_268_);
v___x_281_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_247_, v_00_u03c3s_249_, v_Q_251_, v_H_252_);
v___x_282_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_282_, 0, v_u_247_);
lean_ctor_set(v___x_282_, 1, v_00_u03c3s_249_);
lean_ctor_set(v___x_282_, 2, v___x_281_);
lean_ctor_set(v___x_282_, 3, v_T_250_);
v___x_283_ = lean_box(0);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___x_280_);
lean_ctor_set(v___x_262_, 0, v___x_282_);
v___x_285_ = v___x_262_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v___x_280_);
v___x_285_ = v_reuseFailAlloc_290_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_283_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_286_);
v___x_288_ = v___x_270_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_del_object(v___x_262_);
lean_dec(v_snd_260_);
lean_dec(v_fst_259_);
lean_dec_ref(v_H_252_);
lean_dec_ref(v_Q_251_);
lean_dec_ref(v_T_250_);
lean_dec_ref(v_00_u03c3s_249_);
lean_dec(v_u_247_);
v_a_292_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_267_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_267_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___boxed(lean_object* v_u_301_, lean_object* v_goals_302_, lean_object* v_00_u03c3s_303_, lean_object* v_T_304_, lean_object* v_Q_305_, lean_object* v_H_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal(v_u_301_, v_goals_302_, v_00_u03c3s_303_, v_T_304_, v_Q_305_, v_H_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_goals_302_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(lean_object* v_msgData_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v___x_319_; lean_object* v_env_320_; lean_object* v___x_321_; lean_object* v_mctx_322_; lean_object* v_lctx_323_; lean_object* v_options_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_319_ = lean_st_ref_get(v___y_317_);
v_env_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc_ref(v_env_320_);
lean_dec(v___x_319_);
v___x_321_ = lean_st_ref_get(v___y_315_);
v_mctx_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc_ref(v_mctx_322_);
lean_dec(v___x_321_);
v_lctx_323_ = lean_ctor_get(v___y_314_, 2);
v_options_324_ = lean_ctor_get(v___y_316_, 2);
lean_inc_ref(v_options_324_);
lean_inc_ref(v_lctx_323_);
v___x_325_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_325_, 0, v_env_320_);
lean_ctor_set(v___x_325_, 1, v_mctx_322_);
lean_ctor_set(v___x_325_, 2, v_lctx_323_);
lean_ctor_set(v___x_325_, 3, v_options_324_);
v___x_326_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v_msgData_313_);
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0___boxed(lean_object* v_msgData_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msgData_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(lean_object* v_msg_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_ref_341_; lean_object* v___x_342_; lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_351_; 
v_ref_341_ = lean_ctor_get(v___y_338_, 5);
v___x_342_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
v_a_343_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_351_ == 0)
{
v___x_345_ = v___x_342_;
v_isShared_346_ = v_isSharedCheck_351_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_342_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_351_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; lean_object* v___x_349_; 
lean_inc(v_ref_341_);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v_ref_341_);
lean_ctor_set(v___x_347_, 1, v_a_343_);
if (v_isShared_346_ == 0)
{
lean_ctor_set_tag(v___x_345_, 1);
lean_ctor_set(v___x_345_, 0, v___x_347_);
v___x_349_ = v___x_345_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg___boxed(lean_object* v_msg_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v_msg_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_358_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__0));
v___x_361_ = l_Lean_stringToMessageData(v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(lean_object* v_goal_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_hyps_368_; lean_object* v___x_369_; 
v_hyps_368_ = lean_ctor_get(v_goal_362_, 2);
lean_inc_ref(v_hyps_368_);
lean_dec_ref(v_goal_362_);
v___x_369_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_hyps_368_);
if (lean_obj_tag(v___x_369_) == 1)
{
lean_object* v_val_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_379_; 
lean_dec_ref(v_hyps_368_);
v_val_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_379_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_379_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_val_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_379_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v_snd_374_; lean_object* v_snd_375_; lean_object* v___x_377_; 
v_snd_374_ = lean_ctor_get(v_val_370_, 1);
lean_inc(v_snd_374_);
lean_dec(v_val_370_);
v_snd_375_ = lean_ctor_get(v_snd_374_, 1);
lean_inc(v_snd_375_);
lean_dec(v_snd_374_);
if (v_isShared_373_ == 0)
{
lean_ctor_set_tag(v___x_372_, 0);
lean_ctor_set(v___x_372_, 0, v_snd_375_);
v___x_377_ = v___x_372_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_snd_375_);
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
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
lean_dec(v___x_369_);
v___x_380_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1, &l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1);
v___x_381_ = l_Lean_MessageData_ofExpr(v_hyps_368_);
v___x_382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_382_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___boxed(lean_object* v_goal_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_goal_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0(lean_object* v_00_u03b1_391_, lean_object* v_msg_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v_msg_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___boxed(lean_object* v_00_u03b1_399_, lean_object* v_msg_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0(v_00_u03b1_399_, v_msg_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0(lean_object* v___x_407_, lean_object* v_snd_408_, lean_object* v_k_409_, uint8_t v___x_410_, lean_object* v___x_411_, lean_object* v___x_412_, lean_object* v___x_413_, lean_object* v___x_414_, lean_object* v___x_415_, lean_object* v___x_416_, lean_object* v_H_417_, lean_object* v_x_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_lctx_424_; lean_object* v___x_425_; uint8_t v___x_426_; lean_object* v___x_427_; 
v_lctx_424_ = lean_ctor_get(v___y_419_, 2);
lean_inc_ref(v___x_407_);
v___x_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_407_);
v___x_426_ = 0;
lean_inc_ref(v_x_418_);
lean_inc_ref(v_lctx_424_);
v___x_427_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_snd_408_, v_lctx_424_, v_x_418_, v___x_425_, v___x_426_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v___x_428_; 
lean_dec_ref(v___x_427_);
lean_inc(v___y_422_);
lean_inc_ref(v___y_421_);
lean_inc(v___y_420_);
lean_inc_ref(v___y_419_);
lean_inc_ref(v_x_418_);
v___x_428_ = lean_apply_6(v_k_409_, v_x_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, lean_box(0));
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v_snd_430_; lean_object* v_fst_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_516_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref(v___x_428_);
v_snd_430_ = lean_ctor_get(v_a_429_, 1);
v_fst_431_ = lean_ctor_get(v_a_429_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v_a_429_);
if (v_isSharedCheck_516_ == 0)
{
v___x_433_ = v_a_429_;
v_isShared_434_ = v_isSharedCheck_516_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_snd_430_);
lean_inc(v_fst_431_);
lean_dec(v_a_429_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_516_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v_fst_435_; lean_object* v_snd_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_515_; 
v_fst_435_ = lean_ctor_get(v_snd_430_, 0);
v_snd_436_ = lean_ctor_get(v_snd_430_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v_snd_430_);
if (v_isSharedCheck_515_ == 0)
{
v___x_438_ = v_snd_430_;
v_isShared_439_ = v_isSharedCheck_515_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_snd_436_);
lean_inc(v_fst_435_);
lean_dec(v_snd_430_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_515_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; 
lean_inc(v_fst_435_);
v___x_440_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_435_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v_fst_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_505_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref(v___x_440_);
v_fst_442_ = lean_ctor_get(v_a_441_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v_a_441_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v_a_441_, 1);
lean_dec(v_unused_506_);
v___x_444_ = v_a_441_;
v_isShared_445_ = v_isSharedCheck_505_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_fst_442_);
lean_dec(v_a_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_505_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; 
lean_inc_ref(v___x_407_);
v___x_446_ = l_Lean_Meta_getLevel(v___x_407_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; lean_object* v___x_452_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_447_);
lean_dec_ref(v___x_446_);
v___x_448_ = lean_unsigned_to_nat(1u);
v___x_449_ = lean_mk_empty_array_with_capacity(v___x_448_);
v___x_450_ = lean_array_push(v___x_449_, v_x_418_);
v___x_451_ = 1;
v___x_452_ = l_Lean_Meta_mkLambdaFVars(v___x_450_, v_snd_436_, v___x_426_, v___x_410_, v___x_426_, v___x_410_, v___x_451_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
lean_dec_ref(v___x_450_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_488_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_488_ == 0)
{
v___x_455_ = v___x_452_;
v_isShared_456_ = v_isSharedCheck_488_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_452_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_488_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v_u_457_; lean_object* v_00_u03c3s_458_; lean_object* v_target_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_486_; 
v_u_457_ = lean_ctor_get(v_fst_435_, 0);
v_00_u03c3s_458_ = lean_ctor_get(v_fst_435_, 1);
v_target_459_ = lean_ctor_get(v_fst_435_, 3);
v_isSharedCheck_486_ = !lean_is_exclusive(v_fst_435_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; 
v_unused_487_ = lean_ctor_get(v_fst_435_, 2);
lean_dec(v_unused_487_);
v___x_461_ = v_fst_435_;
v_isShared_462_ = v_isSharedCheck_486_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_target_459_);
lean_inc(v_00_u03c3s_458_);
lean_inc(v_u_457_);
lean_dec(v_fst_435_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_486_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_463_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_464_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_465_ = l_Lean_Name_mkStr6(v___x_411_, v___x_412_, v___x_413_, v___x_463_, v___x_464_, v___x_414_);
v___x_466_ = lean_box(0);
if (v_isShared_434_ == 0)
{
lean_ctor_set_tag(v___x_433_, 1);
lean_ctor_set(v___x_433_, 1, v___x_466_);
lean_ctor_set(v___x_433_, 0, v_a_447_);
v___x_468_ = v___x_433_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_447_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v___x_466_);
v___x_468_ = v_reuseFailAlloc_485_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
lean_inc_n(v_u_457_, 2);
v___x_469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_469_, 0, v_u_457_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = l_Lean_mkConst(v___x_465_, v___x_469_);
lean_inc_ref(v_target_459_);
lean_inc(v_fst_442_);
lean_inc_ref(v___x_415_);
v___x_471_ = l_Lean_mkApp6(v___x_470_, v___x_415_, v___x_407_, v_fst_442_, v___x_416_, v_target_459_, v_a_453_);
v___x_472_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_457_, v___x_415_, v_fst_442_, v_H_417_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 2, v___x_472_);
v___x_474_ = v___x_461_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_u_457_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_00_u03c3s_458_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_484_, 3, v_target_459_);
v___x_474_ = v_reuseFailAlloc_484_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_476_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v___x_471_);
lean_ctor_set(v___x_444_, 0, v___x_474_);
v___x_476_ = v___x_444_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v___x_471_);
v___x_476_ = v_reuseFailAlloc_483_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_478_; 
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v___x_476_);
lean_ctor_set(v___x_438_, 0, v_fst_431_);
v___x_478_ = v___x_438_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_fst_431_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v___x_476_);
v___x_478_ = v_reuseFailAlloc_482_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_480_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v___x_478_);
v___x_480_ = v___x_455_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
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
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
lean_dec(v_a_447_);
lean_del_object(v___x_444_);
lean_dec(v_fst_442_);
lean_del_object(v___x_438_);
lean_dec(v_fst_435_);
lean_del_object(v___x_433_);
lean_dec(v_fst_431_);
lean_dec_ref(v_H_417_);
lean_dec_ref(v___x_416_);
lean_dec_ref(v___x_415_);
lean_dec_ref(v___x_414_);
lean_dec_ref(v___x_413_);
lean_dec_ref(v___x_412_);
lean_dec_ref(v___x_411_);
lean_dec_ref(v___x_407_);
v_a_489_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_452_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_452_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_del_object(v___x_444_);
lean_dec(v_fst_442_);
lean_del_object(v___x_438_);
lean_dec(v_snd_436_);
lean_dec(v_fst_435_);
lean_del_object(v___x_433_);
lean_dec(v_fst_431_);
lean_dec_ref(v_x_418_);
lean_dec_ref(v_H_417_);
lean_dec_ref(v___x_416_);
lean_dec_ref(v___x_415_);
lean_dec_ref(v___x_414_);
lean_dec_ref(v___x_413_);
lean_dec_ref(v___x_412_);
lean_dec_ref(v___x_411_);
lean_dec_ref(v___x_407_);
v_a_497_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_446_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_446_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_del_object(v___x_438_);
lean_dec(v_snd_436_);
lean_dec(v_fst_435_);
lean_del_object(v___x_433_);
lean_dec(v_fst_431_);
lean_dec_ref(v_x_418_);
lean_dec_ref(v_H_417_);
lean_dec_ref(v___x_416_);
lean_dec_ref(v___x_415_);
lean_dec_ref(v___x_414_);
lean_dec_ref(v___x_413_);
lean_dec_ref(v___x_412_);
lean_dec_ref(v___x_411_);
lean_dec_ref(v___x_407_);
v_a_507_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_440_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_440_);
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
}
else
{
lean_dec_ref(v_x_418_);
lean_dec_ref(v_H_417_);
lean_dec_ref(v___x_416_);
lean_dec_ref(v___x_415_);
lean_dec_ref(v___x_414_);
lean_dec_ref(v___x_413_);
lean_dec_ref(v___x_412_);
lean_dec_ref(v___x_411_);
lean_dec_ref(v___x_407_);
return v___x_428_;
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec_ref(v_x_418_);
lean_dec_ref(v_H_417_);
lean_dec_ref(v___x_416_);
lean_dec_ref(v___x_415_);
lean_dec_ref(v___x_414_);
lean_dec_ref(v___x_413_);
lean_dec_ref(v___x_412_);
lean_dec_ref(v___x_411_);
lean_dec_ref(v_k_409_);
lean_dec_ref(v___x_407_);
v_a_517_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_427_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_427_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_525_ = _args[0];
lean_object* v_snd_526_ = _args[1];
lean_object* v_k_527_ = _args[2];
lean_object* v___x_528_ = _args[3];
lean_object* v___x_529_ = _args[4];
lean_object* v___x_530_ = _args[5];
lean_object* v___x_531_ = _args[6];
lean_object* v___x_532_ = _args[7];
lean_object* v___x_533_ = _args[8];
lean_object* v___x_534_ = _args[9];
lean_object* v_H_535_ = _args[10];
lean_object* v_x_536_ = _args[11];
lean_object* v___y_537_ = _args[12];
lean_object* v___y_538_ = _args[13];
lean_object* v___y_539_ = _args[14];
lean_object* v___y_540_ = _args[15];
lean_object* v___y_541_ = _args[16];
_start:
{
uint8_t v___x_2315__boxed_542_; lean_object* v_res_543_; 
v___x_2315__boxed_542_ = lean_unbox(v___x_528_);
v_res_543_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0(v___x_525_, v_snd_526_, v_k_527_, v___x_2315__boxed_542_, v___x_529_, v___x_530_, v___x_531_, v___x_532_, v___x_533_, v___x_534_, v_H_535_, v_x_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0(lean_object* v_k_544_, lean_object* v_b_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v___x_551_; 
lean_inc(v___y_549_);
lean_inc_ref(v___y_548_);
lean_inc(v___y_547_);
lean_inc_ref(v___y_546_);
v___x_551_ = lean_apply_6(v_k_544_, v_b_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, lean_box(0));
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_552_, lean_object* v_b_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0(v_k_552_, v_b_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(lean_object* v_name_560_, uint8_t v_bi_561_, lean_object* v_type_562_, lean_object* v_k_563_, uint8_t v_kind_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___f_570_; lean_object* v___x_571_; 
v___f_570_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_570_, 0, v_k_563_);
v___x_571_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_560_, v_bi_561_, v_type_562_, v___f_570_, v_kind_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
v_a_580_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_571_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_571_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___boxed(lean_object* v_name_588_, lean_object* v_bi_589_, lean_object* v_type_590_, lean_object* v_k_591_, lean_object* v_kind_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
uint8_t v_bi_boxed_598_; uint8_t v_kind_boxed_599_; lean_object* v_res_600_; 
v_bi_boxed_598_ = lean_unbox(v_bi_589_);
v_kind_boxed_599_ = lean_unbox(v_kind_592_);
v_res_600_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_588_, v_bi_boxed_598_, v_type_590_, v_k_591_, v_kind_boxed_599_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(lean_object* v_name_601_, lean_object* v_type_602_, lean_object* v_k_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
uint8_t v___x_609_; uint8_t v___x_610_; lean_object* v___x_611_; 
v___x_609_ = 0;
v___x_610_ = 0;
v___x_611_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_601_, v___x_609_, v_type_602_, v_k_603_, v___x_610_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg___boxed(lean_object* v_name_612_, lean_object* v_type_613_, lean_object* v_k_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_name_612_, v_type_613_, v_k_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
return v_res_620_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__2));
v___x_629_ = l_Lean_stringToMessageData(v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(lean_object* v_H_630_, lean_object* v_name_631_, lean_object* v_k_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_638_ = l_Lean_Expr_consumeMData(v_H_630_);
v___x_639_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0));
v___x_640_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_641_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1));
v___x_642_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0));
v___x_643_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1));
v___x_644_ = lean_unsigned_to_nat(3u);
v___x_645_ = l_Lean_Expr_isAppOfArity(v___x_638_, v___x_643_, v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec_ref(v___x_638_);
lean_dec_ref(v_k_632_);
lean_dec(v_name_631_);
v___x_646_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3);
v___x_647_ = l_Lean_MessageData_ofExpr(v_H_630_);
v___x_648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_648_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_649_;
}
else
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_name_631_, v_a_635_, v_a_636_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v_fst_652_; lean_object* v_snd_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___f_660_; lean_object* v___x_661_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref(v___x_650_);
v_fst_652_ = lean_ctor_get(v_a_651_, 0);
lean_inc(v_fst_652_);
v_snd_653_ = lean_ctor_get(v_a_651_, 1);
lean_inc(v_snd_653_);
lean_dec(v_a_651_);
v___x_654_ = l_Lean_Expr_appFn_x21(v___x_638_);
v___x_655_ = l_Lean_Expr_appFn_x21(v___x_654_);
v___x_656_ = l_Lean_Expr_appArg_x21(v___x_655_);
lean_dec_ref(v___x_655_);
v___x_657_ = l_Lean_Expr_appArg_x21(v___x_654_);
lean_dec_ref(v___x_654_);
v___x_658_ = l_Lean_Expr_appArg_x21(v___x_638_);
lean_dec_ref(v___x_638_);
v___x_659_ = lean_box(v___x_645_);
lean_inc_ref(v___x_656_);
v___f_660_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0___boxed), 17, 11);
lean_closure_set(v___f_660_, 0, v___x_656_);
lean_closure_set(v___f_660_, 1, v_snd_653_);
lean_closure_set(v___f_660_, 2, v_k_632_);
lean_closure_set(v___f_660_, 3, v___x_659_);
lean_closure_set(v___f_660_, 4, v___x_639_);
lean_closure_set(v___f_660_, 5, v___x_640_);
lean_closure_set(v___f_660_, 6, v___x_641_);
lean_closure_set(v___f_660_, 7, v___x_642_);
lean_closure_set(v___f_660_, 8, v___x_657_);
lean_closure_set(v___f_660_, 9, v___x_658_);
lean_closure_set(v___f_660_, 10, v_H_630_);
v___x_661_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_fst_652_, v___x_656_, v___f_660_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_661_;
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec_ref(v___x_638_);
lean_dec_ref(v_k_632_);
lean_dec_ref(v_H_630_);
v_a_662_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_650_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_650_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___boxed(lean_object* v_H_670_, lean_object* v_name_671_, lean_object* v_k_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(v_H_670_, v_name_671_, v_k_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists(lean_object* v_00_u03b1_679_, lean_object* v_H_680_, lean_object* v_name_681_, lean_object* v_k_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(v_H_680_, v_name_681_, v_k_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___boxed(lean_object* v_00_u03b1_689_, lean_object* v_H_690_, lean_object* v_name_691_, lean_object* v_k_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists(v_00_u03b1_689_, v_H_690_, v_name_691_, v_k_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0(lean_object* v_00_u03b1_699_, lean_object* v_name_700_, uint8_t v_bi_701_, lean_object* v_type_702_, lean_object* v_k_703_, uint8_t v_kind_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_700_, v_bi_701_, v_type_702_, v_k_703_, v_kind_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___boxed(lean_object* v_00_u03b1_711_, lean_object* v_name_712_, lean_object* v_bi_713_, lean_object* v_type_714_, lean_object* v_k_715_, lean_object* v_kind_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
uint8_t v_bi_boxed_722_; uint8_t v_kind_boxed_723_; lean_object* v_res_724_; 
v_bi_boxed_722_ = lean_unbox(v_bi_713_);
v_kind_boxed_723_ = lean_unbox(v_kind_716_);
v_res_724_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0(v_00_u03b1_711_, v_name_712_, v_bi_boxed_722_, v_type_714_, v_k_715_, v_kind_boxed_723_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0(lean_object* v_00_u03b1_725_, lean_object* v_name_726_, lean_object* v_type_727_, lean_object* v_k_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_name_726_, v_type_727_, v_k_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___boxed(lean_object* v_00_u03b1_735_, lean_object* v_name_736_, lean_object* v_type_737_, lean_object* v_k_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0(v_00_u03b1_735_, v_name_736_, v_type_737_, v_k_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
return v_res_744_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_745_ = lean_box(0);
v___x_746_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v___x_745_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg(){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0);
v___x_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___boxed(lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0(lean_object* v_00_u03b1_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___boxed(lean_object* v_00_u03b1_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0(v_00_u03b1_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(lean_object* v___y_767_){
_start:
{
lean_object* v___x_769_; lean_object* v_ngen_770_; lean_object* v_namePrefix_771_; lean_object* v_idx_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_801_; 
v___x_769_ = lean_st_ref_get(v___y_767_);
v_ngen_770_ = lean_ctor_get(v___x_769_, 2);
lean_inc_ref(v_ngen_770_);
lean_dec(v___x_769_);
v_namePrefix_771_ = lean_ctor_get(v_ngen_770_, 0);
v_idx_772_ = lean_ctor_get(v_ngen_770_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_ngen_770_);
if (v_isSharedCheck_801_ == 0)
{
v___x_774_ = v_ngen_770_;
v_isShared_775_ = v_isSharedCheck_801_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_idx_772_);
lean_inc(v_namePrefix_771_);
lean_dec(v_ngen_770_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_801_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v_env_777_; lean_object* v_nextMacroScope_778_; lean_object* v_auxDeclNGen_779_; lean_object* v_traceState_780_; lean_object* v_cache_781_; lean_object* v_messages_782_; lean_object* v_infoState_783_; lean_object* v_snapshotTasks_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_799_; 
v___x_776_ = lean_st_ref_take(v___y_767_);
v_env_777_ = lean_ctor_get(v___x_776_, 0);
v_nextMacroScope_778_ = lean_ctor_get(v___x_776_, 1);
v_auxDeclNGen_779_ = lean_ctor_get(v___x_776_, 3);
v_traceState_780_ = lean_ctor_get(v___x_776_, 4);
v_cache_781_ = lean_ctor_get(v___x_776_, 5);
v_messages_782_ = lean_ctor_get(v___x_776_, 6);
v_infoState_783_ = lean_ctor_get(v___x_776_, 7);
v_snapshotTasks_784_ = lean_ctor_get(v___x_776_, 8);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_799_ == 0)
{
lean_object* v_unused_800_; 
v_unused_800_ = lean_ctor_get(v___x_776_, 2);
lean_dec(v_unused_800_);
v___x_786_ = v___x_776_;
v_isShared_787_ = v_isSharedCheck_799_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_snapshotTasks_784_);
lean_inc(v_infoState_783_);
lean_inc(v_messages_782_);
lean_inc(v_cache_781_);
lean_inc(v_traceState_780_);
lean_inc(v_auxDeclNGen_779_);
lean_inc(v_nextMacroScope_778_);
lean_inc(v_env_777_);
lean_dec(v___x_776_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_799_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v_r_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
lean_inc(v_idx_772_);
lean_inc(v_namePrefix_771_);
v_r_788_ = l_Lean_Name_num___override(v_namePrefix_771_, v_idx_772_);
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_add(v_idx_772_, v___x_789_);
lean_dec(v_idx_772_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v___x_790_);
v___x_792_ = v___x_774_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_namePrefix_771_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v___x_790_);
v___x_792_ = v_reuseFailAlloc_798_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_794_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 2, v___x_792_);
v___x_794_ = v___x_786_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_env_777_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_nextMacroScope_778_);
lean_ctor_set(v_reuseFailAlloc_797_, 2, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_797_, 3, v_auxDeclNGen_779_);
lean_ctor_set(v_reuseFailAlloc_797_, 4, v_traceState_780_);
lean_ctor_set(v_reuseFailAlloc_797_, 5, v_cache_781_);
lean_ctor_set(v_reuseFailAlloc_797_, 6, v_messages_782_);
lean_ctor_set(v_reuseFailAlloc_797_, 7, v_infoState_783_);
lean_ctor_set(v_reuseFailAlloc_797_, 8, v_snapshotTasks_784_);
v___x_794_ = v_reuseFailAlloc_797_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_st_ref_set(v___y_767_, v___x_794_);
v___x_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_796_, 0, v_r_788_);
return v___x_796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg___boxed(lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v___y_802_);
lean_dec(v___y_802_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2(lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v___y_808_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___boxed(lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2(v___y_811_, v___y_812_, v___y_813_, v___y_814_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0(lean_object* v_u_825_, lean_object* v_00_u03c3s_826_, lean_object* v_H_u2081_x27_827_, lean_object* v_k_828_, lean_object* v_H_u2082_x27_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___x_835_; lean_object* v_fst_836_; lean_object* v_snd_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_915_; 
lean_inc_ref(v_H_u2082_x27_829_);
lean_inc_ref(v_H_u2081_x27_827_);
lean_inc_ref(v_00_u03c3s_826_);
lean_inc(v_u_825_);
v___x_835_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_825_, v_00_u03c3s_826_, v_H_u2081_x27_827_, v_H_u2082_x27_829_);
v_fst_836_ = lean_ctor_get(v___x_835_, 0);
v_snd_837_ = lean_ctor_get(v___x_835_, 1);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_915_ == 0)
{
v___x_839_ = v___x_835_;
v_isShared_840_ = v_isSharedCheck_915_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_snd_837_);
lean_inc(v_fst_836_);
lean_dec(v___x_835_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_915_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; 
lean_inc(v___y_833_);
lean_inc_ref(v___y_832_);
lean_inc(v___y_831_);
lean_inc_ref(v___y_830_);
lean_inc(v_fst_836_);
v___x_841_ = lean_apply_6(v_k_828_, v_fst_836_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, lean_box(0));
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v_snd_843_; lean_object* v_fst_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_906_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref(v___x_841_);
v_snd_843_ = lean_ctor_get(v_a_842_, 1);
v_fst_844_ = lean_ctor_get(v_a_842_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v_a_842_);
if (v_isSharedCheck_906_ == 0)
{
v___x_846_ = v_a_842_;
v_isShared_847_ = v_isSharedCheck_906_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_snd_843_);
lean_inc(v_fst_844_);
lean_dec(v_a_842_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_906_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v_fst_848_; lean_object* v_snd_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_905_; 
v_fst_848_ = lean_ctor_get(v_snd_843_, 0);
v_snd_849_ = lean_ctor_get(v_snd_843_, 1);
v_isSharedCheck_905_ = !lean_is_exclusive(v_snd_843_);
if (v_isSharedCheck_905_ == 0)
{
v___x_851_ = v_snd_843_;
v_isShared_852_ = v_isSharedCheck_905_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_snd_849_);
lean_inc(v_fst_848_);
lean_dec(v_snd_843_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_905_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; 
lean_inc(v_fst_848_);
v___x_853_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_848_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_896_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_896_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_896_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_896_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v_fst_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_894_; 
v_fst_858_ = lean_ctor_get(v_a_854_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v_a_854_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; 
v_unused_895_ = lean_ctor_get(v_a_854_, 1);
lean_dec(v_unused_895_);
v___x_860_ = v_a_854_;
v_isShared_861_ = v_isSharedCheck_894_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_fst_858_);
lean_dec(v_a_854_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_894_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v_u_862_; lean_object* v_00_u03c3s_863_; lean_object* v_target_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_892_; 
v_u_862_ = lean_ctor_get(v_fst_848_, 0);
v_00_u03c3s_863_ = lean_ctor_get(v_fst_848_, 1);
v_target_864_ = lean_ctor_get(v_fst_848_, 3);
v_isSharedCheck_892_ = !lean_is_exclusive(v_fst_848_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v_fst_848_, 2);
lean_dec(v_unused_893_);
v___x_866_ = v_fst_848_;
v_isShared_867_ = v_isSharedCheck_892_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_target_864_);
lean_inc(v_00_u03c3s_863_);
lean_inc(v_u_862_);
lean_dec(v_fst_848_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_892_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_868_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1));
v___x_869_ = lean_box(0);
lean_inc(v_u_825_);
if (v_isShared_840_ == 0)
{
lean_ctor_set_tag(v___x_839_, 1);
lean_ctor_set(v___x_839_, 1, v___x_869_);
lean_ctor_set(v___x_839_, 0, v_u_825_);
v___x_871_ = v___x_839_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_u_825_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_869_);
v___x_871_ = v_reuseFailAlloc_891_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_872_ = l_Lean_mkConst(v___x_868_, v___x_871_);
lean_inc_ref(v_target_864_);
lean_inc_ref(v_H_u2082_x27_829_);
lean_inc_ref(v_H_u2081_x27_827_);
lean_inc_n(v_fst_858_, 2);
lean_inc_ref_n(v_00_u03c3s_826_, 2);
v___x_873_ = l_Lean_mkApp8(v___x_872_, v_00_u03c3s_826_, v_fst_858_, v_H_u2081_x27_827_, v_H_u2082_x27_829_, v_fst_836_, v_target_864_, v_snd_837_, v_snd_849_);
lean_inc(v_u_825_);
v___x_874_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_825_, v_00_u03c3s_826_, v_fst_858_, v_H_u2081_x27_827_);
v___x_875_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_825_, v_00_u03c3s_826_, v___x_874_, v_H_u2082_x27_829_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 2, v___x_875_);
v___x_877_ = v___x_866_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_u_862_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_00_u03c3s_863_);
lean_ctor_set(v_reuseFailAlloc_890_, 2, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_890_, 3, v_target_864_);
v___x_877_ = v_reuseFailAlloc_890_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_879_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 1, v_fst_858_);
lean_ctor_set(v___x_860_, 0, v_fst_844_);
v___x_879_ = v___x_860_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_fst_844_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_fst_858_);
v___x_879_ = v_reuseFailAlloc_889_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_881_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v___x_873_);
lean_ctor_set(v___x_851_, 0, v___x_877_);
v___x_881_ = v___x_851_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___x_873_);
v___x_881_ = v_reuseFailAlloc_888_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_883_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v___x_881_);
lean_ctor_set(v___x_846_, 0, v___x_879_);
v___x_883_ = v___x_846_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v___x_881_);
v___x_883_ = v_reuseFailAlloc_887_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_883_);
v___x_885_ = v___x_856_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
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
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_del_object(v___x_851_);
lean_dec(v_snd_849_);
lean_dec(v_fst_848_);
lean_del_object(v___x_846_);
lean_dec(v_fst_844_);
lean_del_object(v___x_839_);
lean_dec(v_snd_837_);
lean_dec(v_fst_836_);
lean_dec_ref(v_H_u2082_x27_829_);
lean_dec_ref(v_H_u2081_x27_827_);
lean_dec_ref(v_00_u03c3s_826_);
lean_dec(v_u_825_);
v_a_897_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_853_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_853_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_del_object(v___x_839_);
lean_dec(v_snd_837_);
lean_dec(v_fst_836_);
lean_dec_ref(v_H_u2082_x27_829_);
lean_dec_ref(v_H_u2081_x27_827_);
lean_dec_ref(v_00_u03c3s_826_);
lean_dec(v_u_825_);
v_a_907_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_841_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_841_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___boxed(lean_object* v_u_916_, lean_object* v_00_u03c3s_917_, lean_object* v_H_u2081_x27_918_, lean_object* v_k_919_, lean_object* v_H_u2082_x27_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0(v_u_916_, v_00_u03c3s_917_, v_H_u2081_x27_918_, v_k_919_, v_H_u2082_x27_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0(lean_object* v_a_929_, lean_object* v_snd_930_, lean_object* v_k_931_, lean_object* v___x_932_, lean_object* v___x_933_, lean_object* v___x_934_, lean_object* v___x_935_, lean_object* v___x_936_, lean_object* v_00_u03c3s_937_, lean_object* v_hyp_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_h_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_lctx_947_; lean_object* v___x_948_; uint8_t v___x_949_; lean_object* v___x_950_; 
v_lctx_947_ = lean_ctor_get(v___y_942_, 2);
lean_inc_ref(v_a_929_);
v___x_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_948_, 0, v_a_929_);
v___x_949_ = 0;
lean_inc_ref(v_h_941_);
lean_inc_ref(v_lctx_947_);
v___x_950_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_snd_930_, v_lctx_947_, v_h_941_, v___x_948_, v___x_949_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v___x_951_; 
lean_dec_ref(v___x_950_);
lean_inc(v___y_945_);
lean_inc_ref(v___y_944_);
lean_inc(v___y_943_);
lean_inc_ref(v___y_942_);
lean_inc_ref(v_h_941_);
lean_inc_ref(v_a_929_);
v___x_951_ = lean_apply_7(v_k_931_, v_a_929_, v_h_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, lean_box(0));
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v_snd_953_; lean_object* v_fst_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_1009_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref(v___x_951_);
v_snd_953_ = lean_ctor_get(v_a_952_, 1);
v_fst_954_ = lean_ctor_get(v_a_952_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_a_952_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_956_ = v_a_952_;
v_isShared_957_ = v_isSharedCheck_1009_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_snd_953_);
lean_inc(v_fst_954_);
lean_dec(v_a_952_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_1009_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v_fst_958_; lean_object* v_snd_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_1008_; 
v_fst_958_ = lean_ctor_get(v_snd_953_, 0);
v_snd_959_ = lean_ctor_get(v_snd_953_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_snd_953_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_961_ = v_snd_953_;
v_isShared_962_ = v_isSharedCheck_1008_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_snd_959_);
lean_inc(v_fst_958_);
lean_dec(v_snd_953_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_1008_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; uint8_t v___x_967_; lean_object* v___x_968_; 
v___x_963_ = lean_unsigned_to_nat(1u);
v___x_964_ = lean_mk_empty_array_with_capacity(v___x_963_);
v___x_965_ = lean_array_push(v___x_964_, v_h_941_);
v___x_966_ = 1;
v___x_967_ = 1;
v___x_968_ = l_Lean_Meta_mkLambdaFVars(v___x_965_, v_snd_959_, v___x_949_, v___x_966_, v___x_949_, v___x_966_, v___x_967_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec_ref(v___x_965_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_999_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_999_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_999_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_999_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v_u_973_; lean_object* v_00_u03c3s_974_; lean_object* v_hyps_975_; lean_object* v_target_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_998_; 
v_u_973_ = lean_ctor_get(v_fst_958_, 0);
v_00_u03c3s_974_ = lean_ctor_get(v_fst_958_, 1);
v_hyps_975_ = lean_ctor_get(v_fst_958_, 2);
v_target_976_ = lean_ctor_get(v_fst_958_, 3);
v_isSharedCheck_998_ = !lean_is_exclusive(v_fst_958_);
if (v_isSharedCheck_998_ == 0)
{
v___x_978_ = v_fst_958_;
v_isShared_979_ = v_isSharedCheck_998_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_target_976_);
lean_inc(v_hyps_975_);
lean_inc(v_00_u03c3s_974_);
lean_inc(v_u_973_);
lean_dec(v_fst_958_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_998_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v_prf_984_; lean_object* v___x_985_; lean_object* v_goal_987_; 
v___x_980_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__0));
v___x_981_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__1));
v___x_982_ = l_Lean_Name_mkStr6(v___x_932_, v___x_933_, v___x_934_, v___x_935_, v___x_980_, v___x_981_);
v___x_983_ = l_Lean_mkConst(v___x_982_, v___x_936_);
lean_inc_ref(v_target_976_);
lean_inc_ref(v_hyp_938_);
lean_inc_ref(v_hyps_975_);
lean_inc_ref(v_00_u03c3s_937_);
v_prf_984_ = l_Lean_mkApp7(v___x_983_, v_00_u03c3s_937_, v_hyps_975_, v_hyp_938_, v_target_976_, v_a_929_, v_a_939_, v_a_969_);
v___x_985_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_a_940_, v_00_u03c3s_937_, v_hyps_975_, v_hyp_938_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 2, v___x_985_);
v_goal_987_ = v___x_978_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_u_973_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_00_u03c3s_974_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_997_, 3, v_target_976_);
v_goal_987_ = v_reuseFailAlloc_997_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_989_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v_prf_984_);
lean_ctor_set(v___x_961_, 0, v_goal_987_);
v___x_989_ = v___x_961_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_goal_987_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_prf_984_);
v___x_989_ = v_reuseFailAlloc_996_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_991_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 1, v___x_989_);
v___x_991_ = v___x_956_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_fst_954_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v___x_989_);
v___x_991_ = v_reuseFailAlloc_995_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_993_; 
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_991_);
v___x_993_ = v___x_971_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_del_object(v___x_961_);
lean_dec(v_fst_958_);
lean_del_object(v___x_956_);
lean_dec(v_fst_954_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec_ref(v_hyp_938_);
lean_dec_ref(v_00_u03c3s_937_);
lean_dec(v___x_936_);
lean_dec_ref(v___x_935_);
lean_dec_ref(v___x_934_);
lean_dec_ref(v___x_933_);
lean_dec_ref(v___x_932_);
lean_dec_ref(v_a_929_);
v_a_1000_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_968_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_968_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec_ref(v_hyp_938_);
lean_dec_ref(v_00_u03c3s_937_);
lean_dec(v___x_936_);
lean_dec_ref(v___x_935_);
lean_dec_ref(v___x_934_);
lean_dec_ref(v___x_933_);
lean_dec_ref(v___x_932_);
lean_dec_ref(v_a_929_);
return v___x_951_;
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec_ref(v_h_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec_ref(v_hyp_938_);
lean_dec_ref(v_00_u03c3s_937_);
lean_dec(v___x_936_);
lean_dec_ref(v___x_935_);
lean_dec_ref(v___x_934_);
lean_dec_ref(v___x_933_);
lean_dec_ref(v___x_932_);
lean_dec_ref(v_k_931_);
lean_dec_ref(v_a_929_);
v_a_1010_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_950_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_950_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_a_1018_ = _args[0];
lean_object* v_snd_1019_ = _args[1];
lean_object* v_k_1020_ = _args[2];
lean_object* v___x_1021_ = _args[3];
lean_object* v___x_1022_ = _args[4];
lean_object* v___x_1023_ = _args[5];
lean_object* v___x_1024_ = _args[6];
lean_object* v___x_1025_ = _args[7];
lean_object* v_00_u03c3s_1026_ = _args[8];
lean_object* v_hyp_1027_ = _args[9];
lean_object* v_a_1028_ = _args[10];
lean_object* v_a_1029_ = _args[11];
lean_object* v_h_1030_ = _args[12];
lean_object* v___y_1031_ = _args[13];
lean_object* v___y_1032_ = _args[14];
lean_object* v___y_1033_ = _args[15];
lean_object* v___y_1034_ = _args[16];
lean_object* v___y_1035_ = _args[17];
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0(v_a_1018_, v_snd_1019_, v_k_1020_, v___x_1021_, v___x_1022_, v___x_1023_, v___x_1024_, v___x_1025_, v_00_u03c3s_1026_, v_hyp_1027_, v_a_1028_, v_a_1029_, v_h_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1036_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_box(0);
v___x_1038_ = l_Lean_mkSort(v___x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0);
v___x_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(lean_object* v_00_u03c3s_1048_, lean_object* v_hyp_1049_, lean_object* v_name_1050_, lean_object* v_k_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref(v___x_1057_);
v___x_1059_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1);
v___x_1060_ = 0;
v___x_1061_ = lean_box(0);
v___x_1062_ = l_Lean_Meta_mkFreshExprMVar(v___x_1059_, v___x_1060_, v___x_1061_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc_n(v_a_1063_, 2);
lean_dec_ref(v___x_1062_);
v___x_1064_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0));
v___x_1065_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_1066_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1));
v___x_1067_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_1068_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3));
v___x_1069_ = lean_box(0);
lean_inc(v_a_1058_);
v___x_1070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1070_, 0, v_a_1058_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
lean_inc_ref(v___x_1070_);
v___x_1071_ = l_Lean_mkConst(v___x_1068_, v___x_1070_);
lean_inc_ref(v_hyp_1049_);
lean_inc_ref(v_00_u03c3s_1048_);
v___x_1072_ = l_Lean_mkApp3(v___x_1071_, v_00_u03c3s_1048_, v_hyp_1049_, v_a_1063_);
v___x_1073_ = lean_box(0);
v___x_1074_ = l_Lean_Meta_synthInstance(v___x_1072_, v___x_1073_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1076_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref(v___x_1074_);
v___x_1076_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_name_1050_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v_fst_1078_; lean_object* v_snd_1079_; lean_object* v___f_1080_; lean_object* v___x_1081_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref(v___x_1076_);
v_fst_1078_ = lean_ctor_get(v_a_1077_, 0);
lean_inc(v_fst_1078_);
v_snd_1079_ = lean_ctor_get(v_a_1077_, 1);
lean_inc(v_snd_1079_);
lean_dec(v_a_1077_);
lean_inc(v_a_1063_);
v___f_1080_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1080_, 0, v_a_1063_);
lean_closure_set(v___f_1080_, 1, v_snd_1079_);
lean_closure_set(v___f_1080_, 2, v_k_1051_);
lean_closure_set(v___f_1080_, 3, v___x_1064_);
lean_closure_set(v___f_1080_, 4, v___x_1065_);
lean_closure_set(v___f_1080_, 5, v___x_1066_);
lean_closure_set(v___f_1080_, 6, v___x_1067_);
lean_closure_set(v___f_1080_, 7, v___x_1070_);
lean_closure_set(v___f_1080_, 8, v_00_u03c3s_1048_);
lean_closure_set(v___f_1080_, 9, v_hyp_1049_);
lean_closure_set(v___f_1080_, 10, v_a_1075_);
lean_closure_set(v___f_1080_, 11, v_a_1058_);
v___x_1081_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_fst_1078_, v_a_1063_, v___f_1080_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
return v___x_1081_;
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec(v_a_1075_);
lean_dec_ref(v___x_1070_);
lean_dec(v_a_1063_);
lean_dec(v_a_1058_);
lean_dec_ref(v_k_1051_);
lean_dec_ref(v_hyp_1049_);
lean_dec_ref(v_00_u03c3s_1048_);
v_a_1082_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1076_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1076_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec_ref(v___x_1070_);
lean_dec(v_a_1063_);
lean_dec(v_a_1058_);
lean_dec_ref(v_k_1051_);
lean_dec(v_name_1050_);
lean_dec_ref(v_hyp_1049_);
lean_dec_ref(v_00_u03c3s_1048_);
v_a_1090_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1074_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1074_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec(v_a_1058_);
lean_dec_ref(v_k_1051_);
lean_dec(v_name_1050_);
lean_dec_ref(v_hyp_1049_);
lean_dec_ref(v_00_u03c3s_1048_);
v_a_1098_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1062_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1062_);
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
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref(v_k_1051_);
lean_dec(v_name_1050_);
lean_dec_ref(v_hyp_1049_);
lean_dec_ref(v_00_u03c3s_1048_);
v_a_1106_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1057_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1057_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___boxed(lean_object* v_00_u03c3s_1114_, lean_object* v_hyp_1115_, lean_object* v_name_1116_, lean_object* v_k_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_1114_, v_hyp_1115_, v_name_1116_, v_k_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3(lean_object* v_u_1132_, lean_object* v_00_u03c3s_1133_, lean_object* v_k_1134_, lean_object* v_x_1135_, lean_object* v___h_u03c6_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_H_x27_1142_; lean_object* v___x_1143_; 
lean_inc_ref(v_00_u03c3s_1133_);
lean_inc(v_u_1132_);
v_H_x27_1142_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_u_1132_, v_00_u03c3s_1133_);
lean_inc(v___y_1140_);
lean_inc_ref(v___y_1139_);
lean_inc(v___y_1138_);
lean_inc_ref(v___y_1137_);
v___x_1143_ = lean_apply_6(v_k_1134_, v_H_x27_1142_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, lean_box(0));
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v_snd_1145_; lean_object* v_fst_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1203_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref(v___x_1143_);
v_snd_1145_ = lean_ctor_get(v_a_1144_, 1);
v_fst_1146_ = lean_ctor_get(v_a_1144_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_a_1144_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1148_ = v_a_1144_;
v_isShared_1149_ = v_isSharedCheck_1203_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_snd_1145_);
lean_inc(v_fst_1146_);
lean_dec(v_a_1144_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1203_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v_fst_1150_; lean_object* v_snd_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1202_; 
v_fst_1150_ = lean_ctor_get(v_snd_1145_, 0);
v_snd_1151_ = lean_ctor_get(v_snd_1145_, 1);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_snd_1145_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1153_ = v_snd_1145_;
v_isShared_1154_ = v_isSharedCheck_1202_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_snd_1151_);
lean_inc(v_fst_1150_);
lean_dec(v_snd_1145_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1202_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; 
lean_inc(v_fst_1150_);
v___x_1155_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_1150_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1193_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1158_ = v___x_1155_;
v_isShared_1159_ = v_isSharedCheck_1193_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1155_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1193_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v_fst_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1191_; 
v_fst_1160_ = lean_ctor_get(v_a_1156_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_a_1156_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; 
v_unused_1192_ = lean_ctor_get(v_a_1156_, 1);
lean_dec(v_unused_1192_);
v___x_1162_ = v_a_1156_;
v_isShared_1163_ = v_isSharedCheck_1191_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_fst_1160_);
lean_dec(v_a_1156_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1191_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v_u_1164_; lean_object* v_00_u03c3s_1165_; lean_object* v_target_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1189_; 
v_u_1164_ = lean_ctor_get(v_fst_1150_, 0);
v_00_u03c3s_1165_ = lean_ctor_get(v_fst_1150_, 1);
v_target_1166_ = lean_ctor_get(v_fst_1150_, 3);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_fst_1150_);
if (v_isSharedCheck_1189_ == 0)
{
lean_object* v_unused_1190_; 
v_unused_1190_ = lean_ctor_get(v_fst_1150_, 2);
lean_dec(v_unused_1190_);
v___x_1168_ = v_fst_1150_;
v_isShared_1169_ = v_isSharedCheck_1189_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_target_1166_);
lean_inc(v_00_u03c3s_1165_);
lean_inc(v_u_1164_);
lean_dec(v_fst_1150_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1189_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1170_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1));
v___x_1171_ = lean_box(0);
if (v_isShared_1149_ == 0)
{
lean_ctor_set_tag(v___x_1148_, 1);
lean_ctor_set(v___x_1148_, 1, v___x_1171_);
lean_ctor_set(v___x_1148_, 0, v_u_1132_);
v___x_1173_ = v___x_1148_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_u_1132_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1174_ = l_Lean_mkConst(v___x_1170_, v___x_1173_);
lean_inc_ref(v_target_1166_);
lean_inc(v_fst_1160_);
v___x_1175_ = l_Lean_mkApp4(v___x_1174_, v_00_u03c3s_1133_, v_fst_1160_, v_target_1166_, v_snd_1151_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 2, v_fst_1160_);
v___x_1177_ = v___x_1168_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_u_1164_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_00_u03c3s_1165_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v_fst_1160_);
lean_ctor_set(v_reuseFailAlloc_1187_, 3, v_target_1166_);
v___x_1177_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1179_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v___x_1175_);
lean_ctor_set(v___x_1162_, 0, v___x_1177_);
v___x_1179_ = v___x_1162_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v___x_1175_);
v___x_1179_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1181_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 1, v___x_1179_);
lean_ctor_set(v___x_1153_, 0, v_fst_1146_);
v___x_1181_ = v___x_1153_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_fst_1146_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1183_; 
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1181_);
v___x_1183_ = v___x_1158_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
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
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_del_object(v___x_1153_);
lean_dec(v_snd_1151_);
lean_dec(v_fst_1150_);
lean_del_object(v___x_1148_);
lean_dec(v_fst_1146_);
lean_dec_ref(v_00_u03c3s_1133_);
lean_dec(v_u_1132_);
v_a_1194_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1155_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1155_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_00_u03c3s_1133_);
lean_dec(v_u_1132_);
return v___x_1143_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___boxed(lean_object* v_u_1204_, lean_object* v_00_u03c3s_1205_, lean_object* v_k_1206_, lean_object* v_x_1207_, lean_object* v___h_u03c6_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3(v_u_1204_, v_00_u03c3s_1205_, v_k_1206_, v_x_1207_, v___h_u03c6_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec_ref(v___h_u03c6_1208_);
lean_dec_ref(v_x_1207_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1(lean_object* v_u_1231_, lean_object* v_00_u03c3s_1232_, lean_object* v_k_1233_, lean_object* v_tail_1234_, lean_object* v_fst_1235_, lean_object* v_H_u2081_x27_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___f_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_inc_ref(v_H_u2081_x27_1236_);
lean_inc_ref_n(v_00_u03c3s_1232_, 2);
lean_inc_n(v_u_1231_, 2);
v___f_1242_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1242_, 0, v_u_1231_);
lean_closure_set(v___f_1242_, 1, v_00_u03c3s_1232_);
lean_closure_set(v___f_1242_, 2, v_H_u2081_x27_1236_);
lean_closure_set(v___f_1242_, 3, v_k_1233_);
v___x_1243_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1243_, 0, v_tail_1234_);
lean_inc_ref(v_fst_1235_);
v___x_1244_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1231_, v_00_u03c3s_1232_, v_fst_1235_, v___x_1243_, v___f_1242_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1290_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1290_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1290_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v_fst_1249_; lean_object* v_snd_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1289_; 
v_fst_1249_ = lean_ctor_get(v_a_1245_, 0);
v_snd_1250_ = lean_ctor_get(v_a_1245_, 1);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_a_1245_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1252_ = v_a_1245_;
v_isShared_1253_ = v_isSharedCheck_1289_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_snd_1250_);
lean_inc(v_fst_1249_);
lean_dec(v_a_1245_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1289_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v_fst_1254_; lean_object* v_snd_1255_; lean_object* v_snd_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1287_; 
v_fst_1254_ = lean_ctor_get(v_snd_1250_, 0);
lean_inc(v_fst_1254_);
v_snd_1255_ = lean_ctor_get(v_fst_1249_, 1);
v_snd_1256_ = lean_ctor_get(v_snd_1250_, 1);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_snd_1250_);
if (v_isSharedCheck_1287_ == 0)
{
lean_object* v_unused_1288_; 
v_unused_1288_ = lean_ctor_get(v_snd_1250_, 0);
lean_dec(v_unused_1288_);
v___x_1258_ = v_snd_1250_;
v_isShared_1259_ = v_isSharedCheck_1287_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_snd_1256_);
lean_dec(v_snd_1250_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1287_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v_u_1260_; lean_object* v_00_u03c3s_1261_; lean_object* v_target_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1285_; 
v_u_1260_ = lean_ctor_get(v_fst_1254_, 0);
v_00_u03c3s_1261_ = lean_ctor_get(v_fst_1254_, 1);
v_target_1262_ = lean_ctor_get(v_fst_1254_, 3);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_fst_1254_);
if (v_isSharedCheck_1285_ == 0)
{
lean_object* v_unused_1286_; 
v_unused_1286_ = lean_ctor_get(v_fst_1254_, 2);
lean_dec(v_unused_1286_);
v___x_1264_ = v_fst_1254_;
v_isShared_1265_ = v_isSharedCheck_1285_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_target_1262_);
lean_inc(v_00_u03c3s_1261_);
lean_inc(v_u_1260_);
lean_dec(v_fst_1254_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1285_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1266_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1));
v___x_1267_ = lean_box(0);
lean_inc_n(v_u_1231_, 2);
v___x_1268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1268_, 0, v_u_1231_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = l_Lean_mkConst(v___x_1266_, v___x_1268_);
lean_inc_ref(v_target_1262_);
lean_inc_ref(v_fst_1235_);
lean_inc_ref(v_H_u2081_x27_1236_);
lean_inc_n(v_snd_1255_, 2);
lean_inc_ref_n(v_00_u03c3s_1232_, 2);
v___x_1270_ = l_Lean_mkApp6(v___x_1269_, v_00_u03c3s_1232_, v_snd_1255_, v_H_u2081_x27_1236_, v_fst_1235_, v_target_1262_, v_snd_1256_);
v___x_1271_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1231_, v_00_u03c3s_1232_, v_snd_1255_, v_fst_1235_);
v___x_1272_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1231_, v_00_u03c3s_1232_, v___x_1271_, v_H_u2081_x27_1236_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 2, v___x_1272_);
v___x_1274_ = v___x_1264_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_u_1260_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_00_u03c3s_1261_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v_target_1262_);
v___x_1274_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1276_; 
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 1, v___x_1270_);
lean_ctor_set(v___x_1258_, 0, v___x_1274_);
v___x_1276_ = v___x_1258_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v___x_1270_);
v___x_1276_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1278_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 1, v___x_1276_);
v___x_1278_ = v___x_1252_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_fst_1249_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1280_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1278_);
v___x_1280_ = v___x_1247_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
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
lean_dec_ref(v_H_u2081_x27_1236_);
lean_dec_ref(v_fst_1235_);
lean_dec_ref(v_00_u03c3s_1232_);
lean_dec(v_u_1231_);
return v___x_1244_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___boxed(lean_object* v_u_1291_, lean_object* v_00_u03c3s_1292_, lean_object* v_k_1293_, lean_object* v_tail_1294_, lean_object* v_fst_1295_, lean_object* v_H_u2081_x27_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1(v_u_1291_, v_00_u03c3s_1292_, v_k_1293_, v_tail_1294_, v_fst_1295_, v_H_u2081_x27_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
return v_res_1302_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__4));
v___x_1313_ = l_Lean_stringToMessageData(v___x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2___boxed(lean_object* v___x_1314_, lean_object* v_tail_1315_, lean_object* v_u_1316_, lean_object* v___x_1317_, lean_object* v_k_1318_, lean_object* v_x_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2(v___x_1314_, v_tail_1315_, v_u_1316_, v___x_1317_, v_k_1318_, v_x_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
return v_res_1325_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__6));
v___x_1328_ = l_Lean_stringToMessageData(v___x_1327_);
return v___x_1328_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__10));
v___x_1337_ = l_Lean_stringToMessageData(v___x_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(lean_object* v_u_1344_, lean_object* v_00_u03c3s_1345_, lean_object* v_H_1346_, lean_object* v_pat_1347_, lean_object* v_k_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
switch(lean_obj_tag(v_pat_1347_))
{
case 0:
{
lean_object* v_name_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1401_; 
v_name_1354_ = lean_ctor_get(v_pat_1347_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_pat_1347_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1356_ = v_pat_1347_;
v_isShared_1357_ = v_isSharedCheck_1401_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_name_1354_);
lean_dec(v_pat_1347_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1401_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___y_1359_; uint8_t v___y_1360_; lean_object* v___y_1366_; lean_object* v_a_1367_; lean_object* v___x_1370_; uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1370_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1);
v___x_1371_ = 0;
v___x_1372_ = lean_box(0);
v___x_1373_ = l_Lean_Meta_mkFreshExprMVar(v___x_1370_, v___x_1371_, v___x_1372_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref(v___x_1373_);
v___x_1375_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3));
v___x_1376_ = lean_box(0);
lean_inc(v_u_1344_);
v___x_1377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1377_, 0, v_u_1344_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v___x_1378_ = l_Lean_mkConst(v___x_1375_, v___x_1377_);
lean_inc_ref(v_H_1346_);
lean_inc_ref(v_00_u03c3s_1345_);
v___x_1379_ = l_Lean_mkApp3(v___x_1378_, v_00_u03c3s_1345_, v_H_1346_, v_a_1374_);
v___x_1380_ = lean_box(0);
v___x_1381_ = l_Lean_Meta_synthInstance(v___x_1379_, v___x_1380_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec_ref(v___x_1381_);
lean_inc(v_name_1354_);
v___x_1382_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1382_, 0, v_name_1354_);
lean_inc_ref(v_k_1348_);
lean_inc_ref(v_H_1346_);
lean_inc_ref(v_00_u03c3s_1345_);
lean_inc(v_u_1344_);
v___x_1383_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1344_, v_00_u03c3s_1345_, v_H_1346_, v___x_1382_, v_k_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_del_object(v___x_1356_);
lean_dec(v_name_1354_);
lean_dec_ref(v_k_1348_);
lean_dec_ref(v_H_1346_);
lean_dec_ref(v_00_u03c3s_1345_);
lean_dec(v_u_1344_);
return v___x_1383_;
}
else
{
lean_object* v_a_1384_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
v___y_1366_ = v___x_1383_;
v_a_1367_ = v_a_1384_;
goto v___jp_1365_;
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
v_a_1385_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1381_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1381_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
lean_inc(v_a_1385_);
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
v___y_1366_ = v___x_1390_;
v_a_1367_ = v_a_1385_;
goto v___jp_1365_;
}
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
v_a_1393_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1373_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1373_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
lean_inc(v_a_1393_);
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
v___y_1366_ = v___x_1398_;
v_a_1367_ = v_a_1393_;
goto v___jp_1365_;
}
}
}
v___jp_1358_:
{
if (v___y_1360_ == 0)
{
lean_object* v___x_1362_; 
lean_dec_ref(v___y_1359_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set_tag(v___x_1356_, 5);
v___x_1362_ = v___x_1356_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_name_1354_);
v___x_1362_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
v_pat_1347_ = v___x_1362_;
goto _start;
}
}
else
{
lean_del_object(v___x_1356_);
lean_dec(v_name_1354_);
lean_dec_ref(v_k_1348_);
lean_dec_ref(v_H_1346_);
lean_dec_ref(v_00_u03c3s_1345_);
lean_dec(v_u_1344_);
return v___y_1359_;
}
}
v___jp_1365_:
{
uint8_t v___x_1368_; 
v___x_1368_ = l_Lean_Exception_isInterrupt(v_a_1367_);
if (v___x_1368_ == 0)
{
uint8_t v___x_1369_; 
v___x_1369_ = l_Lean_Exception_isRuntime(v_a_1367_);
v___y_1359_ = v___y_1366_;
v___y_1360_ = v___x_1369_;
goto v___jp_1358_;
}
else
{
lean_dec_ref(v_a_1367_);
v___y_1359_ = v___y_1366_;
v___y_1360_ = v___x_1368_;
goto v___jp_1358_;
}
}
}
}
case 1:
{
lean_object* v_H_x27_1402_; lean_object* v___x_1403_; 
lean_inc_ref(v_00_u03c3s_1345_);
lean_inc(v_u_1344_);
v_H_x27_1402_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_u_1344_, v_00_u03c3s_1345_);
lean_inc(v_a_1352_);
lean_inc_ref(v_a_1351_);
lean_inc(v_a_1350_);
lean_inc_ref(v_a_1349_);
v___x_1403_ = lean_apply_6(v_k_1348_, v_H_x27_1402_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, lean_box(0));
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v_snd_1405_; lean_object* v_fst_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1464_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref(v___x_1403_);
v_snd_1405_ = lean_ctor_get(v_a_1404_, 1);
v_fst_1406_ = lean_ctor_get(v_a_1404_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_a_1404_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1408_ = v_a_1404_;
v_isShared_1409_ = v_isSharedCheck_1464_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_snd_1405_);
lean_inc(v_fst_1406_);
lean_dec(v_a_1404_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1464_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v_fst_1410_; lean_object* v_snd_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1463_; 
v_fst_1410_ = lean_ctor_get(v_snd_1405_, 0);
v_snd_1411_ = lean_ctor_get(v_snd_1405_, 1);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_snd_1405_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1413_ = v_snd_1405_;
v_isShared_1414_ = v_isSharedCheck_1463_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_snd_1411_);
lean_inc(v_fst_1410_);
lean_dec(v_snd_1405_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1463_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; 
lean_inc(v_fst_1410_);
v___x_1415_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_1410_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1454_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1454_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1454_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v_fst_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1452_; 
v_fst_1420_ = lean_ctor_get(v_a_1416_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_a_1416_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; 
v_unused_1453_ = lean_ctor_get(v_a_1416_, 1);
lean_dec(v_unused_1453_);
v___x_1422_ = v_a_1416_;
v_isShared_1423_ = v_isSharedCheck_1452_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_fst_1420_);
lean_dec(v_a_1416_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1452_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v_u_1424_; lean_object* v_00_u03c3s_1425_; lean_object* v_target_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1450_; 
v_u_1424_ = lean_ctor_get(v_fst_1410_, 0);
v_00_u03c3s_1425_ = lean_ctor_get(v_fst_1410_, 1);
v_target_1426_ = lean_ctor_get(v_fst_1410_, 3);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_fst_1410_);
if (v_isSharedCheck_1450_ == 0)
{
lean_object* v_unused_1451_; 
v_unused_1451_ = lean_ctor_get(v_fst_1410_, 2);
lean_dec(v_unused_1451_);
v___x_1428_ = v_fst_1410_;
v_isShared_1429_ = v_isSharedCheck_1450_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_target_1426_);
lean_inc(v_00_u03c3s_1425_);
lean_inc(v_u_1424_);
lean_dec(v_fst_1410_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1450_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1430_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1));
v___x_1431_ = lean_box(0);
lean_inc(v_u_1344_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set_tag(v___x_1408_, 1);
lean_ctor_set(v___x_1408_, 1, v___x_1431_);
lean_ctor_set(v___x_1408_, 0, v_u_1344_);
v___x_1433_ = v___x_1408_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_u_1344_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1434_ = l_Lean_mkConst(v___x_1430_, v___x_1433_);
lean_inc_ref(v_target_1426_);
lean_inc_ref(v_H_1346_);
lean_inc(v_fst_1420_);
lean_inc_ref(v_00_u03c3s_1345_);
v___x_1435_ = l_Lean_mkApp5(v___x_1434_, v_00_u03c3s_1345_, v_fst_1420_, v_H_1346_, v_target_1426_, v_snd_1411_);
v___x_1436_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1344_, v_00_u03c3s_1345_, v_fst_1420_, v_H_1346_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 2, v___x_1436_);
v___x_1438_ = v___x_1428_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_u_1424_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_00_u03c3s_1425_);
lean_ctor_set(v_reuseFailAlloc_1448_, 2, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1448_, 3, v_target_1426_);
v___x_1438_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1440_; 
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 1, v___x_1435_);
lean_ctor_set(v___x_1422_, 0, v___x_1438_);
v___x_1440_ = v___x_1422_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v___x_1435_);
v___x_1440_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1442_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 1, v___x_1440_);
lean_ctor_set(v___x_1413_, 0, v_fst_1406_);
v___x_1442_ = v___x_1413_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_fst_1406_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1444_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1442_);
v___x_1444_ = v___x_1418_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
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
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_del_object(v___x_1413_);
lean_dec(v_snd_1411_);
lean_dec(v_fst_1410_);
lean_del_object(v___x_1408_);
lean_dec(v_fst_1406_);
lean_dec_ref(v_H_1346_);
lean_dec_ref(v_00_u03c3s_1345_);
lean_dec(v_u_1344_);
v_a_1455_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1415_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1415_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_H_1346_);
lean_dec_ref(v_00_u03c3s_1345_);
lean_dec(v_u_1344_);
return v___x_1403_;
}
}
case 2:
{
lean_object* v_args_1465_; 
v_args_1465_ = lean_ctor_get(v_pat_1347_, 0);
lean_inc(v_args_1465_);
lean_dec_ref(v_pat_1347_);
if (lean_obj_tag(v_args_1465_) == 0)
{
lean_object* v___x_1466_; 
v___x_1466_ = lean_box(1);
v_pat_1347_ = v___x_1466_;
goto _start;
}
else
{
lean_object* v_tail_1468_; 
v_tail_1468_ = lean_ctor_get(v_args_1465_, 1);
if (lean_obj_tag(v_tail_1468_) == 0)
{
lean_object* v_head_1469_; 
v_head_1469_ = lean_ctor_get(v_args_1465_, 0);
lean_inc(v_head_1469_);
lean_dec_ref(v_args_1465_);
v_pat_1347_ = v_head_1469_;
goto _start;
}
else
{
lean_object* v_head_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1564_; 
lean_inc(v_tail_1468_);
v_head_1471_ = lean_ctor_get(v_args_1465_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_args_1465_);
if (v_isSharedCheck_1564_ == 0)
{
lean_object* v_unused_1565_; 
v_unused_1565_ = lean_ctor_get(v_args_1465_, 1);
lean_dec(v_unused_1565_);
v___x_1473_ = v_args_1465_;
v_isShared_1474_ = v_isSharedCheck_1564_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_head_1471_);
lean_dec(v_args_1465_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1564_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; 
lean_inc_ref(v_H_1346_);
lean_inc_ref(v_00_u03c3s_1345_);
lean_inc(v_u_1344_);
v___x_1475_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(v_u_1344_, v_00_u03c3s_1345_, v_H_1346_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref(v___x_1475_);
if (lean_obj_tag(v_a_1476_) == 1)
{
lean_object* v_val_1477_; lean_object* v_snd_1478_; lean_object* v_fst_1479_; lean_object* v_fst_1480_; lean_object* v_snd_1481_; lean_object* v___f_1482_; lean_object* v___x_1483_; 
v_val_1477_ = lean_ctor_get(v_a_1476_, 0);
lean_inc(v_val_1477_);
lean_dec_ref(v_a_1476_);
v_snd_1478_ = lean_ctor_get(v_val_1477_, 1);
lean_inc(v_snd_1478_);
v_fst_1479_ = lean_ctor_get(v_val_1477_, 0);
lean_inc_n(v_fst_1479_, 2);
lean_dec(v_val_1477_);
v_fst_1480_ = lean_ctor_get(v_snd_1478_, 0);
lean_inc_n(v_fst_1480_, 2);
v_snd_1481_ = lean_ctor_get(v_snd_1478_, 1);
lean_inc(v_snd_1481_);
lean_dec(v_snd_1478_);
lean_inc_ref_n(v_00_u03c3s_1345_, 2);
lean_inc_n(v_u_1344_, 2);
v___f_1482_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___boxed), 11, 5);
lean_closure_set(v___f_1482_, 0, v_u_1344_);
lean_closure_set(v___f_1482_, 1, v_00_u03c3s_1345_);
lean_closure_set(v___f_1482_, 2, v_k_1348_);
lean_closure_set(v___f_1482_, 3, v_tail_1468_);
lean_closure_set(v___f_1482_, 4, v_fst_1480_);
v___x_1483_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1344_, v_00_u03c3s_1345_, v_fst_1479_, v_head_1471_, v___f_1482_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1531_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1486_ = v___x_1483_;
v_isShared_1487_ = v_isSharedCheck_1531_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1483_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1531_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v_fst_1488_; lean_object* v_snd_1489_; lean_object* v_fst_1490_; lean_object* v_fst_1491_; lean_object* v_snd_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1530_; 
v_fst_1488_ = lean_ctor_get(v_a_1484_, 0);
lean_inc(v_fst_1488_);
v_snd_1489_ = lean_ctor_get(v_a_1484_, 1);
lean_inc(v_snd_1489_);
lean_dec(v_a_1484_);
v_fst_1490_ = lean_ctor_get(v_snd_1489_, 0);
lean_inc(v_fst_1490_);
v_fst_1491_ = lean_ctor_get(v_fst_1488_, 0);
v_snd_1492_ = lean_ctor_get(v_fst_1488_, 1);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_fst_1488_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1494_ = v_fst_1488_;
v_isShared_1495_ = v_isSharedCheck_1530_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_snd_1492_);
lean_inc(v_fst_1491_);
lean_dec(v_fst_1488_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1530_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v_snd_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1528_; 
v_snd_1496_ = lean_ctor_get(v_snd_1489_, 1);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_snd_1489_);
if (v_isSharedCheck_1528_ == 0)
{
lean_object* v_unused_1529_; 
v_unused_1529_ = lean_ctor_get(v_snd_1489_, 0);
lean_dec(v_unused_1529_);
v___x_1498_ = v_snd_1489_;
v_isShared_1499_ = v_isSharedCheck_1528_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_snd_1496_);
lean_dec(v_snd_1489_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1528_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v_u_1500_; lean_object* v_00_u03c3s_1501_; lean_object* v_target_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1526_; 
v_u_1500_ = lean_ctor_get(v_fst_1490_, 0);
v_00_u03c3s_1501_ = lean_ctor_get(v_fst_1490_, 1);
v_target_1502_ = lean_ctor_get(v_fst_1490_, 3);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_fst_1490_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; 
v_unused_1527_ = lean_ctor_get(v_fst_1490_, 2);
lean_dec(v_unused_1527_);
v___x_1504_ = v_fst_1490_;
v_isShared_1505_ = v_isSharedCheck_1526_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_target_1502_);
lean_inc(v_00_u03c3s_1501_);
lean_inc(v_u_1500_);
lean_dec(v_fst_1490_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1526_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1506_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3));
v___x_1507_ = lean_box(0);
lean_inc(v_u_1344_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 1, v___x_1507_);
lean_ctor_set(v___x_1473_, 0, v_u_1344_);
v___x_1509_ = v___x_1473_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_u_1344_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1510_ = l_Lean_mkConst(v___x_1506_, v___x_1509_);
lean_inc_ref(v_target_1502_);
lean_inc_ref(v_H_1346_);
lean_inc(v_snd_1492_);
lean_inc_ref(v_00_u03c3s_1345_);
v___x_1511_ = l_Lean_mkApp8(v___x_1510_, v_00_u03c3s_1345_, v_snd_1492_, v_fst_1479_, v_fst_1480_, v_H_1346_, v_target_1502_, v_snd_1481_, v_snd_1496_);
v___x_1512_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1344_, v_00_u03c3s_1345_, v_snd_1492_, v_H_1346_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 2, v___x_1512_);
v___x_1514_ = v___x_1504_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_u_1500_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_00_u03c3s_1501_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_target_1502_);
v___x_1514_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1516_; 
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 1, v___x_1511_);
lean_ctor_set(v___x_1498_, 0, v___x_1514_);
v___x_1516_ = v___x_1498_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v___x_1511_);
v___x_1516_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1518_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v___x_1516_);
v___x_1518_ = v___x_1494_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_fst_1491_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1520_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1518_);
v___x_1520_ = v___x_1486_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
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
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec(v_snd_1481_);
lean_dec(v_fst_1480_);
lean_dec(v_fst_1479_);
lean_del_object(v___x_1473_);
lean_dec_ref(v_H_1346_);
lean_dec_ref(v_00_u03c3s_1345_);
lean_dec(v_u_1344_);
v_a_1532_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1483_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1483_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
lean_dec(v_a_1476_);
lean_del_object(v___x_1473_);
lean_dec_ref(v_00_u03c3s_1345_);
v___x_1540_ = l_Lean_Expr_consumeMData(v_H_1346_);
v___x_1541_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1));
v___x_1542_ = lean_unsigned_to_nat(3u);
v___x_1543_ = l_Lean_Expr_isAppOfArity(v___x_1540_, v___x_1541_, v___x_1542_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
lean_dec_ref(v___x_1540_);
lean_dec(v_head_1471_);
lean_dec(v_tail_1468_);
lean_dec_ref(v_k_1348_);
lean_dec(v_u_1344_);
v___x_1544_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5);
v___x_1545_ = l_Lean_MessageData_ofExpr(v_H_1346_);
v___x_1546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1544_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_1546_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
return v___x_1547_;
}
else
{
if (lean_obj_tag(v_head_1471_) == 0)
{
lean_object* v_name_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___f_1552_; lean_object* v___x_1553_; 
v_name_1548_ = lean_ctor_get(v_head_1471_, 0);
lean_inc(v_name_1548_);
lean_dec_ref(v_head_1471_);
v___x_1549_ = l_Lean_Expr_appFn_x21(v___x_1540_);
v___x_1550_ = l_Lean_Expr_appArg_x21(v___x_1549_);
lean_dec_ref(v___x_1549_);
v___x_1551_ = l_Lean_Expr_appArg_x21(v___x_1540_);
lean_dec_ref(v___x_1540_);
v___f_1552_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2___boxed), 11, 5);
lean_closure_set(v___f_1552_, 0, v___x_1551_);
lean_closure_set(v___f_1552_, 1, v_tail_1468_);
lean_closure_set(v___f_1552_, 2, v_u_1344_);
lean_closure_set(v___f_1552_, 3, v___x_1550_);
lean_closure_set(v___f_1552_, 4, v_k_1348_);
v___x_1553_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(v_H_1346_, v_name_1548_, v___f_1552_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
return v___x_1553_;
}
else
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
lean_dec_ref(v___x_1540_);
lean_dec(v_head_1471_);
lean_dec(v_tail_1468_);
lean_dec_ref(v_k_1348_);
lean_dec_ref(v_H_1346_);
lean_dec(v_u_1344_);
v___x_1554_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7);
v___x_1555_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_1554_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
return v___x_1555_;
}
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_del_object(v___x_1473_);
lean_dec(v_head_1471_);
lean_dec(v_tail_1468_);
lean_dec_ref(v_k_1348_);
lean_dec_ref(v_H_1346_);
lean_dec_ref(v_00_u03c3s_1345_);
lean_dec(v_u_1344_);
v_a_1556_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1475_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1475_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
}
}
case 3:
{
lean_object* v_args_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1661_; 
v_args_1566_ = lean_ctor_get(v_pat_1347_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_pat_1347_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1568_ = v_pat_1347_;
v_isShared_1569_ = v_isSharedCheck_1661_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_args_1566_);
lean_dec(v_pat_1347_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1661_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
if (lean_obj_tag(v_args_1566_) == 0)
{
lean_object* v___x_1570_; 
lean_del_object(v___x_1568_);
lean_dec_ref(v_k_1348_);
lean_dec_ref(v_H_1346_);
lean_dec_ref(v_00_u03c3s_1345_);
lean_dec(v_u_1344_);
v___x_1570_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
return v___x_1570_;
}
else
{
lean_object* v_tail_1571_; 
v_tail_1571_ = lean_ctor_get(v_args_1566_, 1);
if (lean_obj_tag(v_tail_1571_) == 0)
{
lean_object* v_head_1572_; 
lean_del_object(v___x_1568_);
v_head_1572_ = lean_ctor_get(v_args_1566_, 0);
lean_inc(v_head_1572_);
lean_dec_ref(v_args_1566_);
v_pat_1347_ = v_head_1572_;
goto _start;
}
else
{
lean_object* v_head_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1659_; 
lean_inc(v_tail_1571_);
lean_dec_ref(v_00_u03c3s_1345_);
v_head_1574_ = lean_ctor_get(v_args_1566_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_args_1566_);
if (v_isSharedCheck_1659_ == 0)
{
lean_object* v_unused_1660_; 
v_unused_1660_ = lean_ctor_get(v_args_1566_, 1);
lean_dec(v_unused_1660_);
v___x_1576_ = v_args_1566_;
v_isShared_1577_ = v_isSharedCheck_1659_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_head_1574_);
lean_dec(v_args_1566_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1659_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; 
v___x_1578_ = l_Lean_Expr_consumeMData(v_H_1346_);
v___x_1579_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9));
v___x_1580_ = lean_unsigned_to_nat(3u);
v___x_1581_ = l_Lean_Expr_isAppOfArity(v___x_1578_, v___x_1579_, v___x_1580_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_dec_ref(v___x_1578_);
lean_del_object(v___x_1576_);
lean_dec(v_head_1574_);
lean_dec(v_tail_1571_);
lean_del_object(v___x_1568_);
lean_dec_ref(v_k_1348_);
lean_dec(v_u_1344_);
v___x_1582_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11);
v___x_1583_ = l_Lean_MessageData_ofExpr(v_H_1346_);
v___x_1584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_1584_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
return v___x_1585_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec_ref(v_H_1346_);
v___x_1586_ = l_Lean_Expr_appFn_x21(v___x_1578_);
v___x_1587_ = l_Lean_Expr_appFn_x21(v___x_1586_);
v___x_1588_ = l_Lean_Expr_appArg_x21(v___x_1587_);
lean_dec_ref(v___x_1587_);
v___x_1589_ = l_Lean_Expr_appArg_x21(v___x_1586_);
lean_dec_ref(v___x_1586_);
lean_inc_ref(v_k_1348_);
lean_inc_ref(v___x_1589_);
lean_inc_ref(v___x_1588_);
lean_inc(v_u_1344_);
v___x_1590_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1344_, v___x_1588_, v___x_1589_, v_head_1574_, v_k_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v_snd_1592_; lean_object* v_fst_1593_; lean_object* v_snd_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref(v___x_1590_);
v_snd_1592_ = lean_ctor_get(v_a_1591_, 1);
lean_inc(v_snd_1592_);
lean_dec(v_a_1591_);
v_fst_1593_ = lean_ctor_get(v_snd_1592_, 0);
lean_inc(v_fst_1593_);
v_snd_1594_ = lean_ctor_get(v_snd_1592_, 1);
lean_inc(v_snd_1594_);
lean_dec(v_snd_1592_);
v___x_1595_ = l_Lean_Expr_appArg_x21(v___x_1578_);
lean_dec_ref(v___x_1578_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v_tail_1571_);
v___x_1597_ = v___x_1568_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_tail_1571_);
v___x_1597_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; 
lean_inc_ref(v___x_1595_);
lean_inc_ref(v___x_1588_);
lean_inc(v_u_1344_);
v___x_1598_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1344_, v___x_1588_, v___x_1595_, v___x_1597_, v_k_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v_snd_1600_; lean_object* v_fst_1601_; lean_object* v_snd_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1656_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref(v___x_1598_);
v_snd_1600_ = lean_ctor_get(v_a_1599_, 1);
lean_inc(v_snd_1600_);
v_fst_1601_ = lean_ctor_get(v_a_1599_, 0);
lean_inc(v_fst_1601_);
lean_dec(v_a_1599_);
v_snd_1602_ = lean_ctor_get(v_snd_1600_, 1);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_snd_1600_);
if (v_isSharedCheck_1656_ == 0)
{
lean_object* v_unused_1657_; 
v_unused_1657_ = lean_ctor_get(v_snd_1600_, 0);
lean_dec(v_unused_1657_);
v___x_1604_ = v_snd_1600_;
v_isShared_1605_ = v_isSharedCheck_1656_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_snd_1602_);
lean_dec(v_snd_1600_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1656_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; 
lean_inc(v_fst_1593_);
v___x_1606_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_1593_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1647_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1609_ = v___x_1606_;
v_isShared_1610_ = v_isSharedCheck_1647_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1647_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v_fst_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1645_; 
v_fst_1611_ = lean_ctor_get(v_a_1607_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_a_1607_);
if (v_isSharedCheck_1645_ == 0)
{
lean_object* v_unused_1646_; 
v_unused_1646_ = lean_ctor_get(v_a_1607_, 1);
lean_dec(v_unused_1646_);
v___x_1613_ = v_a_1607_;
v_isShared_1614_ = v_isSharedCheck_1645_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_fst_1611_);
lean_dec(v_a_1607_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1645_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v_u_1615_; lean_object* v_00_u03c3s_1616_; lean_object* v_target_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1643_; 
v_u_1615_ = lean_ctor_get(v_fst_1593_, 0);
v_00_u03c3s_1616_ = lean_ctor_get(v_fst_1593_, 1);
v_target_1617_ = lean_ctor_get(v_fst_1593_, 3);
v_isSharedCheck_1643_ = !lean_is_exclusive(v_fst_1593_);
if (v_isSharedCheck_1643_ == 0)
{
lean_object* v_unused_1644_; 
v_unused_1644_ = lean_ctor_get(v_fst_1593_, 2);
lean_dec(v_unused_1644_);
v___x_1619_ = v_fst_1593_;
v_isShared_1620_ = v_isSharedCheck_1643_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_target_1617_);
lean_inc(v_00_u03c3s_1616_);
lean_inc(v_u_1615_);
lean_dec(v_fst_1593_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1643_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1621_ = lean_box(0);
lean_inc(v_u_1344_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 1, v___x_1621_);
lean_ctor_set(v___x_1576_, 0, v_u_1344_);
v___x_1623_ = v___x_1576_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_u_1344_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
lean_inc_ref(v___x_1623_);
v___x_1624_ = l_Lean_mkConst(v___x_1579_, v___x_1623_);
lean_inc_ref(v___x_1595_);
lean_inc_ref(v___x_1589_);
lean_inc_ref_n(v___x_1588_, 2);
v___x_1625_ = l_Lean_mkApp3(v___x_1624_, v___x_1588_, v___x_1589_, v___x_1595_);
lean_inc(v_fst_1611_);
v___x_1626_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1344_, v___x_1588_, v_fst_1611_, v___x_1625_);
lean_inc_ref(v_target_1617_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 2, v___x_1626_);
v___x_1628_ = v___x_1619_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_u_1615_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_00_u03c3s_1616_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v___x_1626_);
lean_ctor_set(v_reuseFailAlloc_1641_, 3, v_target_1617_);
v___x_1628_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1629_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13));
v___x_1630_ = l_Lean_mkConst(v___x_1629_, v___x_1623_);
v___x_1631_ = l_Lean_mkApp7(v___x_1630_, v___x_1588_, v_fst_1611_, v___x_1589_, v___x_1595_, v_target_1617_, v_snd_1594_, v_snd_1602_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 1, v___x_1631_);
lean_ctor_set(v___x_1613_, 0, v___x_1628_);
v___x_1633_ = v___x_1613_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1635_; 
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 1, v___x_1633_);
lean_ctor_set(v___x_1604_, 0, v_fst_1601_);
v___x_1635_ = v___x_1604_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_fst_1601_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1637_; 
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1635_);
v___x_1637_ = v___x_1609_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
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
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_del_object(v___x_1604_);
lean_dec(v_snd_1602_);
lean_dec(v_fst_1601_);
lean_dec_ref(v___x_1595_);
lean_dec(v_snd_1594_);
lean_dec(v_fst_1593_);
lean_dec_ref(v___x_1589_);
lean_dec_ref(v___x_1588_);
lean_del_object(v___x_1576_);
lean_dec(v_u_1344_);
v_a_1648_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1606_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1606_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1595_);
lean_dec(v_snd_1594_);
lean_dec(v_fst_1593_);
lean_dec_ref(v___x_1589_);
lean_dec_ref(v___x_1588_);
lean_del_object(v___x_1576_);
lean_dec(v_u_1344_);
return v___x_1598_;
}
}
}
else
{
lean_dec_ref(v___x_1589_);
lean_dec_ref(v___x_1588_);
lean_dec_ref(v___x_1578_);
lean_del_object(v___x_1576_);
lean_dec(v_tail_1571_);
lean_del_object(v___x_1568_);
lean_dec_ref(v_k_1348_);
lean_dec(v_u_1344_);
return v___x_1590_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_h_1662_; lean_object* v___f_1663_; lean_object* v___x_1664_; 
v_h_1662_ = lean_ctor_get(v_pat_1347_, 0);
lean_inc(v_h_1662_);
lean_dec_ref(v_pat_1347_);
lean_inc_ref(v_00_u03c3s_1345_);
v___f_1663_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___boxed), 10, 3);
lean_closure_set(v___f_1663_, 0, v_u_1344_);
lean_closure_set(v___f_1663_, 1, v_00_u03c3s_1345_);
lean_closure_set(v___f_1663_, 2, v_k_1348_);
v___x_1664_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_1345_, v_H_1346_, v_h_1662_, v___f_1663_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
return v___x_1664_;
}
default: 
{
lean_object* v_h_1665_; lean_object* v___x_1666_; 
lean_dec(v_u_1344_);
v_h_1665_ = lean_ctor_get(v_pat_1347_, 0);
lean_inc(v_h_1665_);
lean_dec_ref(v_pat_1347_);
v___x_1666_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_h_1665_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v_fst_1668_; lean_object* v_snd_1669_; lean_object* v___x_1670_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref(v___x_1666_);
v_fst_1668_ = lean_ctor_get(v_a_1667_, 0);
lean_inc(v_fst_1668_);
v_snd_1669_ = lean_ctor_get(v_a_1667_, 1);
lean_inc(v_snd_1669_);
lean_dec(v_a_1667_);
v___x_1670_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v_a_1352_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; uint8_t v___x_1674_; lean_object* v___x_1675_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref(v___x_1670_);
v___x_1672_ = l_Lean_Expr_consumeMData(v_H_1346_);
lean_dec_ref(v_H_1346_);
v___x_1673_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1673_, 0, v_fst_1668_);
lean_ctor_set(v___x_1673_, 1, v_a_1671_);
lean_ctor_set(v___x_1673_, 2, v___x_1672_);
v___x_1674_ = 1;
lean_inc_ref(v___x_1673_);
v___x_1675_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_snd_1669_, v_00_u03c3s_1345_, v___x_1673_, v___x_1674_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec_ref(v___x_1675_);
v___x_1676_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1673_);
lean_inc(v_a_1352_);
lean_inc_ref(v_a_1351_);
lean_inc(v_a_1350_);
lean_inc_ref(v_a_1349_);
v___x_1677_ = lean_apply_6(v_k_1348_, v___x_1676_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, lean_box(0));
return v___x_1677_;
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec_ref(v___x_1673_);
lean_dec_ref(v_k_1348_);
v_a_1678_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1675_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1675_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_snd_1669_);
lean_dec(v_fst_1668_);
lean_dec_ref(v_k_1348_);
lean_dec_ref(v_H_1346_);
lean_dec_ref(v_00_u03c3s_1345_);
v_a_1686_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1670_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1670_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec_ref(v_k_1348_);
lean_dec_ref(v_H_1346_);
lean_dec_ref(v_00_u03c3s_1345_);
v_a_1694_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1666_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1666_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2(lean_object* v___x_1702_, lean_object* v_tail_1703_, lean_object* v_u_1704_, lean_object* v___x_1705_, lean_object* v_k_1706_, lean_object* v_x_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1713_ = lean_unsigned_to_nat(1u);
v___x_1714_ = lean_mk_empty_array_with_capacity(v___x_1713_);
v___x_1715_ = lean_array_push(v___x_1714_, v_x_1707_);
v___x_1716_ = 0;
v___x_1717_ = l_Lean_Expr_betaRev(v___x_1702_, v___x_1715_, v___x_1716_, v___x_1716_);
lean_dec_ref(v___x_1715_);
v___x_1718_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1718_, 0, v_tail_1703_);
v___x_1719_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1704_, v___x_1705_, v___x_1717_, v___x_1718_, v_k_1706_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___boxed(lean_object* v_u_1720_, lean_object* v_00_u03c3s_1721_, lean_object* v_H_1722_, lean_object* v_pat_1723_, lean_object* v_k_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1720_, v_00_u03c3s_1721_, v_H_1722_, v_pat_1723_, v_k_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore(lean_object* v_00_u03b1_1731_, lean_object* v_u_1732_, lean_object* v_00_u03c3s_1733_, lean_object* v_H_1734_, lean_object* v_pat_1735_, lean_object* v_k_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1732_, v_00_u03c3s_1733_, v_H_1734_, v_pat_1735_, v_k_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___boxed(lean_object* v_00_u03b1_1743_, lean_object* v_u_1744_, lean_object* v_00_u03c3s_1745_, lean_object* v_H_1746_, lean_object* v_pat_1747_, lean_object* v_k_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore(v_00_u03b1_1743_, v_u_1744_, v_00_u03c3s_1745_, v_H_1746_, v_pat_1747_, v_k_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
lean_dec(v_a_1750_);
lean_dec_ref(v_a_1749_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1(lean_object* v_00_u03b1_1755_, lean_object* v_00_u03c3s_1756_, lean_object* v_hyp_1757_, lean_object* v_name_1758_, lean_object* v_k_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_1756_, v_hyp_1757_, v_name_1758_, v_k_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___boxed(lean_object* v_00_u03b1_1766_, lean_object* v_00_u03c3s_1767_, lean_object* v_hyp_1768_, lean_object* v_name_1769_, lean_object* v_k_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1(v_00_u03b1_1766_, v_00_u03c3s_1767_, v_hyp_1768_, v_name_1769_, v_k_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg(){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0);
v___x_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg___boxed(lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0(lean_object* v_00_u03b1_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___boxed(lean_object* v_00_u03b1_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0(v_00_u03b1_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0(lean_object* v_x_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v___x_1814_; 
lean_inc(v___y_1808_);
lean_inc_ref(v___y_1807_);
lean_inc(v___y_1806_);
lean_inc_ref(v___y_1805_);
v___x_1814_ = lean_apply_9(v_x_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, lean_box(0));
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0___boxed(lean_object* v_x_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0(v_x_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(lean_object* v_mvarId_1826_, lean_object* v_x_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v___f_1837_; lean_object* v___x_1838_; 
lean_inc(v___y_1831_);
lean_inc_ref(v___y_1830_);
lean_inc(v___y_1829_);
lean_inc_ref(v___y_1828_);
v___f_1837_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1837_, 0, v_x_1827_);
lean_closure_set(v___f_1837_, 1, v___y_1828_);
lean_closure_set(v___f_1837_, 2, v___y_1829_);
lean_closure_set(v___f_1837_, 3, v___y_1830_);
lean_closure_set(v___f_1837_, 4, v___y_1831_);
v___x_1838_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1826_, v___f_1837_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1838_) == 0)
{
return v___x_1838_;
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___boxed(lean_object* v_mvarId_1847_, lean_object* v_x_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_mvarId_1847_, v_x_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3(lean_object* v_00_u03b1_1859_, lean_object* v_mvarId_1860_, lean_object* v_x_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_mvarId_1860_, v_x_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___boxed(lean_object* v_00_u03b1_1872_, lean_object* v_mvarId_1873_, lean_object* v_x_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3(v_00_u03b1_1872_, v_mvarId_1873_, v_x_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(lean_object* v_x_1885_, lean_object* v_x_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_){
_start:
{
lean_object* v_ks_1889_; lean_object* v_vs_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1914_; 
v_ks_1889_ = lean_ctor_get(v_x_1885_, 0);
v_vs_1890_ = lean_ctor_get(v_x_1885_, 1);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_x_1885_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1892_ = v_x_1885_;
v_isShared_1893_ = v_isSharedCheck_1914_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_vs_1890_);
lean_inc(v_ks_1889_);
lean_dec(v_x_1885_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1914_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1894_ = lean_array_get_size(v_ks_1889_);
v___x_1895_ = lean_nat_dec_lt(v_x_1886_, v___x_1894_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1899_; 
lean_dec(v_x_1886_);
v___x_1896_ = lean_array_push(v_ks_1889_, v_x_1887_);
v___x_1897_ = lean_array_push(v_vs_1890_, v_x_1888_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 1, v___x_1897_);
lean_ctor_set(v___x_1892_, 0, v___x_1896_);
v___x_1899_ = v___x_1892_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
else
{
lean_object* v_k_x27_1901_; uint8_t v___x_1902_; 
v_k_x27_1901_ = lean_array_fget_borrowed(v_ks_1889_, v_x_1886_);
v___x_1902_ = l_Lean_instBEqMVarId_beq(v_x_1887_, v_k_x27_1901_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1904_; 
if (v_isShared_1893_ == 0)
{
v___x_1904_ = v___x_1892_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_ks_1889_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_vs_1890_);
v___x_1904_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_unsigned_to_nat(1u);
v___x_1906_ = lean_nat_add(v_x_1886_, v___x_1905_);
lean_dec(v_x_1886_);
v_x_1885_ = v___x_1904_;
v_x_1886_ = v___x_1906_;
goto _start;
}
}
else
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1912_; 
v___x_1909_ = lean_array_fset(v_ks_1889_, v_x_1886_, v_x_1887_);
v___x_1910_ = lean_array_fset(v_vs_1890_, v_x_1886_, v_x_1888_);
lean_dec(v_x_1886_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 1, v___x_1910_);
lean_ctor_set(v___x_1892_, 0, v___x_1909_);
v___x_1912_ = v___x_1892_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(lean_object* v_n_1915_, lean_object* v_k_1916_, lean_object* v_v_1917_){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_unsigned_to_nat(0u);
v___x_1919_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(v_n_1915_, v___x_1918_, v_k_1916_, v_v_1917_);
return v___x_1919_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0(void){
_start:
{
size_t v___x_1920_; size_t v___x_1921_; size_t v___x_1922_; 
v___x_1920_ = ((size_t)5ULL);
v___x_1921_ = ((size_t)1ULL);
v___x_1922_ = lean_usize_shift_left(v___x_1921_, v___x_1920_);
return v___x_1922_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1(void){
_start:
{
size_t v___x_1923_; size_t v___x_1924_; size_t v___x_1925_; 
v___x_1923_ = ((size_t)1ULL);
v___x_1924_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0);
v___x_1925_ = lean_usize_sub(v___x_1924_, v___x_1923_);
return v___x_1925_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__2(void){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(lean_object* v_x_1927_, size_t v_x_1928_, size_t v_x_1929_, lean_object* v_x_1930_, lean_object* v_x_1931_){
_start:
{
if (lean_obj_tag(v_x_1927_) == 0)
{
lean_object* v_es_1932_; size_t v___x_1933_; size_t v___x_1934_; size_t v___x_1935_; size_t v___x_1936_; lean_object* v_j_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; 
v_es_1932_ = lean_ctor_get(v_x_1927_, 0);
v___x_1933_ = ((size_t)5ULL);
v___x_1934_ = ((size_t)1ULL);
v___x_1935_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1);
v___x_1936_ = lean_usize_land(v_x_1928_, v___x_1935_);
v_j_1937_ = lean_usize_to_nat(v___x_1936_);
v___x_1938_ = lean_array_get_size(v_es_1932_);
v___x_1939_ = lean_nat_dec_lt(v_j_1937_, v___x_1938_);
if (v___x_1939_ == 0)
{
lean_dec(v_j_1937_);
lean_dec(v_x_1931_);
lean_dec(v_x_1930_);
return v_x_1927_;
}
else
{
lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1976_; 
lean_inc_ref(v_es_1932_);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_1976_ == 0)
{
lean_object* v_unused_1977_; 
v_unused_1977_ = lean_ctor_get(v_x_1927_, 0);
lean_dec(v_unused_1977_);
v___x_1941_ = v_x_1927_;
v_isShared_1942_ = v_isSharedCheck_1976_;
goto v_resetjp_1940_;
}
else
{
lean_dec(v_x_1927_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1976_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v_v_1943_; lean_object* v___x_1944_; lean_object* v_xs_x27_1945_; lean_object* v___y_1947_; 
v_v_1943_ = lean_array_fget(v_es_1932_, v_j_1937_);
v___x_1944_ = lean_box(0);
v_xs_x27_1945_ = lean_array_fset(v_es_1932_, v_j_1937_, v___x_1944_);
switch(lean_obj_tag(v_v_1943_))
{
case 0:
{
lean_object* v_key_1952_; lean_object* v_val_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1963_; 
v_key_1952_ = lean_ctor_get(v_v_1943_, 0);
v_val_1953_ = lean_ctor_get(v_v_1943_, 1);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_v_1943_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1955_ = v_v_1943_;
v_isShared_1956_ = v_isSharedCheck_1963_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_val_1953_);
lean_inc(v_key_1952_);
lean_dec(v_v_1943_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1963_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
uint8_t v___x_1957_; 
v___x_1957_ = l_Lean_instBEqMVarId_beq(v_x_1930_, v_key_1952_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
lean_del_object(v___x_1955_);
v___x_1958_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1952_, v_val_1953_, v_x_1930_, v_x_1931_);
v___x_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
v___y_1947_ = v___x_1959_;
goto v___jp_1946_;
}
else
{
lean_object* v___x_1961_; 
lean_dec(v_val_1953_);
lean_dec(v_key_1952_);
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 1, v_x_1931_);
lean_ctor_set(v___x_1955_, 0, v_x_1930_);
v___x_1961_ = v___x_1955_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_x_1930_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v_x_1931_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
v___y_1947_ = v___x_1961_;
goto v___jp_1946_;
}
}
}
}
case 1:
{
lean_object* v_node_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1974_; 
v_node_1964_ = lean_ctor_get(v_v_1943_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_v_1943_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1966_ = v_v_1943_;
v_isShared_1967_ = v_isSharedCheck_1974_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_node_1964_);
lean_dec(v_v_1943_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1974_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
size_t v___x_1968_; size_t v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1968_ = lean_usize_shift_right(v_x_1928_, v___x_1933_);
v___x_1969_ = lean_usize_add(v_x_1929_, v___x_1934_);
v___x_1970_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_node_1964_, v___x_1968_, v___x_1969_, v_x_1930_, v_x_1931_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v___x_1970_);
v___x_1972_ = v___x_1966_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
v___y_1947_ = v___x_1972_;
goto v___jp_1946_;
}
}
}
default: 
{
lean_object* v___x_1975_; 
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v_x_1930_);
lean_ctor_set(v___x_1975_, 1, v_x_1931_);
v___y_1947_ = v___x_1975_;
goto v___jp_1946_;
}
}
v___jp_1946_:
{
lean_object* v___x_1948_; lean_object* v___x_1950_; 
v___x_1948_ = lean_array_fset(v_xs_x27_1945_, v_j_1937_, v___y_1947_);
lean_dec(v_j_1937_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v___x_1948_);
v___x_1950_ = v___x_1941_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1948_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
else
{
lean_object* v_ks_1978_; lean_object* v_vs_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1999_; 
v_ks_1978_ = lean_ctor_get(v_x_1927_, 0);
v_vs_1979_ = lean_ctor_get(v_x_1927_, 1);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1981_ = v_x_1927_;
v_isShared_1982_ = v_isSharedCheck_1999_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_vs_1979_);
lean_inc(v_ks_1978_);
lean_dec(v_x_1927_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1999_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_ks_1978_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v_vs_1979_);
v___x_1984_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v_newNode_1985_; uint8_t v___y_1987_; size_t v___x_1993_; uint8_t v___x_1994_; 
v_newNode_1985_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(v___x_1984_, v_x_1930_, v_x_1931_);
v___x_1993_ = ((size_t)7ULL);
v___x_1994_ = lean_usize_dec_le(v___x_1993_, v_x_1929_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v___x_1995_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1985_);
v___x_1996_ = lean_unsigned_to_nat(4u);
v___x_1997_ = lean_nat_dec_lt(v___x_1995_, v___x_1996_);
lean_dec(v___x_1995_);
v___y_1987_ = v___x_1997_;
goto v___jp_1986_;
}
else
{
v___y_1987_ = v___x_1994_;
goto v___jp_1986_;
}
v___jp_1986_:
{
if (v___y_1987_ == 0)
{
lean_object* v_ks_1988_; lean_object* v_vs_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v_ks_1988_ = lean_ctor_get(v_newNode_1985_, 0);
lean_inc_ref(v_ks_1988_);
v_vs_1989_ = lean_ctor_get(v_newNode_1985_, 1);
lean_inc_ref(v_vs_1989_);
lean_dec_ref(v_newNode_1985_);
v___x_1990_ = lean_unsigned_to_nat(0u);
v___x_1991_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__2);
v___x_1992_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_x_1929_, v_ks_1988_, v_vs_1989_, v___x_1990_, v___x_1991_);
lean_dec_ref(v_vs_1989_);
lean_dec_ref(v_ks_1988_);
return v___x_1992_;
}
else
{
return v_newNode_1985_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(size_t v_depth_2000_, lean_object* v_keys_2001_, lean_object* v_vals_2002_, lean_object* v_i_2003_, lean_object* v_entries_2004_){
_start:
{
lean_object* v___x_2005_; uint8_t v___x_2006_; 
v___x_2005_ = lean_array_get_size(v_keys_2001_);
v___x_2006_ = lean_nat_dec_lt(v_i_2003_, v___x_2005_);
if (v___x_2006_ == 0)
{
lean_dec(v_i_2003_);
return v_entries_2004_;
}
else
{
lean_object* v_k_2007_; lean_object* v_v_2008_; uint64_t v___x_2009_; size_t v_h_2010_; size_t v___x_2011_; lean_object* v___x_2012_; size_t v___x_2013_; size_t v___x_2014_; size_t v___x_2015_; size_t v_h_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v_k_2007_ = lean_array_fget_borrowed(v_keys_2001_, v_i_2003_);
v_v_2008_ = lean_array_fget_borrowed(v_vals_2002_, v_i_2003_);
v___x_2009_ = l_Lean_instHashableMVarId_hash(v_k_2007_);
v_h_2010_ = lean_uint64_to_usize(v___x_2009_);
v___x_2011_ = ((size_t)5ULL);
v___x_2012_ = lean_unsigned_to_nat(1u);
v___x_2013_ = ((size_t)1ULL);
v___x_2014_ = lean_usize_sub(v_depth_2000_, v___x_2013_);
v___x_2015_ = lean_usize_mul(v___x_2011_, v___x_2014_);
v_h_2016_ = lean_usize_shift_right(v_h_2010_, v___x_2015_);
v___x_2017_ = lean_nat_add(v_i_2003_, v___x_2012_);
lean_dec(v_i_2003_);
lean_inc(v_v_2008_);
lean_inc(v_k_2007_);
v___x_2018_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_entries_2004_, v_h_2016_, v_depth_2000_, v_k_2007_, v_v_2008_);
v_i_2003_ = v___x_2017_;
v_entries_2004_ = v___x_2018_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg___boxed(lean_object* v_depth_2020_, lean_object* v_keys_2021_, lean_object* v_vals_2022_, lean_object* v_i_2023_, lean_object* v_entries_2024_){
_start:
{
size_t v_depth_boxed_2025_; lean_object* v_res_2026_; 
v_depth_boxed_2025_ = lean_unbox_usize(v_depth_2020_);
lean_dec(v_depth_2020_);
v_res_2026_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_depth_boxed_2025_, v_keys_2021_, v_vals_2022_, v_i_2023_, v_entries_2024_);
lean_dec_ref(v_vals_2022_);
lean_dec_ref(v_keys_2021_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___boxed(lean_object* v_x_2027_, lean_object* v_x_2028_, lean_object* v_x_2029_, lean_object* v_x_2030_, lean_object* v_x_2031_){
_start:
{
size_t v_x_20585__boxed_2032_; size_t v_x_20586__boxed_2033_; lean_object* v_res_2034_; 
v_x_20585__boxed_2032_ = lean_unbox_usize(v_x_2028_);
lean_dec(v_x_2028_);
v_x_20586__boxed_2033_ = lean_unbox_usize(v_x_2029_);
lean_dec(v_x_2029_);
v_res_2034_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_2027_, v_x_20585__boxed_2032_, v_x_20586__boxed_2033_, v_x_2030_, v_x_2031_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(lean_object* v_x_2035_, lean_object* v_x_2036_, lean_object* v_x_2037_){
_start:
{
uint64_t v___x_2038_; size_t v___x_2039_; size_t v___x_2040_; lean_object* v___x_2041_; 
v___x_2038_ = l_Lean_instHashableMVarId_hash(v_x_2036_);
v___x_2039_ = lean_uint64_to_usize(v___x_2038_);
v___x_2040_ = ((size_t)1ULL);
v___x_2041_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_2035_, v___x_2039_, v___x_2040_, v_x_2036_, v_x_2037_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(lean_object* v_mvarId_2042_, lean_object* v_val_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; lean_object* v_mctx_2047_; lean_object* v_cache_2048_; lean_object* v_zetaDeltaFVarIds_2049_; lean_object* v_postponed_2050_; lean_object* v_diag_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2079_; 
v___x_2046_ = lean_st_ref_take(v___y_2044_);
v_mctx_2047_ = lean_ctor_get(v___x_2046_, 0);
v_cache_2048_ = lean_ctor_get(v___x_2046_, 1);
v_zetaDeltaFVarIds_2049_ = lean_ctor_get(v___x_2046_, 2);
v_postponed_2050_ = lean_ctor_get(v___x_2046_, 3);
v_diag_2051_ = lean_ctor_get(v___x_2046_, 4);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2053_ = v___x_2046_;
v_isShared_2054_ = v_isSharedCheck_2079_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_diag_2051_);
lean_inc(v_postponed_2050_);
lean_inc(v_zetaDeltaFVarIds_2049_);
lean_inc(v_cache_2048_);
lean_inc(v_mctx_2047_);
lean_dec(v___x_2046_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2079_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v_depth_2055_; lean_object* v_levelAssignDepth_2056_; lean_object* v_lmvarCounter_2057_; lean_object* v_mvarCounter_2058_; lean_object* v_lDecls_2059_; lean_object* v_decls_2060_; lean_object* v_userNames_2061_; lean_object* v_lAssignment_2062_; lean_object* v_eAssignment_2063_; lean_object* v_dAssignment_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2078_; 
v_depth_2055_ = lean_ctor_get(v_mctx_2047_, 0);
v_levelAssignDepth_2056_ = lean_ctor_get(v_mctx_2047_, 1);
v_lmvarCounter_2057_ = lean_ctor_get(v_mctx_2047_, 2);
v_mvarCounter_2058_ = lean_ctor_get(v_mctx_2047_, 3);
v_lDecls_2059_ = lean_ctor_get(v_mctx_2047_, 4);
v_decls_2060_ = lean_ctor_get(v_mctx_2047_, 5);
v_userNames_2061_ = lean_ctor_get(v_mctx_2047_, 6);
v_lAssignment_2062_ = lean_ctor_get(v_mctx_2047_, 7);
v_eAssignment_2063_ = lean_ctor_get(v_mctx_2047_, 8);
v_dAssignment_2064_ = lean_ctor_get(v_mctx_2047_, 9);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_mctx_2047_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2066_ = v_mctx_2047_;
v_isShared_2067_ = v_isSharedCheck_2078_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_dAssignment_2064_);
lean_inc(v_eAssignment_2063_);
lean_inc(v_lAssignment_2062_);
lean_inc(v_userNames_2061_);
lean_inc(v_decls_2060_);
lean_inc(v_lDecls_2059_);
lean_inc(v_mvarCounter_2058_);
lean_inc(v_lmvarCounter_2057_);
lean_inc(v_levelAssignDepth_2056_);
lean_inc(v_depth_2055_);
lean_dec(v_mctx_2047_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2078_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2070_; 
v___x_2068_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(v_eAssignment_2063_, v_mvarId_2042_, v_val_2043_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 8, v___x_2068_);
v___x_2070_ = v___x_2066_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_depth_2055_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_levelAssignDepth_2056_);
lean_ctor_set(v_reuseFailAlloc_2077_, 2, v_lmvarCounter_2057_);
lean_ctor_set(v_reuseFailAlloc_2077_, 3, v_mvarCounter_2058_);
lean_ctor_set(v_reuseFailAlloc_2077_, 4, v_lDecls_2059_);
lean_ctor_set(v_reuseFailAlloc_2077_, 5, v_decls_2060_);
lean_ctor_set(v_reuseFailAlloc_2077_, 6, v_userNames_2061_);
lean_ctor_set(v_reuseFailAlloc_2077_, 7, v_lAssignment_2062_);
lean_ctor_set(v_reuseFailAlloc_2077_, 8, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2077_, 9, v_dAssignment_2064_);
v___x_2070_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2072_; 
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2070_);
v___x_2072_ = v___x_2053_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2070_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_cache_2048_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_zetaDeltaFVarIds_2049_);
lean_ctor_set(v_reuseFailAlloc_2076_, 3, v_postponed_2050_);
lean_ctor_set(v_reuseFailAlloc_2076_, 4, v_diag_2051_);
v___x_2072_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2073_ = lean_st_ref_set(v___y_2044_, v___x_2072_);
v___x_2074_ = lean_box(0);
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
return v___x_2075_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg___boxed(lean_object* v_mvarId_2080_, lean_object* v_val_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_mvarId_2080_, v_val_2081_, v___y_2082_);
lean_dec(v___y_2082_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0(lean_object* v_snd_2087_, lean_object* v_hyp_2088_, lean_object* v_a_2089_, lean_object* v_fst_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v___x_2100_; 
lean_inc_ref(v_snd_2087_);
v___x_2100_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(v_snd_2087_, v_hyp_2088_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v_focusHyp_2104_; lean_object* v_restHyps_2105_; lean_object* v_u_2106_; lean_object* v_00_u03c3s_2107_; lean_object* v_target_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref(v___x_2100_);
v___x_2102_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0));
v___x_2103_ = lean_st_mk_ref(v___x_2102_);
v_focusHyp_2104_ = lean_ctor_get(v_a_2101_, 0);
v_restHyps_2105_ = lean_ctor_get(v_a_2101_, 1);
v_u_2106_ = lean_ctor_get(v_snd_2087_, 0);
v_00_u03c3s_2107_ = lean_ctor_get(v_snd_2087_, 1);
v_target_2108_ = lean_ctor_get(v_snd_2087_, 3);
lean_inc_ref(v_restHyps_2105_);
lean_inc_ref(v_target_2108_);
lean_inc_ref_n(v_00_u03c3s_2107_, 2);
lean_inc(v___x_2103_);
lean_inc_n(v_u_2106_, 2);
v___x_2109_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___boxed), 11, 5);
lean_closure_set(v___x_2109_, 0, v_u_2106_);
lean_closure_set(v___x_2109_, 1, v___x_2103_);
lean_closure_set(v___x_2109_, 2, v_00_u03c3s_2107_);
lean_closure_set(v___x_2109_, 3, v_target_2108_);
lean_closure_set(v___x_2109_, 4, v_restHyps_2105_);
lean_inc_ref(v_focusHyp_2104_);
v___x_2110_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_2106_, v_00_u03c3s_2107_, v_focusHyp_2104_, v_a_2089_, v___x_2109_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v_snd_2112_; lean_object* v_snd_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref(v___x_2110_);
v_snd_2112_ = lean_ctor_get(v_a_2111_, 1);
lean_inc(v_snd_2112_);
lean_dec(v_a_2111_);
v_snd_2113_ = lean_ctor_get(v_snd_2112_, 1);
lean_inc(v_snd_2113_);
lean_dec(v_snd_2112_);
v___x_2114_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps(v_a_2101_, v_snd_2087_, v_snd_2113_);
v___x_2115_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_fst_2090_, v___x_2114_, v___y_2096_);
lean_dec_ref(v___x_2115_);
v___x_2116_ = lean_st_ref_get(v___x_2103_);
lean_dec(v___x_2103_);
v___x_2117_ = lean_array_to_list(v___x_2116_);
v___x_2118_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2117_, v___y_2092_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
return v___x_2118_;
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec(v___x_2103_);
lean_dec(v_a_2101_);
lean_dec(v_fst_2090_);
lean_dec_ref(v_snd_2087_);
v_a_2119_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2110_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2110_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec(v_fst_2090_);
lean_dec(v_a_2089_);
lean_dec_ref(v_snd_2087_);
v_a_2127_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2100_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2100_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___boxed(lean_object* v_snd_2135_, lean_object* v_hyp_2136_, lean_object* v_a_2137_, lean_object* v_fst_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0(v_snd_2135_, v_hyp_2136_, v_a_2137_, v_fst_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
return v_res_2148_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2149_; double v___x_2150_; 
v___x_2149_ = lean_unsigned_to_nat(0u);
v___x_2150_ = lean_float_of_nat(v___x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(lean_object* v_cls_2154_, lean_object* v_msg_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v_ref_2161_; lean_object* v___x_2162_; lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2207_; 
v_ref_2161_ = lean_ctor_get(v___y_2158_, 5);
v___x_2162_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2165_ = v___x_2162_;
v_isShared_2166_ = v_isSharedCheck_2207_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2162_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2207_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2167_; lean_object* v_traceState_2168_; lean_object* v_env_2169_; lean_object* v_nextMacroScope_2170_; lean_object* v_ngen_2171_; lean_object* v_auxDeclNGen_2172_; lean_object* v_cache_2173_; lean_object* v_messages_2174_; lean_object* v_infoState_2175_; lean_object* v_snapshotTasks_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2206_; 
v___x_2167_ = lean_st_ref_take(v___y_2159_);
v_traceState_2168_ = lean_ctor_get(v___x_2167_, 4);
v_env_2169_ = lean_ctor_get(v___x_2167_, 0);
v_nextMacroScope_2170_ = lean_ctor_get(v___x_2167_, 1);
v_ngen_2171_ = lean_ctor_get(v___x_2167_, 2);
v_auxDeclNGen_2172_ = lean_ctor_get(v___x_2167_, 3);
v_cache_2173_ = lean_ctor_get(v___x_2167_, 5);
v_messages_2174_ = lean_ctor_get(v___x_2167_, 6);
v_infoState_2175_ = lean_ctor_get(v___x_2167_, 7);
v_snapshotTasks_2176_ = lean_ctor_get(v___x_2167_, 8);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2178_ = v___x_2167_;
v_isShared_2179_ = v_isSharedCheck_2206_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_snapshotTasks_2176_);
lean_inc(v_infoState_2175_);
lean_inc(v_messages_2174_);
lean_inc(v_cache_2173_);
lean_inc(v_traceState_2168_);
lean_inc(v_auxDeclNGen_2172_);
lean_inc(v_ngen_2171_);
lean_inc(v_nextMacroScope_2170_);
lean_inc(v_env_2169_);
lean_dec(v___x_2167_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2206_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
uint64_t v_tid_2180_; lean_object* v_traces_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2205_; 
v_tid_2180_ = lean_ctor_get_uint64(v_traceState_2168_, sizeof(void*)*1);
v_traces_2181_ = lean_ctor_get(v_traceState_2168_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_traceState_2168_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2183_ = v_traceState_2168_;
v_isShared_2184_ = v_isSharedCheck_2205_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_traces_2181_);
lean_dec(v_traceState_2168_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2205_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2185_; double v___x_2186_; uint8_t v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2185_ = lean_box(0);
v___x_2186_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0);
v___x_2187_ = 0;
v___x_2188_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1));
v___x_2189_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2189_, 0, v_cls_2154_);
lean_ctor_set(v___x_2189_, 1, v___x_2185_);
lean_ctor_set(v___x_2189_, 2, v___x_2188_);
lean_ctor_set_float(v___x_2189_, sizeof(void*)*3, v___x_2186_);
lean_ctor_set_float(v___x_2189_, sizeof(void*)*3 + 8, v___x_2186_);
lean_ctor_set_uint8(v___x_2189_, sizeof(void*)*3 + 16, v___x_2187_);
v___x_2190_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__2));
v___x_2191_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set(v___x_2191_, 1, v_a_2163_);
lean_ctor_set(v___x_2191_, 2, v___x_2190_);
lean_inc(v_ref_2161_);
v___x_2192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2192_, 0, v_ref_2161_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
v___x_2193_ = l_Lean_PersistentArray_push___redArg(v_traces_2181_, v___x_2192_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v___x_2193_);
v___x_2195_ = v___x_2183_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2193_);
lean_ctor_set_uint64(v_reuseFailAlloc_2204_, sizeof(void*)*1, v_tid_2180_);
v___x_2195_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2197_; 
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 4, v___x_2195_);
v___x_2197_ = v___x_2178_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_env_2169_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_nextMacroScope_2170_);
lean_ctor_set(v_reuseFailAlloc_2203_, 2, v_ngen_2171_);
lean_ctor_set(v_reuseFailAlloc_2203_, 3, v_auxDeclNGen_2172_);
lean_ctor_set(v_reuseFailAlloc_2203_, 4, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2203_, 5, v_cache_2173_);
lean_ctor_set(v_reuseFailAlloc_2203_, 6, v_messages_2174_);
lean_ctor_set(v_reuseFailAlloc_2203_, 7, v_infoState_2175_);
lean_ctor_set(v_reuseFailAlloc_2203_, 8, v_snapshotTasks_2176_);
v___x_2197_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2201_; 
v___x_2198_ = lean_st_ref_set(v___y_2159_, v___x_2197_);
v___x_2199_ = lean_box(0);
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 0, v___x_2199_);
v___x_2201_ = v___x_2165_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2199_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___boxed(lean_object* v_cls_2208_, lean_object* v_msg_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_2208_, v_msg_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(lean_object* v_as_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
if (lean_obj_tag(v_as_2219_) == 0)
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = lean_box(0);
v___x_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
return v___x_2230_;
}
else
{
lean_object* v_options_2231_; uint8_t v_hasTrace_2232_; 
v_options_2231_ = lean_ctor_get(v___y_2226_, 2);
v_hasTrace_2232_ = lean_ctor_get_uint8(v_options_2231_, sizeof(void*)*1);
if (v_hasTrace_2232_ == 0)
{
lean_object* v_tail_2233_; 
v_tail_2233_ = lean_ctor_get(v_as_2219_, 1);
lean_inc(v_tail_2233_);
lean_dec_ref(v_as_2219_);
v_as_2219_ = v_tail_2233_;
goto _start;
}
else
{
lean_object* v_head_2235_; lean_object* v_tail_2236_; lean_object* v_fst_2237_; lean_object* v_snd_2238_; lean_object* v_inheritedTraceOptions_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; uint8_t v___x_2242_; 
v_head_2235_ = lean_ctor_get(v_as_2219_, 0);
lean_inc(v_head_2235_);
v_tail_2236_ = lean_ctor_get(v_as_2219_, 1);
lean_inc(v_tail_2236_);
lean_dec_ref(v_as_2219_);
v_fst_2237_ = lean_ctor_get(v_head_2235_, 0);
lean_inc_n(v_fst_2237_, 2);
v_snd_2238_ = lean_ctor_get(v_head_2235_, 1);
lean_inc(v_snd_2238_);
lean_dec(v_head_2235_);
v_inheritedTraceOptions_2239_ = lean_ctor_get(v___y_2226_, 13);
v___x_2240_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1));
v___x_2241_ = l_Lean_Name_append(v___x_2240_, v_fst_2237_);
v___x_2242_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2239_, v_options_2231_, v___x_2241_);
lean_dec(v___x_2241_);
if (v___x_2242_ == 0)
{
lean_dec(v_snd_2238_);
lean_dec(v_fst_2237_);
v_as_2219_ = v_tail_2236_;
goto _start;
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2244_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2244_, 0, v_snd_2238_);
v___x_2245_ = l_Lean_MessageData_ofFormat(v___x_2244_);
v___x_2246_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_fst_2237_, v___x_2245_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_dec_ref(v___x_2246_);
v_as_2219_ = v_tail_2236_;
goto _start;
}
else
{
lean_dec(v_tail_2236_);
return v___x_2246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___boxed(lean_object* v_as_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(v_as_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(lean_object* v_x_2259_, lean_object* v___y_2260_){
_start:
{
if (lean_obj_tag(v_x_2259_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2262_; 
v_a_2261_ = lean_ctor_get(v_x_2259_, 0);
lean_inc(v_a_2261_);
v___x_2262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2262_, 0, v_a_2261_);
lean_ctor_set(v___x_2262_, 1, v___y_2260_);
return v___x_2262_;
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2264_; 
v_a_2263_ = lean_ctor_get(v_x_2259_, 0);
lean_inc(v_a_2263_);
v___x_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2264_, 0, v_a_2263_);
lean_ctor_set(v___x_2264_, 1, v___y_2260_);
return v___x_2264_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___boxed(lean_object* v_x_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v_x_2265_, v___y_2266_);
lean_dec_ref(v_x_2265_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(lean_object* v_env_2268_, lean_object* v_stx_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2268_, v_stx_2269_, v___y_2270_, v___y_2271_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
if (lean_obj_tag(v_a_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2282_; 
v_a_2274_ = lean_ctor_get(v___x_2272_, 1);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2282_ == 0)
{
lean_object* v_unused_2283_; 
v_unused_2283_ = lean_ctor_get(v___x_2272_, 0);
lean_dec(v_unused_2283_);
v___x_2276_ = v___x_2272_;
v_isShared_2277_ = v_isSharedCheck_2282_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2272_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2282_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; lean_object* v___x_2280_; 
v___x_2278_ = lean_box(0);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 0, v___x_2278_);
v___x_2280_ = v___x_2276_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2278_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_a_2274_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
else
{
lean_object* v_val_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2312_; 
v_val_2284_ = lean_ctor_get(v_a_2273_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v_a_2273_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2286_ = v_a_2273_;
v_isShared_2287_ = v_isSharedCheck_2312_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_val_2284_);
lean_dec(v_a_2273_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2312_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v_snd_2288_; 
v_snd_2288_ = lean_ctor_get(v_val_2284_, 1);
lean_inc(v_snd_2288_);
lean_dec(v_val_2284_);
if (lean_obj_tag(v_snd_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2298_; 
lean_del_object(v___x_2286_);
v_a_2289_ = lean_ctor_get(v___x_2272_, 1);
lean_inc(v_a_2289_);
lean_dec_ref(v___x_2272_);
v_a_2290_ = lean_ctor_get(v_snd_2288_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v_snd_2288_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2292_ = v_snd_2288_;
v_isShared_2293_ = v_isSharedCheck_2298_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v_snd_2288_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2298_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
lean_object* v___x_2296_; 
v___x_2296_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v___x_2295_, v_a_2289_);
lean_dec_ref(v___x_2295_);
return v___x_2296_;
}
}
}
else
{
lean_object* v_a_2299_; lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2311_; 
v_a_2299_ = lean_ctor_get(v___x_2272_, 1);
lean_inc(v_a_2299_);
lean_dec_ref(v___x_2272_);
v_a_2300_ = lean_ctor_get(v_snd_2288_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v_snd_2288_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2302_ = v_snd_2288_;
v_isShared_2303_ = v_isSharedCheck_2311_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v_snd_2288_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2311_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v_a_2300_);
v___x_2305_ = v___x_2286_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2307_; 
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___x_2305_);
v___x_2307_ = v___x_2302_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v___x_2307_, v_a_2299_);
lean_dec_ref(v___x_2307_);
return v___x_2308_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
v_a_2313_ = lean_ctor_get(v___x_2272_, 0);
v_a_2314_ = lean_ctor_get(v___x_2272_, 1);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2272_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_inc(v_a_2313_);
lean_dec(v___x_2272_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2313_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0___boxed(lean_object* v_env_2322_, lean_object* v_stx_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(v_env_2322_, v_stx_2323_, v___y_2324_, v___y_2325_);
lean_dec_ref(v___y_2324_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(lean_object* v_msg_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v_ref_2333_; lean_object* v___x_2334_; lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2343_; 
v_ref_2333_ = lean_ctor_get(v___y_2330_, 5);
v___x_2334_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2337_ = v___x_2334_;
v_isShared_2338_ = v_isSharedCheck_2343_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2334_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2343_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2339_; lean_object* v___x_2341_; 
lean_inc(v_ref_2333_);
v___x_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2339_, 0, v_ref_2333_);
lean_ctor_set(v___x_2339_, 1, v_a_2335_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set_tag(v___x_2337_, 1);
lean_ctor_set(v___x_2337_, 0, v___x_2339_);
v___x_2341_ = v___x_2337_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2339_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg___boxed(lean_object* v_msg_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(lean_object* v_ref_2351_, lean_object* v_msg_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v_fileName_2362_; lean_object* v_fileMap_2363_; lean_object* v_options_2364_; lean_object* v_currRecDepth_2365_; lean_object* v_maxRecDepth_2366_; lean_object* v_ref_2367_; lean_object* v_currNamespace_2368_; lean_object* v_openDecls_2369_; lean_object* v_initHeartbeats_2370_; lean_object* v_maxHeartbeats_2371_; lean_object* v_quotContext_2372_; lean_object* v_currMacroScope_2373_; uint8_t v_diag_2374_; lean_object* v_cancelTk_x3f_2375_; uint8_t v_suppressElabErrors_2376_; lean_object* v_inheritedTraceOptions_2377_; lean_object* v_ref_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v_fileName_2362_ = lean_ctor_get(v___y_2359_, 0);
v_fileMap_2363_ = lean_ctor_get(v___y_2359_, 1);
v_options_2364_ = lean_ctor_get(v___y_2359_, 2);
v_currRecDepth_2365_ = lean_ctor_get(v___y_2359_, 3);
v_maxRecDepth_2366_ = lean_ctor_get(v___y_2359_, 4);
v_ref_2367_ = lean_ctor_get(v___y_2359_, 5);
v_currNamespace_2368_ = lean_ctor_get(v___y_2359_, 6);
v_openDecls_2369_ = lean_ctor_get(v___y_2359_, 7);
v_initHeartbeats_2370_ = lean_ctor_get(v___y_2359_, 8);
v_maxHeartbeats_2371_ = lean_ctor_get(v___y_2359_, 9);
v_quotContext_2372_ = lean_ctor_get(v___y_2359_, 10);
v_currMacroScope_2373_ = lean_ctor_get(v___y_2359_, 11);
v_diag_2374_ = lean_ctor_get_uint8(v___y_2359_, sizeof(void*)*14);
v_cancelTk_x3f_2375_ = lean_ctor_get(v___y_2359_, 12);
v_suppressElabErrors_2376_ = lean_ctor_get_uint8(v___y_2359_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2377_ = lean_ctor_get(v___y_2359_, 13);
v_ref_2378_ = l_Lean_replaceRef(v_ref_2351_, v_ref_2367_);
lean_inc_ref(v_inheritedTraceOptions_2377_);
lean_inc(v_cancelTk_x3f_2375_);
lean_inc(v_currMacroScope_2373_);
lean_inc(v_quotContext_2372_);
lean_inc(v_maxHeartbeats_2371_);
lean_inc(v_initHeartbeats_2370_);
lean_inc(v_openDecls_2369_);
lean_inc(v_currNamespace_2368_);
lean_inc(v_maxRecDepth_2366_);
lean_inc(v_currRecDepth_2365_);
lean_inc_ref(v_options_2364_);
lean_inc_ref(v_fileMap_2363_);
lean_inc_ref(v_fileName_2362_);
v___x_2379_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2379_, 0, v_fileName_2362_);
lean_ctor_set(v___x_2379_, 1, v_fileMap_2363_);
lean_ctor_set(v___x_2379_, 2, v_options_2364_);
lean_ctor_set(v___x_2379_, 3, v_currRecDepth_2365_);
lean_ctor_set(v___x_2379_, 4, v_maxRecDepth_2366_);
lean_ctor_set(v___x_2379_, 5, v_ref_2378_);
lean_ctor_set(v___x_2379_, 6, v_currNamespace_2368_);
lean_ctor_set(v___x_2379_, 7, v_openDecls_2369_);
lean_ctor_set(v___x_2379_, 8, v_initHeartbeats_2370_);
lean_ctor_set(v___x_2379_, 9, v_maxHeartbeats_2371_);
lean_ctor_set(v___x_2379_, 10, v_quotContext_2372_);
lean_ctor_set(v___x_2379_, 11, v_currMacroScope_2373_);
lean_ctor_set(v___x_2379_, 12, v_cancelTk_x3f_2375_);
lean_ctor_set(v___x_2379_, 13, v_inheritedTraceOptions_2377_);
lean_ctor_set_uint8(v___x_2379_, sizeof(void*)*14, v_diag_2374_);
lean_ctor_set_uint8(v___x_2379_, sizeof(void*)*14 + 1, v_suppressElabErrors_2376_);
v___x_2380_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_2352_, v___y_2357_, v___y_2358_, v___x_2379_, v___y_2360_);
lean_dec_ref(v___x_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg___boxed(lean_object* v_ref_2381_, lean_object* v_msg_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_ref_2381_, v_msg_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v_ref_2381_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(lean_object* v_env_2393_, lean_object* v_options_2394_, lean_object* v_currNamespace_2395_, lean_object* v_openDecls_2396_, lean_object* v_n_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2400_ = l_Lean_ResolveName_resolveGlobalName(v_env_2393_, v_options_2394_, v_currNamespace_2395_, v_openDecls_2396_, v_n_2397_);
v___x_2401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2400_);
lean_ctor_set(v___x_2401_, 1, v___y_2399_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed(lean_object* v_env_2402_, lean_object* v_options_2403_, lean_object* v_currNamespace_2404_, lean_object* v_openDecls_2405_, lean_object* v_n_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(v_env_2402_, v_options_2403_, v_currNamespace_2404_, v_openDecls_2405_, v_n_2406_, v___y_2407_, v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec_ref(v_options_2403_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(lean_object* v_currNamespace_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v_currNamespace_2410_);
lean_ctor_set(v___x_2413_, 1, v___y_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed(lean_object* v_currNamespace_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(v_currNamespace_2414_, v___y_2415_, v___y_2416_);
lean_dec_ref(v___y_2415_);
return v_res_2417_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = l_Lean_maxRecDepthErrorMessage;
v___x_2424_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
return v___x_2424_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3);
v___x_2426_ = l_Lean_MessageData_ofFormat(v___x_2425_);
return v___x_2426_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2427_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4);
v___x_2428_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2));
v___x_2429_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
lean_ctor_set(v___x_2429_, 1, v___x_2427_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(lean_object* v_ref_2430_){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2432_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5);
v___x_2433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2433_, 0, v_ref_2430_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_ref_2435_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(lean_object* v_env_2438_, lean_object* v_currNamespace_2439_, lean_object* v_openDecls_2440_, lean_object* v_n_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = l_Lean_ResolveName_resolveNamespace(v_env_2438_, v_currNamespace_2439_, v_openDecls_2440_, v_n_2441_);
v___x_2445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
lean_ctor_set(v___x_2445_, 1, v___y_2443_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed(lean_object* v_env_2446_, lean_object* v_currNamespace_2447_, lean_object* v_openDecls_2448_, lean_object* v_n_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(v_env_2446_, v_currNamespace_2447_, v_openDecls_2448_, v_n_2449_, v___y_2450_, v___y_2451_);
lean_dec_ref(v___y_2450_);
return v_res_2452_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(lean_object* v_keys_2453_, lean_object* v_i_2454_, lean_object* v_k_2455_){
_start:
{
lean_object* v___x_2456_; uint8_t v___x_2457_; 
v___x_2456_ = lean_array_get_size(v_keys_2453_);
v___x_2457_ = lean_nat_dec_lt(v_i_2454_, v___x_2456_);
if (v___x_2457_ == 0)
{
lean_dec(v_i_2454_);
return v___x_2457_;
}
else
{
lean_object* v_k_x27_2458_; uint8_t v___x_2459_; 
v_k_x27_2458_ = lean_array_fget_borrowed(v_keys_2453_, v_i_2454_);
v___x_2459_ = l_Lean_instBEqExtraModUse_beq(v_k_2455_, v_k_x27_2458_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = lean_unsigned_to_nat(1u);
v___x_2461_ = lean_nat_add(v_i_2454_, v___x_2460_);
lean_dec(v_i_2454_);
v_i_2454_ = v___x_2461_;
goto _start;
}
else
{
lean_dec(v_i_2454_);
return v___x_2459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg___boxed(lean_object* v_keys_2463_, lean_object* v_i_2464_, lean_object* v_k_2465_){
_start:
{
uint8_t v_res_2466_; lean_object* v_r_2467_; 
v_res_2466_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_keys_2463_, v_i_2464_, v_k_2465_);
lean_dec_ref(v_k_2465_);
lean_dec_ref(v_keys_2463_);
v_r_2467_ = lean_box(v_res_2466_);
return v_r_2467_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(lean_object* v_x_2468_, size_t v_x_2469_, lean_object* v_x_2470_){
_start:
{
if (lean_obj_tag(v_x_2468_) == 0)
{
lean_object* v_es_2471_; lean_object* v___x_2472_; size_t v___x_2473_; size_t v___x_2474_; size_t v___x_2475_; lean_object* v_j_2476_; lean_object* v___x_2477_; 
v_es_2471_ = lean_ctor_get(v_x_2468_, 0);
v___x_2472_ = lean_box(2);
v___x_2473_ = ((size_t)5ULL);
v___x_2474_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1);
v___x_2475_ = lean_usize_land(v_x_2469_, v___x_2474_);
v_j_2476_ = lean_usize_to_nat(v___x_2475_);
v___x_2477_ = lean_array_get_borrowed(v___x_2472_, v_es_2471_, v_j_2476_);
lean_dec(v_j_2476_);
switch(lean_obj_tag(v___x_2477_))
{
case 0:
{
lean_object* v_key_2478_; uint8_t v___x_2479_; 
v_key_2478_ = lean_ctor_get(v___x_2477_, 0);
v___x_2479_ = l_Lean_instBEqExtraModUse_beq(v_x_2470_, v_key_2478_);
return v___x_2479_;
}
case 1:
{
lean_object* v_node_2480_; size_t v___x_2481_; 
v_node_2480_ = lean_ctor_get(v___x_2477_, 0);
v___x_2481_ = lean_usize_shift_right(v_x_2469_, v___x_2473_);
v_x_2468_ = v_node_2480_;
v_x_2469_ = v___x_2481_;
goto _start;
}
default: 
{
uint8_t v___x_2483_; 
v___x_2483_ = 0;
return v___x_2483_;
}
}
}
else
{
lean_object* v_ks_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v_ks_2484_ = lean_ctor_get(v_x_2468_, 0);
v___x_2485_ = lean_unsigned_to_nat(0u);
v___x_2486_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_ks_2484_, v___x_2485_, v_x_2470_);
return v___x_2486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_x_2487_, lean_object* v_x_2488_, lean_object* v_x_2489_){
_start:
{
size_t v_x_21359__boxed_2490_; uint8_t v_res_2491_; lean_object* v_r_2492_; 
v_x_21359__boxed_2490_ = lean_unbox_usize(v_x_2488_);
lean_dec(v_x_2488_);
v_res_2491_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_2487_, v_x_21359__boxed_2490_, v_x_2489_);
lean_dec_ref(v_x_2489_);
lean_dec_ref(v_x_2487_);
v_r_2492_ = lean_box(v_res_2491_);
return v_r_2492_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(lean_object* v_x_2493_, lean_object* v_x_2494_){
_start:
{
uint64_t v___x_2495_; size_t v___x_2496_; uint8_t v___x_2497_; 
v___x_2495_ = l_Lean_instHashableExtraModUse_hash(v_x_2494_);
v___x_2496_ = lean_uint64_to_usize(v___x_2495_);
v___x_2497_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_2493_, v___x_2496_, v_x_2494_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_x_2498_, lean_object* v_x_2499_){
_start:
{
uint8_t v_res_2500_; lean_object* v_r_2501_; 
v_res_2500_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v_x_2498_, v_x_2499_);
lean_dec_ref(v_x_2499_);
lean_dec_ref(v_x_2498_);
v_r_2501_ = lean_box(v_res_2500_);
return v_r_2501_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2504_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1));
v___x_2505_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0));
v___x_2506_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2505_, v___x_2504_);
return v___x_2506_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2507_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3);
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
return v___x_2509_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4);
v___x_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
return v___x_2511_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6(void){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4);
v___x_2513_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
lean_ctor_set(v___x_2513_, 2, v___x_2512_);
lean_ctor_set(v___x_2513_, 3, v___x_2512_);
lean_ctor_set(v___x_2513_, 4, v___x_2512_);
lean_ctor_set(v___x_2513_, 5, v___x_2512_);
return v___x_2513_;
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
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12(void){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11));
v___x_2522_ = l_Lean_stringToMessageData(v___x_2521_);
return v___x_2522_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1));
v___x_2524_ = l_Lean_stringToMessageData(v___x_2523_);
return v___x_2524_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14(void){
_start:
{
lean_object* v_cls_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v_cls_2525_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8));
v___x_2526_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1));
v___x_2527_ = l_Lean_Name_append(v___x_2526_, v_cls_2525_);
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
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18(void){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17));
v___x_2533_ = l_Lean_stringToMessageData(v___x_2532_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(lean_object* v_mod_2538_, uint8_t v_isMeta_2539_, lean_object* v_hint_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v___x_2550_; lean_object* v_env_2551_; uint8_t v_isExporting_2552_; lean_object* v___x_2553_; lean_object* v_env_2554_; lean_object* v___x_2555_; lean_object* v_entry_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___x_2602_; uint8_t v___x_2603_; 
v___x_2550_ = lean_st_ref_get(v___y_2548_);
v_env_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc_ref(v_env_2551_);
lean_dec(v___x_2550_);
v_isExporting_2552_ = lean_ctor_get_uint8(v_env_2551_, sizeof(void*)*8);
lean_dec_ref(v_env_2551_);
v___x_2553_ = lean_st_ref_get(v___y_2548_);
v_env_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc_ref(v_env_2554_);
lean_dec(v___x_2553_);
v___x_2555_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2);
lean_inc(v_mod_2538_);
v_entry_2556_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2556_, 0, v_mod_2538_);
lean_ctor_set_uint8(v_entry_2556_, sizeof(void*)*1, v_isExporting_2552_);
lean_ctor_set_uint8(v_entry_2556_, sizeof(void*)*1 + 1, v_isMeta_2539_);
v___x_2557_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2558_ = lean_box(1);
v___x_2559_ = lean_box(0);
v___x_2602_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2555_, v___x_2557_, v_env_2554_, v___x_2558_, v___x_2559_);
v___x_2603_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v___x_2602_, v_entry_2556_);
lean_dec(v___x_2602_);
if (v___x_2603_ == 0)
{
lean_object* v_options_2604_; uint8_t v_hasTrace_2605_; 
v_options_2604_ = lean_ctor_get(v___y_2547_, 2);
v_hasTrace_2605_ = lean_ctor_get_uint8(v_options_2604_, sizeof(void*)*1);
if (v_hasTrace_2605_ == 0)
{
lean_dec(v_hint_2540_);
lean_dec(v_mod_2538_);
v___y_2561_ = v___y_2546_;
v___y_2562_ = v___y_2548_;
goto v___jp_2560_;
}
else
{
lean_object* v_inheritedTraceOptions_2606_; lean_object* v_cls_2607_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___x_2627_; uint8_t v___x_2628_; 
v_inheritedTraceOptions_2606_ = lean_ctor_get(v___y_2547_, 13);
v_cls_2607_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8));
v___x_2627_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14);
v___x_2628_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2606_, v_options_2604_, v___x_2627_);
if (v___x_2628_ == 0)
{
lean_dec(v_hint_2540_);
lean_dec(v_mod_2538_);
v___y_2561_ = v___y_2546_;
v___y_2562_ = v___y_2548_;
goto v___jp_2560_;
}
else
{
lean_object* v___x_2629_; lean_object* v___y_2631_; 
v___x_2629_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16);
if (v_isExporting_2552_ == 0)
{
lean_object* v___x_2638_; 
v___x_2638_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__21));
v___y_2631_ = v___x_2638_;
goto v___jp_2630_;
}
else
{
lean_object* v___x_2639_; 
v___x_2639_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__22));
v___y_2631_ = v___x_2639_;
goto v___jp_2630_;
}
v___jp_2630_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_inc_ref(v___y_2631_);
v___x_2632_ = l_Lean_stringToMessageData(v___y_2631_);
v___x_2633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2629_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
v___x_2634_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18);
v___x_2635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2633_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
if (v_isMeta_2539_ == 0)
{
lean_object* v___x_2636_; 
v___x_2636_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19));
v___y_2614_ = v___x_2635_;
v___y_2615_ = v___x_2636_;
goto v___jp_2613_;
}
else
{
lean_object* v___x_2637_; 
v___x_2637_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20));
v___y_2614_ = v___x_2635_;
v___y_2615_ = v___x_2637_;
goto v___jp_2613_;
}
}
}
v___jp_2608_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___y_2609_);
lean_ctor_set(v___x_2611_, 1, v___y_2610_);
v___x_2612_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_2607_, v___x_2611_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_dec_ref(v___x_2612_);
v___y_2561_ = v___y_2546_;
v___y_2562_ = v___y_2548_;
goto v___jp_2560_;
}
else
{
lean_dec_ref(v_entry_2556_);
return v___x_2612_;
}
}
v___jp_2613_:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
lean_inc_ref(v___y_2615_);
v___x_2616_ = l_Lean_stringToMessageData(v___y_2615_);
v___x_2617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___y_2614_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
v___x_2618_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10);
v___x_2619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2617_);
lean_ctor_set(v___x_2619_, 1, v___x_2618_);
v___x_2620_ = l_Lean_MessageData_ofName(v_mod_2538_);
v___x_2621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2619_);
lean_ctor_set(v___x_2621_, 1, v___x_2620_);
v___x_2622_ = l_Lean_Name_isAnonymous(v_hint_2540_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2623_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12);
v___x_2624_ = l_Lean_MessageData_ofName(v_hint_2540_);
v___x_2625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2623_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
v___y_2609_ = v___x_2621_;
v___y_2610_ = v___x_2625_;
goto v___jp_2608_;
}
else
{
lean_object* v___x_2626_; 
lean_dec(v_hint_2540_);
v___x_2626_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13);
v___y_2609_ = v___x_2621_;
v___y_2610_ = v___x_2626_;
goto v___jp_2608_;
}
}
}
}
else
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
lean_dec_ref(v_entry_2556_);
lean_dec(v_hint_2540_);
lean_dec(v_mod_2538_);
v___x_2640_ = lean_box(0);
v___x_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2640_);
return v___x_2641_;
}
v___jp_2560_:
{
lean_object* v___x_2563_; lean_object* v_toEnvExtension_2564_; lean_object* v_env_2565_; lean_object* v_nextMacroScope_2566_; lean_object* v_ngen_2567_; lean_object* v_auxDeclNGen_2568_; lean_object* v_traceState_2569_; lean_object* v_messages_2570_; lean_object* v_infoState_2571_; lean_object* v_snapshotTasks_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2600_; 
v___x_2563_ = lean_st_ref_take(v___y_2562_);
v_toEnvExtension_2564_ = lean_ctor_get(v___x_2557_, 0);
v_env_2565_ = lean_ctor_get(v___x_2563_, 0);
v_nextMacroScope_2566_ = lean_ctor_get(v___x_2563_, 1);
v_ngen_2567_ = lean_ctor_get(v___x_2563_, 2);
v_auxDeclNGen_2568_ = lean_ctor_get(v___x_2563_, 3);
v_traceState_2569_ = lean_ctor_get(v___x_2563_, 4);
v_messages_2570_ = lean_ctor_get(v___x_2563_, 6);
v_infoState_2571_ = lean_ctor_get(v___x_2563_, 7);
v_snapshotTasks_2572_ = lean_ctor_get(v___x_2563_, 8);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2600_ == 0)
{
lean_object* v_unused_2601_; 
v_unused_2601_ = lean_ctor_get(v___x_2563_, 5);
lean_dec(v_unused_2601_);
v___x_2574_ = v___x_2563_;
v_isShared_2575_ = v_isSharedCheck_2600_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_snapshotTasks_2572_);
lean_inc(v_infoState_2571_);
lean_inc(v_messages_2570_);
lean_inc(v_traceState_2569_);
lean_inc(v_auxDeclNGen_2568_);
lean_inc(v_ngen_2567_);
lean_inc(v_nextMacroScope_2566_);
lean_inc(v_env_2565_);
lean_dec(v___x_2563_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2600_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v_asyncMode_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2580_; 
v_asyncMode_2576_ = lean_ctor_get(v_toEnvExtension_2564_, 2);
v___x_2577_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2557_, v_env_2565_, v_entry_2556_, v_asyncMode_2576_, v___x_2559_);
v___x_2578_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 5, v___x_2578_);
lean_ctor_set(v___x_2574_, 0, v___x_2577_);
v___x_2580_ = v___x_2574_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2577_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v_nextMacroScope_2566_);
lean_ctor_set(v_reuseFailAlloc_2599_, 2, v_ngen_2567_);
lean_ctor_set(v_reuseFailAlloc_2599_, 3, v_auxDeclNGen_2568_);
lean_ctor_set(v_reuseFailAlloc_2599_, 4, v_traceState_2569_);
lean_ctor_set(v_reuseFailAlloc_2599_, 5, v___x_2578_);
lean_ctor_set(v_reuseFailAlloc_2599_, 6, v_messages_2570_);
lean_ctor_set(v_reuseFailAlloc_2599_, 7, v_infoState_2571_);
lean_ctor_set(v_reuseFailAlloc_2599_, 8, v_snapshotTasks_2572_);
v___x_2580_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v_mctx_2583_; lean_object* v_zetaDeltaFVarIds_2584_; lean_object* v_postponed_2585_; lean_object* v_diag_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2597_; 
v___x_2581_ = lean_st_ref_set(v___y_2562_, v___x_2580_);
v___x_2582_ = lean_st_ref_take(v___y_2561_);
v_mctx_2583_ = lean_ctor_get(v___x_2582_, 0);
v_zetaDeltaFVarIds_2584_ = lean_ctor_get(v___x_2582_, 2);
v_postponed_2585_ = lean_ctor_get(v___x_2582_, 3);
v_diag_2586_ = lean_ctor_get(v___x_2582_, 4);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2597_ == 0)
{
lean_object* v_unused_2598_; 
v_unused_2598_ = lean_ctor_get(v___x_2582_, 1);
lean_dec(v_unused_2598_);
v___x_2588_ = v___x_2582_;
v_isShared_2589_ = v_isSharedCheck_2597_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_diag_2586_);
lean_inc(v_postponed_2585_);
lean_inc(v_zetaDeltaFVarIds_2584_);
lean_inc(v_mctx_2583_);
lean_dec(v___x_2582_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2597_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2590_; lean_object* v___x_2592_; 
v___x_2590_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6);
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 1, v___x_2590_);
v___x_2592_ = v___x_2588_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_mctx_2583_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v___x_2590_);
lean_ctor_set(v_reuseFailAlloc_2596_, 2, v_zetaDeltaFVarIds_2584_);
lean_ctor_set(v_reuseFailAlloc_2596_, 3, v_postponed_2585_);
lean_ctor_set(v_reuseFailAlloc_2596_, 4, v_diag_2586_);
v___x_2592_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = lean_st_ref_set(v___y_2561_, v___x_2592_);
v___x_2594_ = lean_box(0);
v___x_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
return v___x_2595_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___boxed(lean_object* v_mod_2642_, lean_object* v_isMeta_2643_, lean_object* v_hint_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
uint8_t v_isMeta_boxed_2654_; lean_object* v_res_2655_; 
v_isMeta_boxed_2654_ = lean_unbox(v_isMeta_2643_);
v_res_2655_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_mod_2642_, v_isMeta_boxed_2654_, v_hint_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(lean_object* v_a_2656_, lean_object* v_x_2657_){
_start:
{
if (lean_obj_tag(v_x_2657_) == 0)
{
lean_object* v___x_2658_; 
v___x_2658_ = lean_box(0);
return v___x_2658_;
}
else
{
lean_object* v_key_2659_; lean_object* v_value_2660_; lean_object* v_tail_2661_; uint8_t v___x_2662_; 
v_key_2659_ = lean_ctor_get(v_x_2657_, 0);
v_value_2660_ = lean_ctor_get(v_x_2657_, 1);
v_tail_2661_ = lean_ctor_get(v_x_2657_, 2);
v___x_2662_ = lean_name_eq(v_key_2659_, v_a_2656_);
if (v___x_2662_ == 0)
{
v_x_2657_ = v_tail_2661_;
goto _start;
}
else
{
lean_object* v___x_2664_; 
lean_inc(v_value_2660_);
v___x_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2664_, 0, v_value_2660_);
return v___x_2664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_a_2665_, lean_object* v_x_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(v_a_2665_, v_x_2666_);
lean_dec(v_x_2666_);
lean_dec(v_a_2665_);
return v_res_2667_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_2668_; uint64_t v___x_2669_; 
v___x_2668_ = lean_unsigned_to_nat(1723u);
v___x_2669_ = lean_uint64_of_nat(v___x_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(lean_object* v_m_2670_, lean_object* v_a_2671_){
_start:
{
lean_object* v_buckets_2672_; lean_object* v___x_2673_; uint64_t v___y_2675_; 
v_buckets_2672_ = lean_ctor_get(v_m_2670_, 1);
v___x_2673_ = lean_array_get_size(v_buckets_2672_);
if (lean_obj_tag(v_a_2671_) == 0)
{
uint64_t v___x_2689_; 
v___x_2689_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___closed__0);
v___y_2675_ = v___x_2689_;
goto v___jp_2674_;
}
else
{
uint64_t v_hash_2690_; 
v_hash_2690_ = lean_ctor_get_uint64(v_a_2671_, sizeof(void*)*2);
v___y_2675_ = v_hash_2690_;
goto v___jp_2674_;
}
v___jp_2674_:
{
uint64_t v___x_2676_; uint64_t v___x_2677_; uint64_t v_fold_2678_; uint64_t v___x_2679_; uint64_t v___x_2680_; uint64_t v___x_2681_; size_t v___x_2682_; size_t v___x_2683_; size_t v___x_2684_; size_t v___x_2685_; size_t v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2676_ = 32ULL;
v___x_2677_ = lean_uint64_shift_right(v___y_2675_, v___x_2676_);
v_fold_2678_ = lean_uint64_xor(v___y_2675_, v___x_2677_);
v___x_2679_ = 16ULL;
v___x_2680_ = lean_uint64_shift_right(v_fold_2678_, v___x_2679_);
v___x_2681_ = lean_uint64_xor(v_fold_2678_, v___x_2680_);
v___x_2682_ = lean_uint64_to_usize(v___x_2681_);
v___x_2683_ = lean_usize_of_nat(v___x_2673_);
v___x_2684_ = ((size_t)1ULL);
v___x_2685_ = lean_usize_sub(v___x_2683_, v___x_2684_);
v___x_2686_ = lean_usize_land(v___x_2682_, v___x_2685_);
v___x_2687_ = lean_array_uget_borrowed(v_buckets_2672_, v___x_2686_);
v___x_2688_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(v_a_2671_, v___x_2687_);
return v___x_2688_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_m_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v_m_2691_, v_a_2692_);
lean_dec(v_a_2692_);
lean_dec_ref(v_m_2691_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(lean_object* v___x_2694_, lean_object* v_declName_2695_, lean_object* v_as_2696_, size_t v_sz_2697_, size_t v_i_2698_, lean_object* v_b_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
uint8_t v___x_2709_; 
v___x_2709_ = lean_usize_dec_lt(v_i_2698_, v_sz_2697_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; 
lean_dec(v_declName_2695_);
v___x_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2710_, 0, v_b_2699_);
return v___x_2710_;
}
else
{
lean_object* v___x_2711_; lean_object* v_modules_2712_; lean_object* v___x_2713_; lean_object* v_a_2714_; lean_object* v___x_2715_; lean_object* v_toImport_2716_; lean_object* v_module_2717_; uint8_t v___x_2718_; lean_object* v___x_2719_; 
v___x_2711_ = l_Lean_Environment_header(v___x_2694_);
v_modules_2712_ = lean_ctor_get(v___x_2711_, 3);
lean_inc_ref(v_modules_2712_);
lean_dec_ref(v___x_2711_);
v___x_2713_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2714_ = lean_array_uget_borrowed(v_as_2696_, v_i_2698_);
v___x_2715_ = lean_array_get(v___x_2713_, v_modules_2712_, v_a_2714_);
lean_dec_ref(v_modules_2712_);
v_toImport_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc_ref(v_toImport_2716_);
lean_dec(v___x_2715_);
v_module_2717_ = lean_ctor_get(v_toImport_2716_, 0);
lean_inc(v_module_2717_);
lean_dec_ref(v_toImport_2716_);
v___x_2718_ = 0;
lean_inc(v_declName_2695_);
v___x_2719_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_module_2717_, v___x_2718_, v_declName_2695_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v___x_2720_; size_t v___x_2721_; size_t v___x_2722_; 
lean_dec_ref(v___x_2719_);
v___x_2720_ = lean_box(0);
v___x_2721_ = ((size_t)1ULL);
v___x_2722_ = lean_usize_add(v_i_2698_, v___x_2721_);
v_i_2698_ = v___x_2722_;
v_b_2699_ = v___x_2720_;
goto _start;
}
else
{
lean_dec(v_declName_2695_);
return v___x_2719_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6___boxed(lean_object* v___x_2724_, lean_object* v_declName_2725_, lean_object* v_as_2726_, lean_object* v_sz_2727_, lean_object* v_i_2728_, lean_object* v_b_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
size_t v_sz_boxed_2739_; size_t v_i_boxed_2740_; lean_object* v_res_2741_; 
v_sz_boxed_2739_ = lean_unbox_usize(v_sz_2727_);
lean_dec(v_sz_2727_);
v_i_boxed_2740_ = lean_unbox_usize(v_i_2728_);
lean_dec(v_i_2728_);
v_res_2741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(v___x_2724_, v_declName_2725_, v_as_2726_, v_sz_boxed_2739_, v_i_boxed_2740_, v_b_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec_ref(v_as_2726_);
lean_dec_ref(v___x_2724_);
return v_res_2741_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2744_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1));
v___x_2745_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0));
v___x_2746_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2745_, v___x_2744_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(lean_object* v_declName_2749_, uint8_t v_isMeta_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v___x_2760_; lean_object* v_env_2764_; lean_object* v___y_2766_; lean_object* v___x_2779_; 
v___x_2760_ = lean_st_ref_get(v___y_2758_);
v_env_2764_ = lean_ctor_get(v___x_2760_, 0);
lean_inc_ref(v_env_2764_);
lean_dec(v___x_2760_);
v___x_2779_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2764_, v_declName_2749_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_dec_ref(v_env_2764_);
lean_dec(v_declName_2749_);
goto v___jp_2761_;
}
else
{
lean_object* v_val_2780_; lean_object* v___x_2781_; lean_object* v_modules_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v_val_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_val_2780_);
lean_dec_ref(v___x_2779_);
v___x_2781_ = l_Lean_Environment_header(v_env_2764_);
v_modules_2782_ = lean_ctor_get(v___x_2781_, 3);
lean_inc_ref(v_modules_2782_);
lean_dec_ref(v___x_2781_);
v___x_2783_ = lean_array_get_size(v_modules_2782_);
v___x_2784_ = lean_nat_dec_lt(v_val_2780_, v___x_2783_);
if (v___x_2784_ == 0)
{
lean_dec_ref(v_modules_2782_);
lean_dec(v_val_2780_);
lean_dec_ref(v_env_2764_);
lean_dec(v_declName_2749_);
goto v___jp_2761_;
}
else
{
lean_object* v___x_2785_; lean_object* v_env_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; uint8_t v___y_2790_; 
v___x_2785_ = lean_st_ref_get(v___y_2758_);
v_env_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc_ref(v_env_2786_);
lean_dec(v___x_2785_);
v___x_2787_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2);
v___x_2788_ = lean_array_fget(v_modules_2782_, v_val_2780_);
lean_dec(v_val_2780_);
lean_dec_ref(v_modules_2782_);
if (v_isMeta_2750_ == 0)
{
lean_dec_ref(v_env_2786_);
v___y_2790_ = v_isMeta_2750_;
goto v___jp_2789_;
}
else
{
uint8_t v___x_2801_; 
lean_inc(v_declName_2749_);
v___x_2801_ = l_Lean_isMarkedMeta(v_env_2786_, v_declName_2749_);
if (v___x_2801_ == 0)
{
v___y_2790_ = v_isMeta_2750_;
goto v___jp_2789_;
}
else
{
uint8_t v___x_2802_; 
v___x_2802_ = 0;
v___y_2790_ = v___x_2802_;
goto v___jp_2789_;
}
}
v___jp_2789_:
{
lean_object* v_toImport_2791_; lean_object* v_module_2792_; lean_object* v___x_2793_; 
v_toImport_2791_ = lean_ctor_get(v___x_2788_, 0);
lean_inc_ref(v_toImport_2791_);
lean_dec(v___x_2788_);
v_module_2792_ = lean_ctor_get(v_toImport_2791_, 0);
lean_inc(v_module_2792_);
lean_dec_ref(v_toImport_2791_);
lean_inc(v_declName_2749_);
v___x_2793_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_module_2792_, v___y_2790_, v_declName_2749_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
lean_dec_ref(v___x_2793_);
v___x_2794_ = l_Lean_indirectModUseExt;
v___x_2795_ = lean_box(1);
v___x_2796_ = lean_box(0);
lean_inc_ref(v_env_2764_);
v___x_2797_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2787_, v___x_2794_, v_env_2764_, v___x_2795_, v___x_2796_);
v___x_2798_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v___x_2797_, v_declName_2749_);
lean_dec(v___x_2797_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v___x_2799_; 
v___x_2799_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__3));
v___y_2766_ = v___x_2799_;
goto v___jp_2765_;
}
else
{
lean_object* v_val_2800_; 
v_val_2800_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_val_2800_);
lean_dec_ref(v___x_2798_);
v___y_2766_ = v_val_2800_;
goto v___jp_2765_;
}
}
else
{
lean_dec_ref(v_env_2764_);
lean_dec(v_declName_2749_);
return v___x_2793_;
}
}
}
}
v___jp_2761_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = lean_box(0);
v___x_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2762_);
return v___x_2763_;
}
v___jp_2765_:
{
lean_object* v___x_2767_; size_t v_sz_2768_; size_t v___x_2769_; lean_object* v___x_2770_; 
v___x_2767_ = lean_box(0);
v_sz_2768_ = lean_array_size(v___y_2766_);
v___x_2769_ = ((size_t)0ULL);
v___x_2770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(v_env_2764_, v_declName_2749_, v___y_2766_, v_sz_2768_, v___x_2769_, v___x_2767_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
lean_dec_ref(v___y_2766_);
lean_dec_ref(v_env_2764_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2777_ == 0)
{
lean_object* v_unused_2778_; 
v_unused_2778_ = lean_ctor_get(v___x_2770_, 0);
lean_dec(v_unused_2778_);
v___x_2772_ = v___x_2770_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_dec(v___x_2770_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v___x_2767_);
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2767_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
else
{
return v___x_2770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___boxed(lean_object* v_declName_2803_, lean_object* v_isMeta_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
uint8_t v_isMeta_boxed_2814_; lean_object* v_res_2815_; 
v_isMeta_boxed_2814_ = lean_unbox(v_isMeta_2804_);
v_res_2815_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(v_declName_2803_, v_isMeta_boxed_2814_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(lean_object* v_as_x27_2816_, lean_object* v_b_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
if (lean_obj_tag(v_as_x27_2816_) == 0)
{
lean_object* v___x_2827_; 
v___x_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2827_, 0, v_b_2817_);
return v___x_2827_;
}
else
{
lean_object* v_head_2828_; lean_object* v_tail_2829_; uint8_t v___x_2830_; lean_object* v___x_2831_; 
v_head_2828_ = lean_ctor_get(v_as_x27_2816_, 0);
lean_inc(v_head_2828_);
v_tail_2829_ = lean_ctor_get(v_as_x27_2816_, 1);
lean_inc(v_tail_2829_);
lean_dec_ref(v_as_x27_2816_);
v___x_2830_ = 1;
v___x_2831_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(v_head_2828_, v___x_2830_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v___x_2832_; 
lean_dec_ref(v___x_2831_);
v___x_2832_ = lean_box(0);
v_as_x27_2816_ = v_tail_2829_;
v_b_2817_ = v___x_2832_;
goto _start;
}
else
{
lean_dec(v_tail_2829_);
return v___x_2831_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2834_, lean_object* v_b_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_as_x27_2834_, v_b_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1(lean_object* v_env_2846_, lean_object* v_declName_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
uint8_t v___x_2850_; lean_object* v_env_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; uint8_t v___x_2854_; 
v___x_2850_ = 0;
v_env_2851_ = l_Lean_Environment_setExporting(v_env_2846_, v___x_2850_);
lean_inc(v_declName_2847_);
v___x_2852_ = l_Lean_mkPrivateName(v_env_2851_, v_declName_2847_);
v___x_2853_ = 1;
lean_inc_ref(v_env_2851_);
v___x_2854_ = l_Lean_Environment_contains(v_env_2851_, v___x_2852_, v___x_2853_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; uint8_t v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2855_ = l_Lean_privateToUserName(v_declName_2847_);
v___x_2856_ = l_Lean_Environment_contains(v_env_2851_, v___x_2855_, v___x_2853_);
v___x_2857_ = lean_box(v___x_2856_);
v___x_2858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2857_);
lean_ctor_set(v___x_2858_, 1, v___y_2849_);
return v___x_2858_;
}
else
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
lean_dec_ref(v_env_2851_);
lean_dec(v_declName_2847_);
v___x_2859_ = lean_box(v___x_2854_);
v___x_2860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
lean_ctor_set(v___x_2860_, 1, v___y_2849_);
return v___x_2860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1___boxed(lean_object* v_env_2861_, lean_object* v_declName_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1(v_env_2861_, v_declName_2862_, v___y_2863_, v___y_2864_);
lean_dec_ref(v___y_2863_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(lean_object* v_x_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v___x_2877_; lean_object* v_env_2878_; lean_object* v_options_2879_; lean_object* v_currRecDepth_2880_; lean_object* v_maxRecDepth_2881_; lean_object* v_ref_2882_; lean_object* v_currNamespace_2883_; lean_object* v_openDecls_2884_; lean_object* v_quotContext_2885_; lean_object* v_currMacroScope_2886_; lean_object* v___x_2887_; lean_object* v_nextMacroScope_2888_; lean_object* v___f_2889_; lean_object* v___f_2890_; lean_object* v___f_2891_; lean_object* v___f_2892_; lean_object* v___f_2893_; lean_object* v_methods_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2877_ = lean_st_ref_get(v___y_2875_);
v_env_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc_ref_n(v_env_2878_, 4);
lean_dec(v___x_2877_);
v_options_2879_ = lean_ctor_get(v___y_2874_, 2);
v_currRecDepth_2880_ = lean_ctor_get(v___y_2874_, 3);
v_maxRecDepth_2881_ = lean_ctor_get(v___y_2874_, 4);
v_ref_2882_ = lean_ctor_get(v___y_2874_, 5);
v_currNamespace_2883_ = lean_ctor_get(v___y_2874_, 6);
v_openDecls_2884_ = lean_ctor_get(v___y_2874_, 7);
v_quotContext_2885_ = lean_ctor_get(v___y_2874_, 10);
v_currMacroScope_2886_ = lean_ctor_get(v___y_2874_, 11);
v___x_2887_ = lean_st_ref_get(v___y_2875_);
v_nextMacroScope_2888_ = lean_ctor_get(v___x_2887_, 1);
lean_inc(v_nextMacroScope_2888_);
lean_dec(v___x_2887_);
v___f_2889_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2889_, 0, v_env_2878_);
v___f_2890_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2890_, 0, v_env_2878_);
lean_inc_n(v_openDecls_2884_, 2);
lean_inc_n(v_currNamespace_2883_, 3);
v___f_2891_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_2891_, 0, v_env_2878_);
lean_closure_set(v___f_2891_, 1, v_currNamespace_2883_);
lean_closure_set(v___f_2891_, 2, v_openDecls_2884_);
v___f_2892_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2892_, 0, v_currNamespace_2883_);
lean_inc_ref(v_options_2879_);
v___f_2893_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2893_, 0, v_env_2878_);
lean_closure_set(v___f_2893_, 1, v_options_2879_);
lean_closure_set(v___f_2893_, 2, v_currNamespace_2883_);
lean_closure_set(v___f_2893_, 3, v_openDecls_2884_);
v_methods_2894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2894_, 0, v___f_2889_);
lean_ctor_set(v_methods_2894_, 1, v___f_2892_);
lean_ctor_set(v_methods_2894_, 2, v___f_2890_);
lean_ctor_set(v_methods_2894_, 3, v___f_2891_);
lean_ctor_set(v_methods_2894_, 4, v___f_2893_);
lean_inc(v_ref_2882_);
lean_inc(v_maxRecDepth_2881_);
lean_inc(v_currRecDepth_2880_);
lean_inc(v_currMacroScope_2886_);
lean_inc(v_quotContext_2885_);
v___x_2895_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2895_, 0, v_methods_2894_);
lean_ctor_set(v___x_2895_, 1, v_quotContext_2885_);
lean_ctor_set(v___x_2895_, 2, v_currMacroScope_2886_);
lean_ctor_set(v___x_2895_, 3, v_currRecDepth_2880_);
lean_ctor_set(v___x_2895_, 4, v_maxRecDepth_2881_);
lean_ctor_set(v___x_2895_, 5, v_ref_2882_);
v___x_2896_ = lean_box(0);
v___x_2897_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2897_, 0, v_nextMacroScope_2888_);
lean_ctor_set(v___x_2897_, 1, v___x_2896_);
lean_ctor_set(v___x_2897_, 2, v___x_2896_);
v___x_2898_ = lean_apply_2(v_x_2867_, v___x_2895_, v___x_2897_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v_a_2900_; lean_object* v_macroScope_2901_; lean_object* v_traceMsgs_2902_; lean_object* v_expandedMacroDecls_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 1);
lean_inc(v_a_2899_);
v_a_2900_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2900_);
lean_dec_ref(v___x_2898_);
v_macroScope_2901_ = lean_ctor_get(v_a_2899_, 0);
lean_inc(v_macroScope_2901_);
v_traceMsgs_2902_ = lean_ctor_get(v_a_2899_, 1);
lean_inc(v_traceMsgs_2902_);
v_expandedMacroDecls_2903_ = lean_ctor_get(v_a_2899_, 2);
lean_inc(v_expandedMacroDecls_2903_);
lean_dec(v_a_2899_);
v___x_2904_ = lean_box(0);
v___x_2905_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_expandedMacroDecls_2903_, v___x_2904_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v___x_2906_; lean_object* v_env_2907_; lean_object* v_ngen_2908_; lean_object* v_auxDeclNGen_2909_; lean_object* v_traceState_2910_; lean_object* v_cache_2911_; lean_object* v_messages_2912_; lean_object* v_infoState_2913_; lean_object* v_snapshotTasks_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2940_; 
lean_dec_ref(v___x_2905_);
v___x_2906_ = lean_st_ref_take(v___y_2875_);
v_env_2907_ = lean_ctor_get(v___x_2906_, 0);
v_ngen_2908_ = lean_ctor_get(v___x_2906_, 2);
v_auxDeclNGen_2909_ = lean_ctor_get(v___x_2906_, 3);
v_traceState_2910_ = lean_ctor_get(v___x_2906_, 4);
v_cache_2911_ = lean_ctor_get(v___x_2906_, 5);
v_messages_2912_ = lean_ctor_get(v___x_2906_, 6);
v_infoState_2913_ = lean_ctor_get(v___x_2906_, 7);
v_snapshotTasks_2914_ = lean_ctor_get(v___x_2906_, 8);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2940_ == 0)
{
lean_object* v_unused_2941_; 
v_unused_2941_ = lean_ctor_get(v___x_2906_, 1);
lean_dec(v_unused_2941_);
v___x_2916_ = v___x_2906_;
v_isShared_2917_ = v_isSharedCheck_2940_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_snapshotTasks_2914_);
lean_inc(v_infoState_2913_);
lean_inc(v_messages_2912_);
lean_inc(v_cache_2911_);
lean_inc(v_traceState_2910_);
lean_inc(v_auxDeclNGen_2909_);
lean_inc(v_ngen_2908_);
lean_inc(v_env_2907_);
lean_dec(v___x_2906_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2940_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 1, v_macroScope_2901_);
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_env_2907_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v_macroScope_2901_);
lean_ctor_set(v_reuseFailAlloc_2939_, 2, v_ngen_2908_);
lean_ctor_set(v_reuseFailAlloc_2939_, 3, v_auxDeclNGen_2909_);
lean_ctor_set(v_reuseFailAlloc_2939_, 4, v_traceState_2910_);
lean_ctor_set(v_reuseFailAlloc_2939_, 5, v_cache_2911_);
lean_ctor_set(v_reuseFailAlloc_2939_, 6, v_messages_2912_);
lean_ctor_set(v_reuseFailAlloc_2939_, 7, v_infoState_2913_);
lean_ctor_set(v_reuseFailAlloc_2939_, 8, v_snapshotTasks_2914_);
v___x_2919_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2920_ = lean_st_ref_set(v___y_2875_, v___x_2919_);
v___x_2921_ = l_List_reverse___redArg(v_traceMsgs_2902_);
v___x_2922_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(v___x_2921_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2929_ == 0)
{
lean_object* v_unused_2930_; 
v_unused_2930_ = lean_ctor_get(v___x_2922_, 0);
lean_dec(v_unused_2930_);
v___x_2924_ = v___x_2922_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_dec(v___x_2922_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 0, v_a_2900_);
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2900_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_dec(v_a_2900_);
v_a_2931_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2922_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2922_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
}
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_dec(v_traceMsgs_2902_);
lean_dec(v_macroScope_2901_);
lean_dec(v_a_2900_);
v_a_2942_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2905_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2905_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
else
{
lean_object* v_a_2950_; 
v_a_2950_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2950_);
lean_dec_ref(v___x_2898_);
if (lean_obj_tag(v_a_2950_) == 0)
{
lean_object* v_a_2951_; lean_object* v_a_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; 
v_a_2951_ = lean_ctor_get(v_a_2950_, 0);
lean_inc(v_a_2951_);
v_a_2952_ = lean_ctor_get(v_a_2950_, 1);
lean_inc_ref(v_a_2952_);
lean_dec_ref(v_a_2950_);
v___x_2953_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___closed__0));
v___x_2954_ = lean_string_dec_eq(v_a_2952_, v___x_2953_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2955_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2955_, 0, v_a_2952_);
v___x_2956_ = l_Lean_MessageData_ofFormat(v___x_2955_);
v___x_2957_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_a_2951_, v___x_2956_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
lean_dec(v_a_2951_);
return v___x_2957_;
}
else
{
lean_object* v___x_2958_; 
lean_dec_ref(v_a_2952_);
v___x_2958_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_a_2951_);
return v___x_2958_;
}
}
else
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_2959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___boxed(lean_object* v_x_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v_x_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases(lean_object* v_x_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_){
_start:
{
lean_object* v___x_2991_; uint8_t v___x_2992_; 
v___x_2991_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2));
lean_inc(v_x_2981_);
v___x_2992_ = l_Lean_Syntax_isOfKind(v_x_2981_, v___x_2991_);
if (v___x_2992_ == 0)
{
lean_object* v___x_2993_; 
lean_dec(v_x_2981_);
v___x_2993_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_2993_;
}
else
{
lean_object* v___x_2994_; lean_object* v_hyp_2995_; lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2994_ = lean_unsigned_to_nat(1u);
v_hyp_2995_ = l_Lean_Syntax_getArg(v_x_2981_, v___x_2994_);
v___x_2996_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4));
lean_inc(v_hyp_2995_);
v___x_2997_ = l_Lean_Syntax_isOfKind(v_hyp_2995_, v___x_2996_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; 
lean_dec(v_hyp_2995_);
lean_dec(v_x_2981_);
v___x_2998_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_2998_;
}
else
{
lean_object* v___x_2999_; lean_object* v_pat_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_2999_ = lean_unsigned_to_nat(3u);
v_pat_3000_ = l_Lean_Syntax_getArg(v_x_2981_, v___x_2999_);
lean_dec(v_x_2981_);
v___x_3001_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_MCasesPat_parse___boxed), 3, 1);
lean_closure_set(v___x_3001_, 0, v_pat_3000_);
v___x_3002_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v___x_3001_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3004_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_a_3003_);
lean_dec_ref(v___x_3002_);
v___x_3004_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_2983_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v_fst_3006_; lean_object* v_snd_3007_; lean_object* v___f_3008_; lean_object* v___x_3009_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref(v___x_3004_);
v_fst_3006_ = lean_ctor_get(v_a_3005_, 0);
lean_inc_n(v_fst_3006_, 2);
v_snd_3007_ = lean_ctor_get(v_a_3005_, 1);
lean_inc(v_snd_3007_);
lean_dec(v_a_3005_);
v___f_3008_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___boxed), 13, 4);
lean_closure_set(v___f_3008_, 0, v_snd_3007_);
lean_closure_set(v___f_3008_, 1, v_hyp_2995_);
lean_closure_set(v___f_3008_, 2, v_a_3003_);
lean_closure_set(v___f_3008_, 3, v_fst_3006_);
v___x_3009_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_fst_3006_, v___f_3008_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_);
return v___x_3009_;
}
else
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_dec(v_a_3003_);
lean_dec(v_hyp_2995_);
v_a_3010_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_3004_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_3004_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_dec(v_hyp_2995_);
v_a_3018_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_3002_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3002_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___boxed(lean_object* v_x_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases(v_x_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
lean_dec(v_a_3028_);
lean_dec_ref(v_a_3027_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2(lean_object* v_00_u03b1_3037_, lean_object* v_x_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_){
_start:
{
lean_object* v___x_3041_; 
v___x_3041_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v_x_3038_, v___y_3040_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3042_, lean_object* v_x_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2(v_00_u03b1_3042_, v_x_3043_, v___y_3044_, v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec_ref(v_x_3043_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7(lean_object* v_00_u03b1_3047_, lean_object* v_ref_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_ref_3048_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___boxed(lean_object* v_00_u03b1_3059_, lean_object* v_ref_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7(v_00_u03b1_3059_, v_ref_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1(lean_object* v_00_u03b1_3071_, lean_object* v_x_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v___x_3082_; 
v___x_3082_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v_x_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___boxed(lean_object* v_00_u03b1_3083_, lean_object* v_x_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1(v_00_u03b1_3083_, v_x_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2(lean_object* v_mvarId_3095_, lean_object* v_val_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v___x_3106_; 
v___x_3106_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_mvarId_3095_, v_val_3096_, v___y_3102_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___boxed(lean_object* v_mvarId_3107_, lean_object* v_val_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2(v_mvarId_3107_, v_val_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1(lean_object* v_cls_3119_, lean_object* v_msg_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v___x_3130_; 
v___x_3130_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_3119_, v_msg_3120_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___boxed(lean_object* v_cls_3131_, lean_object* v_msg_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1(v_cls_3131_, v_msg_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(lean_object* v_as_3143_, lean_object* v_as_x27_3144_, lean_object* v_b_3145_, lean_object* v_a_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v___x_3156_; 
v___x_3156_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_as_x27_3144_, v_b_3145_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___boxed(lean_object* v_as_3157_, lean_object* v_as_x27_3158_, lean_object* v_b_3159_, lean_object* v_a_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(v_as_3157_, v_as_x27_3158_, v_b_3159_, v_a_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v_as_3157_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(lean_object* v_00_u03b1_3171_, lean_object* v_ref_3172_, lean_object* v_msg_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v___x_3183_; 
v___x_3183_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_ref_3172_, v_msg_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3184_, lean_object* v_ref_3185_, lean_object* v_msg_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(v_00_u03b1_3184_, v_ref_3185_, v_msg_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v_ref_3185_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9(lean_object* v_00_u03b2_3197_, lean_object* v_x_3198_, lean_object* v_x_3199_, lean_object* v_x_3200_){
_start:
{
lean_object* v___x_3201_; 
v___x_3201_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(v_x_3198_, v_x_3199_, v_x_3200_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_3202_, lean_object* v_m_3203_, lean_object* v_a_3204_){
_start:
{
lean_object* v___x_3205_; 
v___x_3205_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v_m_3203_, v_a_3204_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3206_, lean_object* v_m_3207_, lean_object* v_a_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7(v_00_u03b2_3206_, v_m_3207_, v_a_3208_);
lean_dec(v_a_3208_);
lean_dec_ref(v_m_3207_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11(lean_object* v_00_u03b1_3210_, lean_object* v_msg_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_3211_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___boxed(lean_object* v_00_u03b1_3222_, lean_object* v_msg_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11(v_00_u03b1_3222_, v_msg_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15(lean_object* v_00_u03b2_3234_, lean_object* v_x_3235_, size_t v_x_3236_, size_t v_x_3237_, lean_object* v_x_3238_, lean_object* v_x_3239_){
_start:
{
lean_object* v___x_3240_; 
v___x_3240_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_3235_, v_x_3236_, v_x_3237_, v_x_3238_, v_x_3239_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___boxed(lean_object* v_00_u03b2_3241_, lean_object* v_x_3242_, lean_object* v_x_3243_, lean_object* v_x_3244_, lean_object* v_x_3245_, lean_object* v_x_3246_){
_start:
{
size_t v_x_22501__boxed_3247_; size_t v_x_22502__boxed_3248_; lean_object* v_res_3249_; 
v_x_22501__boxed_3247_ = lean_unbox_usize(v_x_3243_);
lean_dec(v_x_3243_);
v_x_22502__boxed_3248_ = lean_unbox_usize(v_x_3244_);
lean_dec(v_x_3244_);
v_res_3249_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15(v_00_u03b2_3241_, v_x_3242_, v_x_22501__boxed_3247_, v_x_22502__boxed_3248_, v_x_3245_, v_x_3246_);
return v_res_3249_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_3250_, lean_object* v_x_3251_, lean_object* v_x_3252_){
_start:
{
uint8_t v___x_3253_; 
v___x_3253_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v_x_3251_, v_x_3252_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3254_, lean_object* v_x_3255_, lean_object* v_x_3256_){
_start:
{
uint8_t v_res_3257_; lean_object* v_r_3258_; 
v_res_3257_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8(v_00_u03b2_3254_, v_x_3255_, v_x_3256_);
lean_dec_ref(v_x_3256_);
lean_dec_ref(v_x_3255_);
v_r_3258_ = lean_box(v_res_3257_);
return v_r_3258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11(lean_object* v_00_u03b2_3259_, lean_object* v_a_3260_, lean_object* v_x_3261_){
_start:
{
lean_object* v___x_3262_; 
v___x_3262_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(v_a_3260_, v_x_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3263_, lean_object* v_a_3264_, lean_object* v_x_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11(v_00_u03b2_3263_, v_a_3264_, v_x_3265_);
lean_dec(v_x_3265_);
lean_dec(v_a_3264_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18(lean_object* v_00_u03b2_3267_, lean_object* v_n_3268_, lean_object* v_k_3269_, lean_object* v_v_3270_){
_start:
{
lean_object* v___x_3271_; 
v___x_3271_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(v_n_3268_, v_k_3269_, v_v_3270_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19(lean_object* v_00_u03b2_3272_, size_t v_depth_3273_, lean_object* v_keys_3274_, lean_object* v_vals_3275_, lean_object* v_heq_3276_, lean_object* v_i_3277_, lean_object* v_entries_3278_){
_start:
{
lean_object* v___x_3279_; 
v___x_3279_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_depth_3273_, v_keys_3274_, v_vals_3275_, v_i_3277_, v_entries_3278_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___boxed(lean_object* v_00_u03b2_3280_, lean_object* v_depth_3281_, lean_object* v_keys_3282_, lean_object* v_vals_3283_, lean_object* v_heq_3284_, lean_object* v_i_3285_, lean_object* v_entries_3286_){
_start:
{
size_t v_depth_boxed_3287_; lean_object* v_res_3288_; 
v_depth_boxed_3287_ = lean_unbox_usize(v_depth_3281_);
lean_dec(v_depth_3281_);
v_res_3288_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19(v_00_u03b2_3280_, v_depth_boxed_3287_, v_keys_3282_, v_vals_3283_, v_heq_3284_, v_i_3285_, v_entries_3286_);
lean_dec_ref(v_vals_3283_);
lean_dec_ref(v_keys_3282_);
return v_res_3288_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13(lean_object* v_00_u03b2_3289_, lean_object* v_x_3290_, size_t v_x_3291_, lean_object* v_x_3292_){
_start:
{
uint8_t v___x_3293_; 
v___x_3293_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_3290_, v_x_3291_, v_x_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___boxed(lean_object* v_00_u03b2_3294_, lean_object* v_x_3295_, lean_object* v_x_3296_, lean_object* v_x_3297_){
_start:
{
size_t v_x_22535__boxed_3298_; uint8_t v_res_3299_; lean_object* v_r_3300_; 
v_x_22535__boxed_3298_ = lean_unbox_usize(v_x_3296_);
lean_dec(v_x_3296_);
v_res_3299_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13(v_00_u03b2_3294_, v_x_3295_, v_x_22535__boxed_3298_, v_x_3297_);
lean_dec_ref(v_x_3297_);
lean_dec_ref(v_x_3295_);
v_r_3300_ = lean_box(v_res_3299_);
return v_r_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20(lean_object* v_00_u03b2_3301_, lean_object* v_x_3302_, lean_object* v_x_3303_, lean_object* v_x_3304_, lean_object* v_x_3305_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(v_x_3302_, v_x_3303_, v_x_3304_, v_x_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18(lean_object* v_00_u03b2_3307_, lean_object* v_keys_3308_, lean_object* v_vals_3309_, lean_object* v_heq_3310_, lean_object* v_i_3311_, lean_object* v_k_3312_){
_start:
{
uint8_t v___x_3313_; 
v___x_3313_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_keys_3308_, v_i_3311_, v_k_3312_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___boxed(lean_object* v_00_u03b2_3314_, lean_object* v_keys_3315_, lean_object* v_vals_3316_, lean_object* v_heq_3317_, lean_object* v_i_3318_, lean_object* v_k_3319_){
_start:
{
uint8_t v_res_3320_; lean_object* v_r_3321_; 
v_res_3320_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18(v_00_u03b2_3314_, v_keys_3315_, v_vals_3316_, v_heq_3317_, v_i_3318_, v_k_3319_);
lean_dec_ref(v_k_3319_);
lean_dec_ref(v_vals_3316_);
lean_dec_ref(v_keys_3315_);
v_r_3321_ = lean_box(v_res_3320_);
return v_r_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1(){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3331_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3332_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2));
v___x_3333_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1));
v___x_3334_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___boxed), 10, 0);
v___x_3335_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3331_, v___x_3332_, v___x_3333_, v___x_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___boxed(lean_object* v_a_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1();
return v_res_3337_;
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
