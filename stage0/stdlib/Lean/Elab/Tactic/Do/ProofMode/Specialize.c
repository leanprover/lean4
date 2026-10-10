// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Specialize
// Imports: public import Lean.Elab.Tactic.ElabTerm public import Lean.Elab.Tactic.Do.ProofMode.MGoal import Lean.Elab.Tactic.Do.ProofMode.Basic import Lean.Elab.Tactic.Do.ProofMode.Focus
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTermWithHoles(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_pushGoals___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instInhabitedOfPure___redArg(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "specialize"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(218, 187, 99, 122, 205, 56, 35, 106)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 237, 62, 57, 45, 132, 211, 125)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(89, 242, 56, 182, 153, 42, 114, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 162, 5, 152, 35, 161, 128, 56)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Specialize"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(123, 37, 216, 217, 52, 107, 81, 131)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(134, 228, 134, 131, 92, 39, 23, 124)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(143, 84, 44, 84, 94, 37, 243, 254)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(177, 217, 191, 18, 25, 138, 163, 38)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(56, 26, 90, 163, 35, 58, 46, 128)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(168, 184, 77, 185, 84, 89, 170, 239)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 192, 102, 68, 242, 71, 106, 40)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 181, 167, 13, 84, 137, 136, 3)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 86, 143, 172, 185, 64, 192, 68)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 45, 16, 233, 253, 87, 107, 100)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(153, 248, 124, 248, 87, 161, 106, 245)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(48, 11, 80, 153, 37, 248, 122, 243)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 177, 224, 235, 201, 234, 118, 182)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 25, 207, 76, 204, 57, 77, 197)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 36, 163, 18, 92, 122, 68, 208)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1458348229) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(66, 4, 91, 112, 211, 207, 232, 93)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(237, 227, 102, 41, 10, 173, 229, 224)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(173, 214, 239, 114, 51, 49, 230, 90)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(128, 248, 53, 236, 251, 118, 25, 137)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "imp"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "imp_stateful"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 115, 245, 151, 170, 35, 10, 68)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__3_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 128, 0, 160, 79, 34, 25)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "failed to specialize "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " with "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__9_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Statefully specialize "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ". New Goal: "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__5 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__6 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(241, 143, 174, 76, 41, 16, 248, 244)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "IsPure"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__3_value),LEAN_SCALAR_PTR_LITERAL(237, 27, 197, 114, 200, 2, 153, 253)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "PropAsSPredTautology"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 191, 216, 96, 0, 209, 179, 40)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "imp_pure"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 115, 245, 151, 170, 35, 10, 68)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__7_value),LEAN_SCALAR_PTR_LITERAL(194, 113, 147, 239, 22, 13, 55, 251)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Purely specialize "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "pure_taut"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 115, 245, 151, 170, 35, 10, 68)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__11_value),LEAN_SCALAR_PTR_LITERAL(154, 170, 199, 122, 147, 93, 65, 106)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "tautological"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__13_value),LEAN_SCALAR_PTR_LITERAL(162, 116, 221, 240, 227, 37, 93, 202)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Elab.Tactic.Do.ProofMode.Specialize"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "Lean.Elab.Tactic.Do.ProofMode.mSpecializeImpPure"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__16_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Precondition of specializeImpPure violated"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__17_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "forall"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 115, 245, 151, 170, 35, 10, 68)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 228, 134, 48, 205, 218, 14, 147)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Instantiate "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Lean.Elab.Tactic.Do.ProofMode.mSpecializeForall"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Precondition of specializeForall violated"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instInhabitedTacticM___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3___closed__0 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "entails"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Could not specialize "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "focus"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Lean.Elab.Tactic.Do.ProofMode.elabMSpecialize"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Invariant of specialize violated"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unknown identifier `"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mspecialize"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(183, 227, 189, 220, 199, 75, 123, 209)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "elabMSpecialize"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 116, 229, 144, 100, 97, 175, 56)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2___boxed(lean_object**);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "pure_start"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Lean.Elab.Tactic.Do.ProofMode.elabMspecializePure"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invariant of specialize_pure violated"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "mspecializePure"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 62, 145, 88, 202, 28, 127)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "elabMspecializePure"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(150, 249, 52, 165, 26, 61, 227, 217)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_95_; uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_95_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_96_ = 0;
v___x_97_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_98_ = l_Lean_registerTraceClass(v___x_95_, v___x_96_, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_99_;
v_res_99_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_();
stack->m_obj
 = v_res_99_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2____boxed(lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_();
return v_res_101_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(lean_object* v_msgData_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___x_108_; lean_object* v_env_109_; uint8_t v___x_110_; lean_object* v_env_111_; lean_object* v___x_112_; lean_object* v_toCold_113_; lean_object* v_mctx_114_; lean_object* v_lctx_115_; lean_object* v_options_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_108_ = lean_st_ref_get(v___y_106_);
v_env_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc_ref(v_env_109_);
lean_dec(v___x_108_);
v___x_110_ = 0;
v_env_111_ = l_Lean_Environment_setRecordingDeps(v_env_109_, v___x_110_);
v___x_112_ = lean_st_ref_get(v___y_104_);
v_toCold_113_ = lean_ctor_get(v___y_105_, 0);
v_mctx_114_ = lean_ctor_get(v___x_112_, 0);
lean_inc_ref(v_mctx_114_);
lean_dec(v___x_112_);
v_lctx_115_ = lean_ctor_get(v___y_103_, 2);
v_options_116_ = lean_ctor_get(v_toCold_113_, 2);
lean_inc_ref(v_options_116_);
lean_inc_ref(v_lctx_115_);
v___x_117_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_117_, 0, v_env_111_);
lean_ctor_set(v___x_117_, 1, v_mctx_114_);
lean_ctor_set(v___x_117_, 2, v_lctx_115_);
lean_ctor_set(v___x_117_, 3, v_options_116_);
v___x_118_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v_msgData_102_);
v___x_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_102_ = stack[0].m_obj;
lean_object* v___y_103_ = stack[1].m_obj;
lean_object* v___y_104_ = stack[2].m_obj;
lean_object* v___y_105_ = stack[3].m_obj;
lean_object* v___y_106_ = stack[4].m_obj;
lean_object* v_res_120_;
v_res_120_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(v_msgData_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
stack->m_obj
 = v_res_120_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0___boxed(lean_object* v_msgData_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(v_msgData_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
return v_res_127_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_128_; double v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_float_of_nat(v___x_128_);
return v___x_129_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(lean_object* v_cls_133_, lean_object* v_msg_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_ref_140_; lean_object* v___x_141_; lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_187_; 
v_ref_140_ = lean_ctor_get(v___y_137_, 2);
v___x_141_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(v_msg_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
v_a_142_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_187_ == 0)
{
v___x_144_ = v___x_141_;
v_isShared_145_ = v_isSharedCheck_187_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_141_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_187_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; lean_object* v_traceState_147_; lean_object* v_env_148_; lean_object* v_nextMacroScope_149_; lean_object* v_ngen_150_; lean_object* v_auxDeclNGen_151_; lean_object* v_cache_152_; lean_object* v_recordedDeps_153_; lean_object* v_messages_154_; lean_object* v_infoState_155_; lean_object* v_snapshotTasks_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_186_; 
v___x_146_ = lean_st_ref_take(v___y_138_);
v_traceState_147_ = lean_ctor_get(v___x_146_, 4);
v_env_148_ = lean_ctor_get(v___x_146_, 0);
v_nextMacroScope_149_ = lean_ctor_get(v___x_146_, 1);
v_ngen_150_ = lean_ctor_get(v___x_146_, 2);
v_auxDeclNGen_151_ = lean_ctor_get(v___x_146_, 3);
v_cache_152_ = lean_ctor_get(v___x_146_, 5);
v_recordedDeps_153_ = lean_ctor_get(v___x_146_, 6);
v_messages_154_ = lean_ctor_get(v___x_146_, 7);
v_infoState_155_ = lean_ctor_get(v___x_146_, 8);
v_snapshotTasks_156_ = lean_ctor_get(v___x_146_, 9);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_186_ == 0)
{
v___x_158_ = v___x_146_;
v_isShared_159_ = v_isSharedCheck_186_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_snapshotTasks_156_);
lean_inc(v_infoState_155_);
lean_inc(v_messages_154_);
lean_inc(v_recordedDeps_153_);
lean_inc(v_cache_152_);
lean_inc(v_traceState_147_);
lean_inc(v_auxDeclNGen_151_);
lean_inc(v_ngen_150_);
lean_inc(v_nextMacroScope_149_);
lean_inc(v_env_148_);
lean_dec(v___x_146_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_186_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
uint64_t v_tid_160_; lean_object* v_traces_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_185_; 
v_tid_160_ = lean_ctor_get_uint64(v_traceState_147_, sizeof(void*)*1);
v_traces_161_ = lean_ctor_get(v_traceState_147_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v_traceState_147_);
if (v_isSharedCheck_185_ == 0)
{
v___x_163_ = v_traceState_147_;
v_isShared_164_ = v_isSharedCheck_185_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_traces_161_);
lean_dec(v_traceState_147_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_185_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; lean_object* v___x_166_; double v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_165_ = lean_box(0);
v___x_166_ = lean_box(0);
v___x_167_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0);
v___x_168_ = 0;
v___x_169_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__1));
v___x_170_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_170_, 0, v_cls_133_);
lean_ctor_set(v___x_170_, 1, v___x_166_);
lean_ctor_set(v___x_170_, 2, v___x_169_);
lean_ctor_set_float(v___x_170_, sizeof(void*)*3, v___x_167_);
lean_ctor_set_float(v___x_170_, sizeof(void*)*3 + 8, v___x_167_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*3 + 16, v___x_168_);
v___x_171_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__2));
v___x_172_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_172_, 0, v___x_170_);
lean_ctor_set(v___x_172_, 1, v_a_142_);
lean_ctor_set(v___x_172_, 2, v___x_171_);
lean_inc(v_ref_140_);
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v_ref_140_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = l_Lean_PersistentArray_push___redArg(v_traces_161_, v___x_173_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v___x_174_);
v___x_176_ = v___x_163_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_174_);
lean_ctor_set_uint64(v_reuseFailAlloc_184_, sizeof(void*)*1, v_tid_160_);
v___x_176_ = v_reuseFailAlloc_184_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_178_; 
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 4, v___x_176_);
v___x_178_ = v___x_158_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_env_148_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_nextMacroScope_149_);
lean_ctor_set(v_reuseFailAlloc_183_, 2, v_ngen_150_);
lean_ctor_set(v_reuseFailAlloc_183_, 3, v_auxDeclNGen_151_);
lean_ctor_set(v_reuseFailAlloc_183_, 4, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_183_, 5, v_cache_152_);
lean_ctor_set(v_reuseFailAlloc_183_, 6, v_recordedDeps_153_);
lean_ctor_set(v_reuseFailAlloc_183_, 7, v_messages_154_);
lean_ctor_set(v_reuseFailAlloc_183_, 8, v_infoState_155_);
lean_ctor_set(v_reuseFailAlloc_183_, 9, v_snapshotTasks_156_);
v___x_178_ = v_reuseFailAlloc_183_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_st_ref_put(v___y_138_, v___x_178_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v___x_165_);
v___x_181_ = v___x_144_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_165_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_133_ = stack[0].m_obj;
lean_object* v_msg_134_ = stack[1].m_obj;
lean_object* v___y_135_ = stack[2].m_obj;
lean_object* v___y_136_ = stack[3].m_obj;
lean_object* v___y_137_ = stack[4].m_obj;
lean_object* v___y_138_ = stack[5].m_obj;
lean_object* v_res_188_;
v_res_188_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v_cls_133_, v_msg_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
stack->m_obj
 = v_res_188_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___boxed(lean_object* v_cls_189_, lean_object* v_msg_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v_cls_189_, v_msg_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
return v_res_196_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(lean_object* v_msg_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_ref_203_; lean_object* v___x_204_; lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_213_; 
v_ref_203_ = lean_ctor_get(v___y_200_, 2);
v___x_204_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(v_msg_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
v_a_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_213_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_211_; 
lean_inc(v_ref_203_);
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v_ref_203_);
lean_ctor_set(v___x_209_, 1, v_a_205_);
if (v_isShared_208_ == 0)
{
lean_ctor_set_tag(v___x_207_, 1);
lean_ctor_set(v___x_207_, 0, v___x_209_);
v___x_211_ = v___x_207_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
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
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_197_ = stack[0].m_obj;
lean_object* v___y_198_ = stack[1].m_obj;
lean_object* v___y_199_ = stack[2].m_obj;
lean_object* v___y_200_ = stack[3].m_obj;
lean_object* v___y_201_ = stack[4].m_obj;
lean_object* v_res_214_;
v_res_214_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v_msg_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
stack->m_obj
 = v_res_214_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg___boxed(lean_object* v_msg_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v_msg_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
return v_res_221_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__5));
v___x_235_ = l_Lean_stringToMessageData(v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__7));
v___x_238_ = l_Lean_stringToMessageData(v___x_237_);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_243_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__10));
v___x_244_ = l_Lean_Name_append(v___x_243_, v___x_242_);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__12));
v___x_247_ = l_Lean_stringToMessageData(v___x_246_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__14));
v___x_250_ = l_Lean_stringToMessageData(v___x_249_);
return v___x_250_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(lean_object* v_P_251_, lean_object* v_QR_252_, lean_object* v_arg_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
uint8_t v___x_266_; 
v___x_266_ = l_Lean_Syntax_isIdent(v_arg_253_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec(v_arg_253_);
lean_dec_ref(v_QR_252_);
lean_dec_ref(v_P_251_);
v___x_267_ = lean_box(0);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
else
{
lean_object* v___x_269_; 
lean_inc_ref(v_QR_252_);
v___x_269_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_QR_252_);
if (lean_obj_tag(v___x_269_) == 1)
{
lean_object* v_val_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_427_; 
v_val_270_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_427_ == 0)
{
v___x_272_ = v___x_269_;
v_isShared_273_ = v_isSharedCheck_427_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_val_270_);
lean_dec(v___x_269_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_427_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v_p_274_; 
v_p_274_ = lean_ctor_get(v_val_270_, 2);
lean_inc_ref(v_p_274_);
if (lean_obj_tag(v_p_274_) == 5)
{
lean_object* v_fn_275_; 
v_fn_275_ = lean_ctor_get(v_p_274_, 0);
if (lean_obj_tag(v_fn_275_) == 5)
{
lean_object* v_fn_276_; 
v_fn_276_ = lean_ctor_get(v_fn_275_, 0);
if (lean_obj_tag(v_fn_276_) == 5)
{
lean_object* v_fn_277_; 
v_fn_277_ = lean_ctor_get(v_fn_276_, 0);
if (lean_obj_tag(v_fn_277_) == 4)
{
lean_object* v_declName_278_; 
v_declName_278_ = lean_ctor_get(v_fn_277_, 0);
if (lean_obj_tag(v_declName_278_) == 1)
{
lean_object* v_pre_279_; 
v_pre_279_ = lean_ctor_get(v_declName_278_, 0);
if (lean_obj_tag(v_pre_279_) == 1)
{
lean_object* v_pre_280_; 
v_pre_280_ = lean_ctor_get(v_pre_279_, 0);
if (lean_obj_tag(v_pre_280_) == 1)
{
lean_object* v_pre_281_; 
v_pre_281_ = lean_ctor_get(v_pre_280_, 0);
if (lean_obj_tag(v_pre_281_) == 1)
{
lean_object* v_pre_282_; 
v_pre_282_ = lean_ctor_get(v_pre_281_, 0);
if (lean_obj_tag(v_pre_282_) == 0)
{
lean_object* v_name_283_; lean_object* v_uniq_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_425_; 
v_name_283_ = lean_ctor_get(v_val_270_, 0);
v_uniq_284_ = lean_ctor_get(v_val_270_, 1);
v_isSharedCheck_425_ = !lean_is_exclusive(v_val_270_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; 
v_unused_426_ = lean_ctor_get(v_val_270_, 2);
lean_dec(v_unused_426_);
v___x_286_ = v_val_270_;
v_isShared_287_ = v_isSharedCheck_425_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_uniq_284_);
lean_inc(v_name_283_);
lean_dec(v_val_270_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_425_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v_arg_288_; lean_object* v_arg_289_; lean_object* v_arg_290_; lean_object* v_us_291_; lean_object* v_str_292_; lean_object* v_str_293_; lean_object* v_str_294_; lean_object* v_str_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v_arg_288_ = lean_ctor_get(v_p_274_, 1);
v_arg_289_ = lean_ctor_get(v_fn_275_, 1);
v_arg_290_ = lean_ctor_get(v_fn_276_, 1);
v_us_291_ = lean_ctor_get(v_fn_277_, 1);
v_str_292_ = lean_ctor_get(v_declName_278_, 1);
v_str_293_ = lean_ctor_get(v_pre_279_, 1);
v_str_294_ = lean_ctor_get(v_pre_280_, 1);
v_str_295_ = lean_ctor_get(v_pre_281_, 1);
v___x_296_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_297_ = lean_string_dec_eq(v_str_295_, v___x_296_);
if (v___x_297_ == 0)
{
lean_del_object(v___x_286_);
lean_dec(v_uniq_284_);
lean_dec(v_name_283_);
lean_dec_ref_known(v_p_274_, 2);
lean_del_object(v___x_272_);
lean_dec(v_arg_253_);
lean_dec_ref(v_QR_252_);
lean_dec_ref(v_P_251_);
goto v___jp_263_;
}
else
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_299_ = lean_string_dec_eq(v_str_294_, v___x_298_);
if (v___x_299_ == 0)
{
lean_del_object(v___x_286_);
lean_dec(v_uniq_284_);
lean_dec(v_name_283_);
lean_dec_ref_known(v_p_274_, 2);
lean_del_object(v___x_272_);
lean_dec(v_arg_253_);
lean_dec_ref(v_QR_252_);
lean_dec_ref(v_P_251_);
goto v___jp_263_;
}
else
{
lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_300_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_301_ = lean_string_dec_eq(v_str_293_, v___x_300_);
if (v___x_301_ == 0)
{
lean_del_object(v___x_286_);
lean_dec(v_uniq_284_);
lean_dec(v_name_283_);
lean_dec_ref_known(v_p_274_, 2);
lean_del_object(v___x_272_);
lean_dec(v_arg_253_);
lean_dec_ref(v_QR_252_);
lean_dec_ref(v_P_251_);
goto v___jp_263_;
}
else
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__2));
v___x_303_ = lean_string_dec_eq(v_str_292_, v___x_302_);
if (v___x_303_ == 0)
{
lean_del_object(v___x_286_);
lean_dec(v_uniq_284_);
lean_dec(v_name_283_);
lean_dec_ref_known(v_p_274_, 2);
lean_del_object(v___x_272_);
lean_dec(v_arg_253_);
lean_dec_ref(v_QR_252_);
lean_dec_ref(v_P_251_);
goto v___jp_263_;
}
else
{
if (lean_obj_tag(v_us_291_) == 1)
{
lean_object* v_tail_304_; 
v_tail_304_ = lean_ctor_get(v_us_291_, 1);
if (lean_obj_tag(v_tail_304_) == 0)
{
lean_object* v_head_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_head_305_ = lean_ctor_get(v_us_291_, 0);
lean_inc_ref(v_P_251_);
lean_inc_ref_n(v_arg_290_, 2);
lean_inc_n(v_head_305_, 2);
v___x_306_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_head_305_, v_arg_290_, v_P_251_, v_QR_252_);
v___x_307_ = l_Lean_Syntax_getId(v_arg_253_);
v___x_308_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(v_head_305_, v_arg_290_, v___x_306_, v___x_307_);
lean_dec(v___x_307_);
if (lean_obj_tag(v___x_308_) == 1)
{
lean_object* v_val_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_420_; 
lean_del_object(v___x_272_);
v_val_309_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_420_ == 0)
{
v___x_311_ = v___x_308_;
v_isShared_312_ = v_isSharedCheck_420_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_val_309_);
lean_dec(v___x_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_420_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v_focusHyp_313_; lean_object* v_restHyps_314_; lean_object* v_proof_315_; lean_object* v___x_316_; 
v_focusHyp_313_ = lean_ctor_get(v_val_309_, 0);
lean_inc_ref_n(v_focusHyp_313_, 2);
v_restHyps_314_ = lean_ctor_get(v_val_309_, 1);
lean_inc_ref(v_restHyps_314_);
v_proof_315_ = lean_ctor_get(v_val_309_, 2);
lean_inc_ref(v_proof_315_);
lean_dec(v_val_309_);
v___x_316_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_313_);
if (lean_obj_tag(v___x_316_) == 1)
{
lean_object* v_val_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_415_; 
lean_del_object(v___x_311_);
v_val_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_415_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_415_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_val_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_415_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
uint8_t v___x_321_; lean_object* v___x_322_; 
v___x_321_ = 0;
lean_inc_ref(v_arg_290_);
v___x_322_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_arg_253_, v_arg_290_, v_val_317_, v___x_321_, v_a_258_, v_a_259_, v_a_260_, v_a_261_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_405_; 
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; 
v_unused_406_ = lean_ctor_get(v___x_322_, 0);
lean_dec(v_unused_406_);
v___x_324_ = v___x_322_;
v_isShared_325_ = v_isSharedCheck_405_;
goto v_resetjp_323_;
}
else
{
lean_dec(v___x_322_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_405_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v_toCold_326_; lean_object* v_options_327_; lean_object* v_inheritedTraceOptions_328_; uint8_t v_hasTrace_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; 
v_toCold_326_ = lean_ctor_get(v_a_260_, 0);
v_options_327_ = lean_ctor_get(v_toCold_326_, 2);
v_inheritedTraceOptions_328_ = lean_ctor_get(v_toCold_326_, 11);
v_hasTrace_329_ = lean_ctor_get_uint8(v_options_327_, sizeof(void*)*1);
v___x_330_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4));
lean_inc_ref(v_us_291_);
v___x_331_ = l_Lean_mkConst(v___x_330_, v_us_291_);
lean_inc_ref(v_arg_288_);
lean_inc_ref(v_focusHyp_313_);
lean_inc_ref(v_P_251_);
lean_inc_ref(v_arg_290_);
v___x_332_ = l_Lean_mkApp6(v___x_331_, v_arg_290_, v_P_251_, v_restHyps_314_, v_focusHyp_313_, v_arg_288_, v_proof_315_);
if (v_hasTrace_329_ == 0)
{
lean_dec_ref(v_P_251_);
v___y_346_ = v_a_254_;
v___y_347_ = v_a_255_;
v___y_348_ = v_a_256_;
v___y_349_ = v_a_257_;
v___y_350_ = v_a_258_;
v___y_351_ = v_a_259_;
v___y_352_ = v_a_260_;
v___y_353_ = v_a_261_;
goto v___jp_345_;
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_381_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_382_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11);
v___x_383_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_328_, v_options_327_, v___x_382_);
if (v___x_383_ == 0)
{
lean_dec_ref(v_P_251_);
v___y_346_ = v_a_254_;
v___y_347_ = v_a_255_;
v___y_348_ = v_a_256_;
v___y_349_ = v_a_257_;
v___y_350_ = v_a_258_;
v___y_351_ = v_a_259_;
v___y_352_ = v_a_260_;
v___y_353_ = v_a_261_;
goto v___jp_345_;
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_384_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13);
lean_inc_ref(v_p_274_);
v___x_385_ = l_Lean_MessageData_ofExpr(v_p_274_);
v___x_386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
lean_inc_ref(v_focusHyp_313_);
v___x_389_ = l_Lean_MessageData_ofExpr(v_focusHyp_313_);
v___x_390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_388_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15);
v___x_392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_390_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
lean_inc_ref(v_arg_288_);
lean_inc_ref(v_arg_290_);
lean_inc(v_head_305_);
v___x_393_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_head_305_, v_arg_290_, v_P_251_, v_arg_288_);
v___x_394_ = l_Lean_MessageData_ofExpr(v___x_393_);
v___x_395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_392_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v___x_381_, v___x_395_, v_a_258_, v_a_259_, v_a_260_, v_a_261_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_dec_ref_known(v___x_396_, 1);
v___y_346_ = v_a_254_;
v___y_347_ = v_a_255_;
v___y_348_ = v_a_256_;
v___y_349_ = v_a_257_;
v___y_350_ = v_a_258_;
v___y_351_ = v_a_259_;
v___y_352_ = v_a_260_;
v___y_353_ = v_a_261_;
goto v___jp_345_;
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec_ref(v___x_332_);
lean_del_object(v___x_324_);
lean_del_object(v___x_319_);
lean_dec_ref(v_focusHyp_313_);
lean_del_object(v___x_286_);
lean_dec(v_uniq_284_);
lean_dec(v_name_283_);
lean_dec_ref_known(v_p_274_, 2);
v_a_397_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_396_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
v___jp_333_:
{
lean_object* v___x_335_; 
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 2, v_arg_288_);
v___x_335_ = v___x_286_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_name_283_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_uniq_284_);
lean_ctor_set(v_reuseFailAlloc_344_, 2, v_arg_288_);
v___x_335_ = v_reuseFailAlloc_344_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_336_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_335_);
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_332_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_337_);
v___x_339_ = v___x_319_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_343_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___x_341_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v___x_339_);
v___x_341_ = v___x_324_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
v___jp_345_:
{
lean_object* v___x_354_; 
lean_inc_ref(v_arg_289_);
lean_inc_ref(v_focusHyp_313_);
v___x_354_ = l_Lean_Meta_isExprDefEq(v_focusHyp_313_, v_arg_289_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; uint8_t v___x_356_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
lean_dec_ref_known(v___x_354_, 1);
v___x_356_ = lean_unbox(v_a_355_);
lean_dec(v_a_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
lean_dec_ref(v___x_332_);
lean_del_object(v___x_324_);
lean_del_object(v___x_319_);
lean_del_object(v___x_286_);
lean_dec(v_uniq_284_);
lean_dec(v_name_283_);
v___x_357_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6);
v___x_358_ = l_Lean_MessageData_ofExpr(v_p_274_);
v___x_359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_359_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = l_Lean_MessageData_ofExpr(v_focusHyp_313_);
v___x_363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_363_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_365_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
else
{
lean_inc_ref(v_arg_288_);
lean_dec_ref(v_focusHyp_313_);
lean_dec_ref_known(v_p_274_, 2);
goto v___jp_333_;
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec_ref(v___x_332_);
lean_del_object(v___x_324_);
lean_del_object(v___x_319_);
lean_dec_ref(v_focusHyp_313_);
lean_del_object(v___x_286_);
lean_dec(v_uniq_284_);
lean_dec(v_name_283_);
lean_dec_ref_known(v_p_274_, 2);
v_a_373_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_354_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_354_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_del_object(v___x_319_);
lean_dec_ref(v_proof_315_);
lean_dec_ref(v_restHyps_314_);
lean_dec_ref(v_focusHyp_313_);
lean_del_object(v___x_286_);
lean_dec(v_uniq_284_);
lean_dec(v_name_283_);
lean_dec_ref_known(v_p_274_, 2);
lean_dec_ref(v_P_251_);
v_a_407_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_322_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_322_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
else
{
lean_object* v___x_416_; lean_object* v___x_418_; 
lean_dec(v___x_316_);
lean_dec_ref(v_proof_315_);
lean_dec_ref(v_restHyps_314_);
lean_dec_ref(v_focusHyp_313_);
lean_del_object(v___x_286_);
lean_dec(v_uniq_284_);
lean_dec(v_name_283_);
lean_dec_ref_known(v_p_274_, 2);
lean_dec(v_arg_253_);
lean_dec_ref(v_P_251_);
v___x_416_ = lean_box(0);
if (v_isShared_312_ == 0)
{
lean_ctor_set_tag(v___x_311_, 0);
lean_ctor_set(v___x_311_, 0, v___x_416_);
v___x_418_ = v___x_311_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
else
{
lean_object* v___x_421_; lean_object* v___x_423_; 
lean_dec(v___x_308_);
lean_del_object(v___x_286_);
lean_dec(v_uniq_284_);
lean_dec(v_name_283_);
lean_dec_ref_known(v_p_274_, 2);
lean_dec(v_arg_253_);
lean_dec_ref(v_P_251_);
v___x_421_ = lean_box(0);
if (v_isShared_273_ == 0)
{
lean_ctor_set_tag(v___x_272_, 0);
lean_ctor_set(v___x_272_, 0, v___x_421_);
v___x_423_ = v___x_272_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
else
{
lean_del_object(v___x_286_);
lean_dec(v_uniq_284_);
lean_dec(v_name_283_);
lean_dec_ref_known(v_p_274_, 2);
lean_del_object(v___x_272_);
lean_dec(v_arg_253_);
lean_dec_ref(v_QR_252_);
lean_dec_ref(v_P_251_);
goto v___jp_263_;
}
}
else
{
lean_del_object(v___x_286_);
lean_dec(v_uniq_284_);
lean_dec(v_name_283_);
lean_dec_ref_known(v_p_274_, 2);
lean_del_object(v___x_272_);
lean_dec(v_arg_253_);
lean_dec_ref(v_QR_252_);
lean_dec_ref(v_P_251_);
goto v___jp_263_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_p_274_, 2);
lean_del_object(v___x_272_);
lean_dec(v_val_270_);
lean_dec(v_arg_253_);
lean_dec_ref(v_QR_252_);
lean_dec_ref(v_P_251_);
goto v___jp_263_;
}
}
else
{
lean_dec_ref_known(v_p_274_, 2);
lean_del_object(v___x_272_);
lean_dec(v_val_270_);
lean_dec(v_arg_253_);
lean_dec_ref(v_QR_252_);
lean_dec_ref(v_P_251_);
goto v___jp_263_;
}
}
else
{
lean_dec_ref_known(v_p_274_, 2);
lean_del_object(v___x_272_);
lean_dec(v_val_270_);
lean_dec(v_arg_253_);
lean_dec_ref(v_QR_252_);
lean_dec_ref(v_P_251_);
goto v___jp_263_;
}
}
else
{
lean_dec_ref_known(v_p_274_, 2);
lean_del_object(v___x_272_);
lean_dec(v_val_270_);
lean_dec(v_arg_253_);
lean_dec_ref(v_QR_252_);
lean_dec_ref(v_P_251_);
goto v___jp_263_;
}
}
else
{
lean_dec_ref_known(v_p_274_, 2);
lean_del_object(v___x_272_);
lean_dec(v_val_270_);
lean_dec(v_arg_253_);
lean_dec_ref(v_QR_252_);
lean_dec_ref(v_P_251_);
goto v___jp_263_;
}
}
else
{
lean_dec_ref_known(v_p_274_, 2);
lean_del_object(v___x_272_);
lean_dec(v_val_270_);
lean_dec(v_arg_253_);
lean_dec_ref(v_QR_252_);
lean_dec_ref(v_P_251_);
goto v___jp_263_;
}
}
else
{
lean_dec_ref_known(v_p_274_, 2);
lean_del_object(v___x_272_);
lean_dec(v_val_270_);
lean_dec(v_arg_253_);
lean_dec_ref(v_QR_252_);
lean_dec_ref(v_P_251_);
goto v___jp_263_;
}
}
else
{
lean_dec_ref_known(v_p_274_, 2);
lean_del_object(v___x_272_);
lean_dec(v_val_270_);
lean_dec(v_arg_253_);
lean_dec_ref(v_QR_252_);
lean_dec_ref(v_P_251_);
goto v___jp_263_;
}
}
else
{
lean_dec_ref(v_p_274_);
lean_del_object(v___x_272_);
lean_dec(v_val_270_);
lean_dec(v_arg_253_);
lean_dec_ref(v_QR_252_);
lean_dec_ref(v_P_251_);
goto v___jp_263_;
}
}
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; 
lean_dec(v___x_269_);
lean_dec(v_arg_253_);
lean_dec_ref(v_QR_252_);
lean_dec_ref(v_P_251_);
v___x_428_ = lean_box(0);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
}
v___jp_263_:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_box(0);
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
return v___x_265_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_0interp(lean_interpreter_value* stack)
{
lean_object* v_P_251_ = stack[0].m_obj;
lean_object* v_QR_252_ = stack[1].m_obj;
lean_object* v_arg_253_ = stack[2].m_obj;
lean_object* v_a_254_ = stack[3].m_obj;
lean_object* v_a_255_ = stack[4].m_obj;
lean_object* v_a_256_ = stack[5].m_obj;
lean_object* v_a_257_ = stack[6].m_obj;
lean_object* v_a_258_ = stack[7].m_obj;
lean_object* v_a_259_ = stack[8].m_obj;
lean_object* v_a_260_ = stack[9].m_obj;
lean_object* v_a_261_ = stack[10].m_obj;
lean_object* v_res_430_;
v_res_430_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(v_P_251_, v_QR_252_, v_arg_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___boxed(lean_object* v_P_431_, lean_object* v_QR_432_, lean_object* v_arg_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(v_P_431_, v_QR_432_, v_arg_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
return v_res_443_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0(lean_object* v_00_u03b1_444_, lean_object* v_msg_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v_msg_445_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
return v___x_455_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_445_ = stack[1].m_obj;
lean_object* v___y_446_ = stack[2].m_obj;
lean_object* v___y_447_ = stack[3].m_obj;
lean_object* v___y_448_ = stack[4].m_obj;
lean_object* v___y_449_ = stack[5].m_obj;
lean_object* v___y_450_ = stack[6].m_obj;
lean_object* v___y_451_ = stack[7].m_obj;
lean_object* v___y_452_ = stack[8].m_obj;
lean_object* v___y_453_ = stack[9].m_obj;
lean_object* v_res_456_;
v_res_456_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0(lean_box(0), v_msg_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
stack->m_obj
 = v_res_456_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___boxed(lean_object* v_00_u03b1_457_, lean_object* v_msg_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0(v_00_u03b1_457_, v_msg_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
return v_res_468_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1(lean_object* v_cls_469_, lean_object* v_msg_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v_cls_469_, v_msg_470_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
return v___x_480_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_469_ = stack[0].m_obj;
lean_object* v_msg_470_ = stack[1].m_obj;
lean_object* v___y_471_ = stack[2].m_obj;
lean_object* v___y_472_ = stack[3].m_obj;
lean_object* v___y_473_ = stack[4].m_obj;
lean_object* v___y_474_ = stack[5].m_obj;
lean_object* v___y_475_ = stack[6].m_obj;
lean_object* v___y_476_ = stack[7].m_obj;
lean_object* v___y_477_ = stack[8].m_obj;
lean_object* v___y_478_ = stack[9].m_obj;
lean_object* v_res_481_;
v_res_481_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1(v_cls_469_, v_msg_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
stack->m_obj
 = v_res_481_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___boxed(lean_object* v_cls_482_, lean_object* v_msg_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1(v_cls_482_, v_msg_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
return v_res_493_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0(void){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_instMonadEIO___redArg();
return v___x_494_;
}
}
lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(lean_object* v_msg_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v_toApplicative_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_605_; 
v___x_511_ = lean_obj_once(&l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0, &l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0);
v___x_512_ = l_StateRefT_x27_instMonad___redArg(v___x_511_);
v_toApplicative_513_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_605_ == 0)
{
lean_object* v_unused_606_; 
v_unused_606_ = lean_ctor_get(v___x_512_, 1);
lean_dec(v_unused_606_);
v___x_515_ = v___x_512_;
v_isShared_516_ = v_isSharedCheck_605_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_toApplicative_513_);
lean_dec(v___x_512_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_605_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v_toFunctor_517_; lean_object* v_toSeq_518_; lean_object* v_toSeqLeft_519_; lean_object* v_toSeqRight_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_603_; 
v_toFunctor_517_ = lean_ctor_get(v_toApplicative_513_, 0);
v_toSeq_518_ = lean_ctor_get(v_toApplicative_513_, 2);
v_toSeqLeft_519_ = lean_ctor_get(v_toApplicative_513_, 3);
v_toSeqRight_520_ = lean_ctor_get(v_toApplicative_513_, 4);
v_isSharedCheck_603_ = !lean_is_exclusive(v_toApplicative_513_);
if (v_isSharedCheck_603_ == 0)
{
lean_object* v_unused_604_; 
v_unused_604_ = lean_ctor_get(v_toApplicative_513_, 1);
lean_dec(v_unused_604_);
v___x_522_ = v_toApplicative_513_;
v_isShared_523_ = v_isSharedCheck_603_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_toSeqRight_520_);
lean_inc(v_toSeqLeft_519_);
lean_inc(v_toSeq_518_);
lean_inc(v_toFunctor_517_);
lean_dec(v_toApplicative_513_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_603_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___f_524_; lean_object* v___f_525_; lean_object* v___f_526_; lean_object* v___f_527_; lean_object* v___x_528_; lean_object* v___f_529_; lean_object* v___f_530_; lean_object* v___f_531_; lean_object* v___x_533_; 
v___f_524_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__1));
v___f_525_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__2));
lean_inc_ref(v_toFunctor_517_);
v___f_526_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_526_, 0, v_toFunctor_517_);
v___f_527_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_527_, 0, v_toFunctor_517_);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v___f_526_);
lean_ctor_set(v___x_528_, 1, v___f_527_);
v___f_529_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_529_, 0, v_toSeqRight_520_);
v___f_530_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_530_, 0, v_toSeqLeft_519_);
v___f_531_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_531_, 0, v_toSeq_518_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 4, v___f_529_);
lean_ctor_set(v___x_522_, 3, v___f_530_);
lean_ctor_set(v___x_522_, 2, v___f_531_);
lean_ctor_set(v___x_522_, 1, v___f_524_);
lean_ctor_set(v___x_522_, 0, v___x_528_);
v___x_533_ = v___x_522_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v___f_524_);
lean_ctor_set(v_reuseFailAlloc_602_, 2, v___f_531_);
lean_ctor_set(v_reuseFailAlloc_602_, 3, v___f_530_);
lean_ctor_set(v_reuseFailAlloc_602_, 4, v___f_529_);
v___x_533_ = v_reuseFailAlloc_602_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_535_; 
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 1, v___f_525_);
lean_ctor_set(v___x_515_, 0, v___x_533_);
v___x_535_ = v___x_515_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v___f_525_);
v___x_535_ = v_reuseFailAlloc_601_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_536_; lean_object* v_toApplicative_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_599_; 
v___x_536_ = l_StateRefT_x27_instMonad___redArg(v___x_535_);
v_toApplicative_537_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; 
v_unused_600_ = lean_ctor_get(v___x_536_, 1);
lean_dec(v_unused_600_);
v___x_539_ = v___x_536_;
v_isShared_540_ = v_isSharedCheck_599_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_toApplicative_537_);
lean_dec(v___x_536_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_599_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v_toFunctor_541_; lean_object* v_toSeq_542_; lean_object* v_toSeqLeft_543_; lean_object* v_toSeqRight_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_597_; 
v_toFunctor_541_ = lean_ctor_get(v_toApplicative_537_, 0);
v_toSeq_542_ = lean_ctor_get(v_toApplicative_537_, 2);
v_toSeqLeft_543_ = lean_ctor_get(v_toApplicative_537_, 3);
v_toSeqRight_544_ = lean_ctor_get(v_toApplicative_537_, 4);
v_isSharedCheck_597_ = !lean_is_exclusive(v_toApplicative_537_);
if (v_isSharedCheck_597_ == 0)
{
lean_object* v_unused_598_; 
v_unused_598_ = lean_ctor_get(v_toApplicative_537_, 1);
lean_dec(v_unused_598_);
v___x_546_ = v_toApplicative_537_;
v_isShared_547_ = v_isSharedCheck_597_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_toSeqRight_544_);
lean_inc(v_toSeqLeft_543_);
lean_inc(v_toSeq_542_);
lean_inc(v_toFunctor_541_);
lean_dec(v_toApplicative_537_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_597_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___f_548_; lean_object* v___f_549_; lean_object* v___f_550_; lean_object* v___f_551_; lean_object* v___x_552_; lean_object* v___f_553_; lean_object* v___f_554_; lean_object* v___f_555_; lean_object* v___x_557_; 
v___f_548_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__3));
v___f_549_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__4));
lean_inc_ref(v_toFunctor_541_);
v___f_550_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_550_, 0, v_toFunctor_541_);
v___f_551_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_551_, 0, v_toFunctor_541_);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v___f_550_);
lean_ctor_set(v___x_552_, 1, v___f_551_);
v___f_553_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_553_, 0, v_toSeqRight_544_);
v___f_554_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_554_, 0, v_toSeqLeft_543_);
v___f_555_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_555_, 0, v_toSeq_542_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 4, v___f_553_);
lean_ctor_set(v___x_546_, 3, v___f_554_);
lean_ctor_set(v___x_546_, 2, v___f_555_);
lean_ctor_set(v___x_546_, 1, v___f_548_);
lean_ctor_set(v___x_546_, 0, v___x_552_);
v___x_557_ = v___x_546_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v___f_548_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v___f_555_);
lean_ctor_set(v_reuseFailAlloc_596_, 3, v___f_554_);
lean_ctor_set(v_reuseFailAlloc_596_, 4, v___f_553_);
v___x_557_ = v_reuseFailAlloc_596_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_559_; 
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___f_549_);
lean_ctor_set(v___x_539_, 0, v___x_557_);
v___x_559_ = v___x_539_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v___f_549_);
v___x_559_ = v_reuseFailAlloc_595_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; lean_object* v_toApplicative_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_593_; 
v___x_560_ = l_StateRefT_x27_instMonad___redArg(v___x_559_);
v_toApplicative_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_593_ == 0)
{
lean_object* v_unused_594_; 
v_unused_594_ = lean_ctor_get(v___x_560_, 1);
lean_dec(v_unused_594_);
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_593_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_toApplicative_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_593_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v_toFunctor_565_; lean_object* v_toSeq_566_; lean_object* v_toSeqLeft_567_; lean_object* v_toSeqRight_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_591_; 
v_toFunctor_565_ = lean_ctor_get(v_toApplicative_561_, 0);
v_toSeq_566_ = lean_ctor_get(v_toApplicative_561_, 2);
v_toSeqLeft_567_ = lean_ctor_get(v_toApplicative_561_, 3);
v_toSeqRight_568_ = lean_ctor_get(v_toApplicative_561_, 4);
v_isSharedCheck_591_ = !lean_is_exclusive(v_toApplicative_561_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v_toApplicative_561_, 1);
lean_dec(v_unused_592_);
v___x_570_ = v_toApplicative_561_;
v_isShared_571_ = v_isSharedCheck_591_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_toSeqRight_568_);
lean_inc(v_toSeqLeft_567_);
lean_inc(v_toSeq_566_);
lean_inc(v_toFunctor_565_);
lean_dec(v_toApplicative_561_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_591_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___f_572_; lean_object* v___f_573_; lean_object* v___f_574_; lean_object* v___f_575_; lean_object* v___x_576_; lean_object* v___f_577_; lean_object* v___f_578_; lean_object* v___f_579_; lean_object* v___x_581_; 
v___f_572_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__5));
v___f_573_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__6));
lean_inc_ref(v_toFunctor_565_);
v___f_574_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_574_, 0, v_toFunctor_565_);
v___f_575_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_575_, 0, v_toFunctor_565_);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v___f_574_);
lean_ctor_set(v___x_576_, 1, v___f_575_);
v___f_577_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_577_, 0, v_toSeqRight_568_);
v___f_578_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_578_, 0, v_toSeqLeft_567_);
v___f_579_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_579_, 0, v_toSeq_566_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 4, v___f_577_);
lean_ctor_set(v___x_570_, 3, v___f_578_);
lean_ctor_set(v___x_570_, 2, v___f_579_);
lean_ctor_set(v___x_570_, 1, v___f_572_);
lean_ctor_set(v___x_570_, 0, v___x_576_);
v___x_581_ = v___x_570_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v___f_572_);
lean_ctor_set(v_reuseFailAlloc_590_, 2, v___f_579_);
lean_ctor_set(v_reuseFailAlloc_590_, 3, v___f_578_);
lean_ctor_set(v_reuseFailAlloc_590_, 4, v___f_577_);
v___x_581_ = v_reuseFailAlloc_590_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_583_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v___f_573_);
lean_ctor_set(v___x_563_, 0, v___x_581_);
v___x_583_ = v___x_563_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v___f_573_);
v___x_583_ = v_reuseFailAlloc_589_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_10473__overap_587_; lean_object* v___x_588_; 
v___x_584_ = l_StateRefT_x27_instMonad___redArg(v___x_583_);
v___x_585_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_585_, 0, lean_box(0));
lean_closure_set(v___x_585_, 1, lean_box(0));
lean_closure_set(v___x_585_, 2, v___x_584_);
v___x_586_ = l_OptionT_instInhabitedOfPure___redArg(v___x_585_);
v___x_10473__overap_587_ = lean_panic_fn_borrowed(v___x_586_, v_msg_501_);
lean_dec(v___x_586_);
lean_inc(v___y_509_);
lean_inc_ref(v___y_508_);
lean_inc(v___y_507_);
lean_inc_ref(v___y_506_);
lean_inc(v___y_505_);
lean_inc_ref(v___y_504_);
lean_inc(v___y_503_);
lean_inc_ref(v___y_502_);
v___x_588_ = lean_apply_9(v___x_10473__overap_587_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, lean_box(0));
return v___x_588_;
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
}
}
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_501_ = stack[0].m_obj;
lean_object* v___y_502_ = stack[1].m_obj;
lean_object* v___y_503_ = stack[2].m_obj;
lean_object* v___y_504_ = stack[3].m_obj;
lean_object* v___y_505_ = stack[4].m_obj;
lean_object* v___y_506_ = stack[5].m_obj;
lean_object* v___y_507_ = stack[6].m_obj;
lean_object* v___y_508_ = stack[7].m_obj;
lean_object* v___y_509_ = stack[8].m_obj;
lean_object* v_res_607_;
v_res_607_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(v_msg_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
stack->m_obj
 = v_res_607_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___boxed(lean_object* v_msg_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(v_msg_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
return v_res_618_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_box(0);
v___x_620_ = l_Lean_mkSort(v___x_619_);
return v___x_620_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0);
v___x_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__9));
v___x_649_ = l_Lean_stringToMessageData(v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_668_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__17));
v___x_669_ = lean_unsigned_to_nat(37u);
v___x_670_ = lean_unsigned_to_nat(45u);
v___x_671_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__16));
v___x_672_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15));
v___x_673_ = l_mkPanicMessageWithDecl(v___x_672_, v___x_671_, v___x_670_, v___x_669_, v___x_668_);
return v___x_673_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(lean_object* v_P_674_, lean_object* v_QR_675_, lean_object* v_arg_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_QR_675_);
if (lean_obj_tag(v___x_689_) == 1)
{
lean_object* v_val_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_868_; 
v_val_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_868_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_868_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_val_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_868_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_p_694_; 
v_p_694_ = lean_ctor_get(v_val_690_, 2);
lean_inc_ref(v_p_694_);
if (lean_obj_tag(v_p_694_) == 5)
{
lean_object* v_name_695_; lean_object* v_uniq_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_866_; 
v_name_695_ = lean_ctor_get(v_val_690_, 0);
v_uniq_696_ = lean_ctor_get(v_val_690_, 1);
v_isSharedCheck_866_ = !lean_is_exclusive(v_val_690_);
if (v_isSharedCheck_866_ == 0)
{
lean_object* v_unused_867_; 
v_unused_867_ = lean_ctor_get(v_val_690_, 2);
lean_dec(v_unused_867_);
v___x_698_ = v_val_690_;
v_isShared_699_ = v_isSharedCheck_866_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_uniq_696_);
lean_inc(v_name_695_);
lean_dec(v_val_690_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_866_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_fn_700_; lean_object* v_arg_701_; lean_object* v___y_703_; 
v_fn_700_ = lean_ctor_get(v_p_694_, 0);
v_arg_701_ = lean_ctor_get(v_p_694_, 1);
lean_inc_ref(v_arg_701_);
if (lean_obj_tag(v_fn_700_) == 5)
{
lean_object* v_fn_713_; 
v_fn_713_ = lean_ctor_get(v_fn_700_, 0);
if (lean_obj_tag(v_fn_713_) == 5)
{
lean_object* v_fn_714_; 
v_fn_714_ = lean_ctor_get(v_fn_713_, 0);
if (lean_obj_tag(v_fn_714_) == 4)
{
lean_object* v_declName_715_; 
v_declName_715_ = lean_ctor_get(v_fn_714_, 0);
if (lean_obj_tag(v_declName_715_) == 1)
{
lean_object* v_pre_716_; 
v_pre_716_ = lean_ctor_get(v_declName_715_, 0);
if (lean_obj_tag(v_pre_716_) == 1)
{
lean_object* v_pre_717_; 
v_pre_717_ = lean_ctor_get(v_pre_716_, 0);
if (lean_obj_tag(v_pre_717_) == 1)
{
lean_object* v_pre_718_; 
v_pre_718_ = lean_ctor_get(v_pre_717_, 0);
if (lean_obj_tag(v_pre_718_) == 1)
{
lean_object* v_pre_719_; 
v_pre_719_ = lean_ctor_get(v_pre_718_, 0);
if (lean_obj_tag(v_pre_719_) == 0)
{
lean_object* v_arg_720_; lean_object* v_arg_721_; lean_object* v_us_722_; lean_object* v_str_723_; lean_object* v_str_724_; lean_object* v_str_725_; lean_object* v_str_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v_arg_720_ = lean_ctor_get(v_fn_700_, 1);
lean_inc_ref(v_arg_720_);
v_arg_721_ = lean_ctor_get(v_fn_713_, 1);
lean_inc_ref(v_arg_721_);
v_us_722_ = lean_ctor_get(v_fn_714_, 1);
v_str_723_ = lean_ctor_get(v_declName_715_, 1);
v_str_724_ = lean_ctor_get(v_pre_716_, 1);
v_str_725_ = lean_ctor_get(v_pre_717_, 1);
v_str_726_ = lean_ctor_get(v_pre_718_, 1);
v___x_727_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_728_ = lean_string_dec_eq(v_str_726_, v___x_727_);
if (v___x_728_ == 0)
{
lean_dec_ref(v_arg_721_);
lean_dec_ref(v_arg_720_);
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_dec_ref_known(v_p_694_, 2);
lean_del_object(v___x_692_);
lean_dec(v_arg_676_);
lean_dec_ref(v_P_674_);
goto v___jp_686_;
}
else
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_730_ = lean_string_dec_eq(v_str_725_, v___x_729_);
if (v___x_730_ == 0)
{
lean_dec_ref(v_arg_721_);
lean_dec_ref(v_arg_720_);
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_dec_ref_known(v_p_694_, 2);
lean_del_object(v___x_692_);
lean_dec(v_arg_676_);
lean_dec_ref(v_P_674_);
goto v___jp_686_;
}
else
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_732_ = lean_string_dec_eq(v_str_724_, v___x_731_);
if (v___x_732_ == 0)
{
lean_dec_ref(v_arg_721_);
lean_dec_ref(v_arg_720_);
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_dec_ref_known(v_p_694_, 2);
lean_del_object(v___x_692_);
lean_dec(v_arg_676_);
lean_dec_ref(v_P_674_);
goto v___jp_686_;
}
else
{
lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_733_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__2));
v___x_734_ = lean_string_dec_eq(v_str_723_, v___x_733_);
if (v___x_734_ == 0)
{
lean_dec_ref(v_arg_721_);
lean_dec_ref(v_arg_720_);
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_dec_ref_known(v_p_694_, 2);
lean_del_object(v___x_692_);
lean_dec(v_arg_676_);
lean_dec_ref(v_P_674_);
goto v___jp_686_;
}
else
{
if (lean_obj_tag(v_us_722_) == 1)
{
lean_object* v_tail_735_; 
v_tail_735_ = lean_ctor_get(v_us_722_, 1);
if (lean_obj_tag(v_tail_735_) == 0)
{
lean_object* v_head_736_; lean_object* v___x_737_; uint8_t v___x_738_; lean_object* v___x_739_; 
v_head_736_ = lean_ctor_get(v_us_722_, 0);
lean_inc(v_head_736_);
v___x_737_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1);
v___x_738_ = 0;
v___x_739_ = l_Lean_Meta_mkFreshExprMVar(v___x_737_, v___x_738_, v_pre_719_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc_n(v_a_740_, 2);
lean_dec_ref_known(v___x_739_, 1);
v___x_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_741_, 0, v_a_740_);
v___x_742_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2));
v___x_743_ = lean_box(0);
v___x_744_ = l_Lean_Elab_Tactic_elabTermWithHoles(v_arg_676_, v___x_741_, v___x_742_, v___x_734_, v___x_743_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v_fst_746_; lean_object* v_snd_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_842_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v___x_744_, 1);
v_fst_746_ = lean_ctor_get(v_a_745_, 0);
v_snd_747_ = lean_ctor_get(v_a_745_, 1);
v_isSharedCheck_842_ = !lean_is_exclusive(v_a_745_);
if (v_isSharedCheck_842_ == 0)
{
v___x_749_ = v_a_745_;
v_isShared_750_ = v_isSharedCheck_842_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_snd_747_);
lean_inc(v_fst_746_);
lean_dec(v_a_745_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_842_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v_00_u03c6_755_; lean_object* v_h_u03c6_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___x_825_; 
v___x_751_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4));
lean_inc_ref(v_us_722_);
v___x_752_ = l_Lean_mkConst(v___x_751_, v_us_722_);
lean_inc(v_a_740_);
lean_inc_ref(v_arg_720_);
lean_inc_ref(v_arg_721_);
v___x_753_ = l_Lean_mkApp3(v___x_752_, v_arg_721_, v_arg_720_, v_a_740_);
v___x_825_ = l_Lean_Meta_synthInstance_x3f(v___x_753_, v___x_743_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
lean_dec_ref_known(v___x_825_, 1);
if (lean_obj_tag(v_a_826_) == 1)
{
lean_object* v_val_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_val_827_ = lean_ctor_get(v_a_826_, 0);
lean_inc(v_val_827_);
lean_dec_ref_known(v_a_826_, 1);
v___x_828_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12));
lean_inc_ref_n(v_us_722_, 2);
v___x_829_ = l_Lean_mkConst(v___x_828_, v_us_722_);
lean_inc_ref_n(v_arg_720_, 2);
lean_inc_ref_n(v_arg_721_, 2);
v___x_830_ = l_Lean_mkApp5(v___x_829_, v_arg_721_, v_a_740_, v_arg_720_, v_val_827_, v_fst_746_);
v___x_831_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14));
v___x_832_ = l_Lean_mkConst(v___x_831_, v_us_722_);
v___x_833_ = l_Lean_mkAppB(v___x_832_, v_arg_721_, v_arg_720_);
v_00_u03c6_755_ = v___x_833_;
v_h_u03c6_756_ = v___x_830_;
v___y_757_ = v_a_678_;
v___y_758_ = v_a_681_;
v___y_759_ = v_a_682_;
v___y_760_ = v_a_683_;
v___y_761_ = v_a_684_;
goto v___jp_754_;
}
else
{
lean_dec(v_a_826_);
v_00_u03c6_755_ = v_a_740_;
v_h_u03c6_756_ = v_fst_746_;
v___y_757_ = v_a_678_;
v___y_758_ = v_a_681_;
v___y_759_ = v_a_682_;
v___y_760_ = v_a_683_;
v___y_761_ = v_a_684_;
goto v___jp_754_;
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_del_object(v___x_749_);
lean_dec(v_snd_747_);
lean_dec(v_fst_746_);
lean_dec(v_a_740_);
lean_dec(v_head_736_);
lean_dec_ref(v_arg_721_);
lean_dec_ref(v_arg_720_);
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_dec_ref_known(v_p_694_, 2);
lean_del_object(v___x_692_);
lean_dec_ref(v_P_674_);
v_a_834_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_825_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_825_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
v___jp_754_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_762_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6));
lean_inc_ref(v_us_722_);
v___x_763_ = l_Lean_mkConst(v___x_762_, v_us_722_);
lean_inc_ref(v_arg_720_);
lean_inc_ref(v_arg_721_);
lean_inc_ref(v_00_u03c6_755_);
v___x_764_ = l_Lean_mkApp3(v___x_763_, v_00_u03c6_755_, v_arg_721_, v_arg_720_);
v___x_765_ = l_Lean_Meta_synthInstance_x3f(v___x_764_, v___x_743_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_816_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_816_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_816_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_816_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
if (lean_obj_tag(v_a_766_) == 1)
{
lean_object* v_val_770_; lean_object* v___x_771_; 
lean_del_object(v___x_768_);
v_val_770_ = lean_ctor_get(v_a_766_, 0);
lean_inc(v_val_770_);
lean_dec_ref_known(v_a_766_, 1);
v___x_771_ = l_Lean_Elab_Tactic_pushGoals___redArg(v_snd_747_, v___y_757_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_toCold_772_; lean_object* v_options_773_; lean_object* v_inheritedTraceOptions_774_; uint8_t v_hasTrace_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
lean_dec_ref_known(v___x_771_, 1);
v_toCold_772_ = lean_ctor_get(v___y_760_, 0);
v_options_773_ = lean_ctor_get(v_toCold_772_, 2);
v_inheritedTraceOptions_774_ = lean_ctor_get(v_toCold_772_, 11);
v_hasTrace_775_ = lean_ctor_get_uint8(v_options_773_, sizeof(void*)*1);
v___x_776_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8));
lean_inc_ref(v_us_722_);
v___x_777_ = l_Lean_mkConst(v___x_776_, v_us_722_);
lean_inc_ref(v_arg_701_);
lean_inc_ref(v_arg_720_);
lean_inc_ref(v_P_674_);
lean_inc_ref(v_arg_721_);
v___x_778_ = l_Lean_mkApp7(v___x_777_, v_arg_721_, v_00_u03c6_755_, v_P_674_, v_arg_720_, v_arg_701_, v_val_770_, v_h_u03c6_756_);
if (v_hasTrace_775_ == 0)
{
lean_del_object(v___x_749_);
lean_dec(v_head_736_);
lean_dec_ref(v_arg_721_);
lean_dec_ref(v_arg_720_);
lean_dec_ref_known(v_p_694_, 2);
lean_dec_ref(v_P_674_);
v___y_703_ = v___x_778_;
goto v___jp_702_;
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_779_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_780_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11);
v___x_781_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_774_, v_options_773_, v___x_780_);
if (v___x_781_ == 0)
{
lean_del_object(v___x_749_);
lean_dec(v_head_736_);
lean_dec_ref(v_arg_721_);
lean_dec_ref(v_arg_720_);
lean_dec_ref_known(v_p_694_, 2);
lean_dec_ref(v_P_674_);
v___y_703_ = v___x_778_;
goto v___jp_702_;
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_782_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10);
v___x_783_ = l_Lean_MessageData_ofExpr(v_p_694_);
if (v_isShared_750_ == 0)
{
lean_ctor_set_tag(v___x_749_, 7);
lean_ctor_set(v___x_749_, 1, v___x_783_);
lean_ctor_set(v___x_749_, 0, v___x_782_);
v___x_785_ = v___x_749_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v___x_783_);
v___x_785_ = v_reuseFailAlloc_804_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_786_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = l_Lean_MessageData_ofExpr(v_arg_720_);
v___x_789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_787_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15);
v___x_791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_789_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
lean_inc_ref(v_arg_701_);
v___x_792_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_head_736_, v_arg_721_, v_P_674_, v_arg_701_);
v___x_793_ = l_Lean_MessageData_ofExpr(v___x_792_);
v___x_794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_791_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v___x_779_, v___x_794_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_dec_ref_known(v___x_795_, 1);
v___y_703_ = v___x_778_;
goto v___jp_702_;
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v___x_778_);
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_del_object(v___x_692_);
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec(v_val_770_);
lean_dec_ref(v_h_u03c6_756_);
lean_dec_ref(v_00_u03c6_755_);
lean_del_object(v___x_749_);
lean_dec(v_head_736_);
lean_dec_ref(v_arg_721_);
lean_dec_ref(v_arg_720_);
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_dec_ref_known(v_p_694_, 2);
lean_del_object(v___x_692_);
lean_dec_ref(v_P_674_);
v_a_805_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_771_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_771_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
else
{
lean_object* v___x_814_; 
lean_dec(v_a_766_);
lean_dec_ref(v_h_u03c6_756_);
lean_dec_ref(v_00_u03c6_755_);
lean_del_object(v___x_749_);
lean_dec(v_snd_747_);
lean_dec(v_head_736_);
lean_dec_ref(v_arg_721_);
lean_dec_ref(v_arg_720_);
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_dec_ref_known(v_p_694_, 2);
lean_del_object(v___x_692_);
lean_dec_ref(v_P_674_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_743_);
v___x_814_ = v___x_768_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_743_);
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
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec_ref(v_h_u03c6_756_);
lean_dec_ref(v_00_u03c6_755_);
lean_del_object(v___x_749_);
lean_dec(v_snd_747_);
lean_dec(v_head_736_);
lean_dec_ref(v_arg_721_);
lean_dec_ref(v_arg_720_);
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_dec_ref_known(v_p_694_, 2);
lean_del_object(v___x_692_);
lean_dec_ref(v_P_674_);
v_a_817_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_765_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_765_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_857_; 
lean_dec(v_a_740_);
lean_dec(v_head_736_);
lean_dec_ref(v_arg_721_);
lean_dec_ref(v_arg_720_);
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_dec_ref_known(v_p_694_, 2);
lean_del_object(v___x_692_);
lean_dec_ref(v_P_674_);
v_a_843_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_857_ == 0)
{
v___x_845_ = v___x_744_;
v_isShared_846_ = v_isSharedCheck_857_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_744_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_857_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
uint8_t v___y_848_; uint8_t v___x_855_; 
v___x_855_ = l_Lean_Exception_isInterrupt(v_a_843_);
if (v___x_855_ == 0)
{
uint8_t v___x_856_; 
lean_inc(v_a_843_);
v___x_856_ = l_Lean_Exception_isRuntime(v_a_843_);
v___y_848_ = v___x_856_;
goto v___jp_847_;
}
else
{
v___y_848_ = v___x_855_;
goto v___jp_847_;
}
v___jp_847_:
{
if (v___y_848_ == 0)
{
lean_object* v___x_850_; 
lean_dec(v_a_843_);
if (v_isShared_846_ == 0)
{
lean_ctor_set_tag(v___x_845_, 0);
lean_ctor_set(v___x_845_, 0, v___x_743_);
v___x_850_ = v___x_845_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_743_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
else
{
lean_object* v___x_853_; 
if (v_isShared_846_ == 0)
{
v___x_853_ = v___x_845_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_843_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec(v_head_736_);
lean_dec_ref(v_arg_721_);
lean_dec_ref(v_arg_720_);
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_dec_ref_known(v_p_694_, 2);
lean_del_object(v___x_692_);
lean_dec(v_arg_676_);
lean_dec_ref(v_P_674_);
v_a_858_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_739_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_739_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
else
{
lean_dec_ref(v_arg_721_);
lean_dec_ref(v_arg_720_);
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_dec_ref_known(v_p_694_, 2);
lean_del_object(v___x_692_);
lean_dec(v_arg_676_);
lean_dec_ref(v_P_674_);
goto v___jp_686_;
}
}
else
{
lean_dec_ref(v_arg_721_);
lean_dec_ref(v_arg_720_);
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_dec_ref_known(v_p_694_, 2);
lean_del_object(v___x_692_);
lean_dec(v_arg_676_);
lean_dec_ref(v_P_674_);
goto v___jp_686_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_dec_ref_known(v_p_694_, 2);
lean_del_object(v___x_692_);
lean_dec(v_arg_676_);
lean_dec_ref(v_P_674_);
goto v___jp_686_;
}
}
else
{
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_dec_ref_known(v_p_694_, 2);
lean_del_object(v___x_692_);
lean_dec(v_arg_676_);
lean_dec_ref(v_P_674_);
goto v___jp_686_;
}
}
else
{
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_dec_ref_known(v_p_694_, 2);
lean_del_object(v___x_692_);
lean_dec(v_arg_676_);
lean_dec_ref(v_P_674_);
goto v___jp_686_;
}
}
else
{
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_dec_ref_known(v_p_694_, 2);
lean_del_object(v___x_692_);
lean_dec(v_arg_676_);
lean_dec_ref(v_P_674_);
goto v___jp_686_;
}
}
else
{
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_dec_ref_known(v_p_694_, 2);
lean_del_object(v___x_692_);
lean_dec(v_arg_676_);
lean_dec_ref(v_P_674_);
goto v___jp_686_;
}
}
else
{
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_dec_ref_known(v_p_694_, 2);
lean_del_object(v___x_692_);
lean_dec(v_arg_676_);
lean_dec_ref(v_P_674_);
goto v___jp_686_;
}
}
else
{
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_dec_ref_known(v_p_694_, 2);
lean_del_object(v___x_692_);
lean_dec(v_arg_676_);
lean_dec_ref(v_P_674_);
goto v___jp_686_;
}
}
else
{
lean_dec_ref(v_arg_701_);
lean_del_object(v___x_698_);
lean_dec(v_uniq_696_);
lean_dec(v_name_695_);
lean_dec_ref_known(v_p_694_, 2);
lean_del_object(v___x_692_);
lean_dec(v_arg_676_);
lean_dec_ref(v_P_674_);
goto v___jp_686_;
}
v___jp_702_:
{
lean_object* v___x_705_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 2, v_arg_701_);
v___x_705_ = v___x_698_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_name_695_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_uniq_696_);
lean_ctor_set(v_reuseFailAlloc_712_, 2, v_arg_701_);
v___x_705_ = v_reuseFailAlloc_712_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_706_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_705_);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v___y_703_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_707_);
v___x_709_ = v___x_692_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_711_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_710_; 
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_694_);
lean_del_object(v___x_692_);
lean_dec(v_val_690_);
lean_dec(v_arg_676_);
lean_dec_ref(v_P_674_);
goto v___jp_686_;
}
}
}
else
{
lean_object* v___x_869_; lean_object* v___x_870_; 
lean_dec(v___x_689_);
lean_dec(v_arg_676_);
lean_dec_ref(v_P_674_);
v___x_869_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18);
v___x_870_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(v___x_869_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
return v___x_870_;
}
v___jp_686_:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_box(0);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_0interp(lean_interpreter_value* stack)
{
lean_object* v_P_674_ = stack[0].m_obj;
lean_object* v_QR_675_ = stack[1].m_obj;
lean_object* v_arg_676_ = stack[2].m_obj;
lean_object* v_a_677_ = stack[3].m_obj;
lean_object* v_a_678_ = stack[4].m_obj;
lean_object* v_a_679_ = stack[5].m_obj;
lean_object* v_a_680_ = stack[6].m_obj;
lean_object* v_a_681_ = stack[7].m_obj;
lean_object* v_a_682_ = stack[8].m_obj;
lean_object* v_a_683_ = stack[9].m_obj;
lean_object* v_a_684_ = stack[10].m_obj;
lean_object* v_res_871_;
v_res_871_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(v_P_674_, v_QR_675_, v_arg_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
stack->m_obj
 = v_res_871_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___boxed(lean_object* v_P_872_, lean_object* v_QR_873_, lean_object* v_arg_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(v_P_872_, v_QR_873_, v_arg_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
return v_res_884_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__2));
v___x_895_ = l_Lean_stringToMessageData(v___x_894_);
return v___x_895_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_898_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__5));
v___x_899_ = lean_unsigned_to_nat(36u);
v___x_900_ = lean_unsigned_to_nat(73u);
v___x_901_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__4));
v___x_902_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15));
v___x_903_ = l_mkPanicMessageWithDecl(v___x_902_, v___x_901_, v___x_900_, v___x_899_, v___x_898_);
return v___x_903_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(lean_object* v_P_904_, lean_object* v_00_u03a8_905_, lean_object* v_arg_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_00_u03a8_905_);
if (lean_obj_tag(v___x_919_) == 1)
{
lean_object* v_val_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_1055_; 
v_val_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_1055_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_val_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_1055_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v_p_924_; 
v_p_924_ = lean_ctor_get(v_val_920_, 2);
lean_inc_ref(v_p_924_);
if (lean_obj_tag(v_p_924_) == 5)
{
lean_object* v_fn_925_; 
v_fn_925_ = lean_ctor_get(v_p_924_, 0);
if (lean_obj_tag(v_fn_925_) == 5)
{
lean_object* v_fn_926_; 
v_fn_926_ = lean_ctor_get(v_fn_925_, 0);
if (lean_obj_tag(v_fn_926_) == 5)
{
lean_object* v_fn_927_; 
v_fn_927_ = lean_ctor_get(v_fn_926_, 0);
if (lean_obj_tag(v_fn_927_) == 4)
{
lean_object* v_declName_928_; 
v_declName_928_ = lean_ctor_get(v_fn_927_, 0);
if (lean_obj_tag(v_declName_928_) == 1)
{
lean_object* v_pre_929_; 
v_pre_929_ = lean_ctor_get(v_declName_928_, 0);
if (lean_obj_tag(v_pre_929_) == 1)
{
lean_object* v_pre_930_; 
v_pre_930_ = lean_ctor_get(v_pre_929_, 0);
if (lean_obj_tag(v_pre_930_) == 1)
{
lean_object* v_pre_931_; 
v_pre_931_ = lean_ctor_get(v_pre_930_, 0);
if (lean_obj_tag(v_pre_931_) == 1)
{
lean_object* v_pre_932_; 
v_pre_932_ = lean_ctor_get(v_pre_931_, 0);
if (lean_obj_tag(v_pre_932_) == 0)
{
lean_object* v_name_933_; lean_object* v_uniq_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_1053_; 
v_name_933_ = lean_ctor_get(v_val_920_, 0);
v_uniq_934_ = lean_ctor_get(v_val_920_, 1);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_val_920_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; 
v_unused_1054_ = lean_ctor_get(v_val_920_, 2);
lean_dec(v_unused_1054_);
v___x_936_ = v_val_920_;
v_isShared_937_ = v_isSharedCheck_1053_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_uniq_934_);
lean_inc(v_name_933_);
lean_dec(v_val_920_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_1053_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v_arg_938_; lean_object* v_arg_939_; lean_object* v_arg_940_; lean_object* v_us_941_; lean_object* v_str_942_; lean_object* v_str_943_; lean_object* v_str_944_; lean_object* v_str_945_; lean_object* v___x_946_; uint8_t v___x_947_; 
v_arg_938_ = lean_ctor_get(v_p_924_, 1);
v_arg_939_ = lean_ctor_get(v_fn_925_, 1);
lean_inc_ref(v_arg_939_);
v_arg_940_ = lean_ctor_get(v_fn_926_, 1);
v_us_941_ = lean_ctor_get(v_fn_927_, 1);
v_str_942_ = lean_ctor_get(v_declName_928_, 1);
v_str_943_ = lean_ctor_get(v_pre_929_, 1);
v_str_944_ = lean_ctor_get(v_pre_930_, 1);
v_str_945_ = lean_ctor_get(v_pre_931_, 1);
v___x_946_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_947_ = lean_string_dec_eq(v_str_945_, v___x_946_);
if (v___x_947_ == 0)
{
lean_dec_ref(v_arg_939_);
lean_del_object(v___x_936_);
lean_dec(v_uniq_934_);
lean_dec(v_name_933_);
lean_dec_ref_known(v_p_924_, 2);
lean_del_object(v___x_922_);
lean_dec(v_arg_906_);
lean_dec_ref(v_P_904_);
goto v___jp_916_;
}
else
{
lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_948_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_949_ = lean_string_dec_eq(v_str_944_, v___x_948_);
if (v___x_949_ == 0)
{
lean_dec_ref(v_arg_939_);
lean_del_object(v___x_936_);
lean_dec(v_uniq_934_);
lean_dec(v_name_933_);
lean_dec_ref_known(v_p_924_, 2);
lean_del_object(v___x_922_);
lean_dec(v_arg_906_);
lean_dec_ref(v_P_904_);
goto v___jp_916_;
}
else
{
lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_950_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_951_ = lean_string_dec_eq(v_str_943_, v___x_950_);
if (v___x_951_ == 0)
{
lean_dec_ref(v_arg_939_);
lean_del_object(v___x_936_);
lean_dec(v_uniq_934_);
lean_dec(v_name_933_);
lean_dec_ref_known(v_p_924_, 2);
lean_del_object(v___x_922_);
lean_dec(v_arg_906_);
lean_dec_ref(v_P_904_);
goto v___jp_916_;
}
else
{
lean_object* v___x_952_; uint8_t v___x_953_; 
v___x_952_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__0));
v___x_953_ = lean_string_dec_eq(v_str_942_, v___x_952_);
if (v___x_953_ == 0)
{
lean_dec_ref(v_arg_939_);
lean_del_object(v___x_936_);
lean_dec(v_uniq_934_);
lean_dec(v_name_933_);
lean_dec_ref_known(v_p_924_, 2);
lean_del_object(v___x_922_);
lean_dec(v_arg_906_);
lean_dec_ref(v_P_904_);
goto v___jp_916_;
}
else
{
if (lean_obj_tag(v_us_941_) == 1)
{
lean_object* v_tail_954_; 
v_tail_954_ = lean_ctor_get(v_us_941_, 1);
lean_inc(v_tail_954_);
if (lean_obj_tag(v_tail_954_) == 1)
{
lean_object* v_tail_955_; 
v_tail_955_ = lean_ctor_get(v_tail_954_, 1);
if (lean_obj_tag(v_tail_955_) == 0)
{
lean_object* v_head_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_1051_; 
v_head_956_ = lean_ctor_get(v_tail_954_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_tail_954_);
if (v_isSharedCheck_1051_ == 0)
{
lean_object* v_unused_1052_; 
v_unused_1052_ = lean_ctor_get(v_tail_954_, 1);
lean_dec(v_unused_1052_);
v___x_958_ = v_tail_954_;
v_isShared_959_ = v_isSharedCheck_1051_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_head_956_);
lean_dec(v_tail_954_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_1051_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
lean_inc_ref(v_arg_940_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v_arg_940_);
v___x_961_ = v___x_922_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_arg_940_);
v___x_961_ = v_reuseFailAlloc_1050_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2));
v___x_963_ = lean_box(0);
v___x_964_ = l_Lean_Elab_Tactic_elabTermWithHoles(v_arg_906_, v___x_961_, v___x_962_, v___x_953_, v___x_963_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v_fst_966_; lean_object* v_snd_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_1034_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_964_, 1);
v_fst_966_ = lean_ctor_get(v_a_965_, 0);
v_snd_967_ = lean_ctor_get(v_a_965_, 1);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_a_965_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_969_ = v_a_965_;
v_isShared_970_ = v_isSharedCheck_1034_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_snd_967_);
lean_inc(v_fst_966_);
lean_dec(v_a_965_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_1034_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_Elab_Tactic_pushGoals___redArg(v_snd_967_, v_a_908_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_1024_; 
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; 
v_unused_1025_ = lean_ctor_get(v___x_971_, 0);
lean_dec(v_unused_1025_);
v___x_973_ = v___x_971_;
v_isShared_974_ = v_isSharedCheck_1024_;
goto v_resetjp_972_;
}
else
{
lean_dec(v___x_971_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_1024_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v_toCold_975_; lean_object* v_options_976_; lean_object* v_inheritedTraceOptions_977_; uint8_t v_hasTrace_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_toCold_975_ = lean_ctor_get(v_a_913_, 0);
v_options_976_ = lean_ctor_get(v_toCold_975_, 2);
v_inheritedTraceOptions_977_ = lean_ctor_get(v_toCold_975_, 11);
v_hasTrace_978_ = lean_ctor_get_uint8(v_options_976_, sizeof(void*)*1);
v___x_979_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1));
lean_inc_ref(v_us_941_);
v___x_980_ = l_Lean_mkConst(v___x_979_, v_us_941_);
lean_inc_n(v_fst_966_, 2);
lean_inc_ref(v_P_904_);
lean_inc_ref_n(v_arg_938_, 2);
lean_inc_ref(v_arg_939_);
lean_inc_ref(v_arg_940_);
v___x_981_ = l_Lean_mkApp5(v___x_980_, v_arg_940_, v_arg_939_, v_arg_938_, v_P_904_, v_fst_966_);
v___x_982_ = lean_unsigned_to_nat(1u);
v___x_983_ = lean_mk_empty_array_with_capacity(v___x_982_);
v___x_984_ = lean_array_push(v___x_983_, v_fst_966_);
v___x_985_ = l_Lean_Expr_beta(v_arg_938_, v___x_984_);
if (v_hasTrace_978_ == 0)
{
lean_dec(v_fst_966_);
lean_del_object(v___x_958_);
lean_dec(v_head_956_);
lean_dec_ref(v_arg_939_);
lean_dec_ref_known(v_p_924_, 2);
lean_dec_ref(v_P_904_);
goto v___jp_986_;
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_998_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_999_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11);
v___x_1000_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_977_, v_options_976_, v___x_999_);
if (v___x_1000_ == 0)
{
lean_dec(v_fst_966_);
lean_del_object(v___x_958_);
lean_dec(v_head_956_);
lean_dec_ref(v_arg_939_);
lean_dec_ref_known(v_p_924_, 2);
lean_dec_ref(v_P_904_);
goto v___jp_986_;
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_1001_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3);
v___x_1002_ = l_Lean_MessageData_ofExpr(v_p_924_);
if (v_isShared_959_ == 0)
{
lean_ctor_set_tag(v___x_958_, 7);
lean_ctor_set(v___x_958_, 1, v___x_1002_);
lean_ctor_set(v___x_958_, 0, v___x_1001_);
v___x_1004_ = v___x_958_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1005_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_1006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1004_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = l_Lean_MessageData_ofExpr(v_fst_966_);
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
lean_inc_ref(v___x_985_);
v___x_1011_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_head_956_, v_arg_939_, v_P_904_, v___x_985_);
v___x_1012_ = l_Lean_MessageData_ofExpr(v___x_1011_);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1010_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v___x_998_, v___x_1013_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_dec_ref_known(v___x_1014_, 1);
goto v___jp_986_;
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec_ref(v___x_985_);
lean_dec_ref(v___x_981_);
lean_del_object(v___x_973_);
lean_del_object(v___x_969_);
lean_del_object(v___x_936_);
lean_dec(v_uniq_934_);
lean_dec(v_name_933_);
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1014_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
}
v___jp_986_:
{
lean_object* v___x_988_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 2, v___x_985_);
v___x_988_ = v___x_936_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_name_933_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_uniq_934_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v___x_985_);
v___x_988_ = v_reuseFailAlloc_997_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_989_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_988_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v___x_981_);
lean_ctor_set(v___x_969_, 0, v___x_989_);
v___x_991_ = v___x_969_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v___x_981_);
v___x_991_ = v_reuseFailAlloc_996_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_992_);
v___x_994_ = v___x_973_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_del_object(v___x_969_);
lean_dec(v_fst_966_);
lean_del_object(v___x_958_);
lean_dec(v_head_956_);
lean_dec_ref(v_arg_939_);
lean_del_object(v___x_936_);
lean_dec(v_uniq_934_);
lean_dec(v_name_933_);
lean_dec_ref_known(v_p_924_, 2);
lean_dec_ref(v_P_904_);
v_a_1026_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_971_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_971_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1049_; 
lean_del_object(v___x_958_);
lean_dec(v_head_956_);
lean_dec_ref(v_arg_939_);
lean_del_object(v___x_936_);
lean_dec(v_uniq_934_);
lean_dec(v_name_933_);
lean_dec_ref_known(v_p_924_, 2);
lean_dec_ref(v_P_904_);
v_a_1035_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1037_ = v___x_964_;
v_isShared_1038_ = v_isSharedCheck_1049_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_964_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1049_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
uint8_t v___y_1040_; uint8_t v___x_1047_; 
v___x_1047_ = l_Lean_Exception_isInterrupt(v_a_1035_);
if (v___x_1047_ == 0)
{
uint8_t v___x_1048_; 
lean_inc(v_a_1035_);
v___x_1048_ = l_Lean_Exception_isRuntime(v_a_1035_);
v___y_1040_ = v___x_1048_;
goto v___jp_1039_;
}
else
{
v___y_1040_ = v___x_1047_;
goto v___jp_1039_;
}
v___jp_1039_:
{
if (v___y_1040_ == 0)
{
lean_object* v___x_1042_; 
lean_dec(v_a_1035_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 0);
lean_ctor_set(v___x_1037_, 0, v___x_963_);
v___x_1042_ = v___x_1037_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_963_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
else
{
lean_object* v___x_1045_; 
if (v_isShared_1038_ == 0)
{
v___x_1045_ = v___x_1037_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1035_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
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
lean_dec_ref_known(v_tail_954_, 2);
lean_dec_ref(v_arg_939_);
lean_del_object(v___x_936_);
lean_dec(v_uniq_934_);
lean_dec(v_name_933_);
lean_dec_ref_known(v_p_924_, 2);
lean_del_object(v___x_922_);
lean_dec(v_arg_906_);
lean_dec_ref(v_P_904_);
goto v___jp_916_;
}
}
else
{
lean_dec(v_tail_954_);
lean_dec_ref(v_arg_939_);
lean_del_object(v___x_936_);
lean_dec(v_uniq_934_);
lean_dec(v_name_933_);
lean_dec_ref_known(v_p_924_, 2);
lean_del_object(v___x_922_);
lean_dec(v_arg_906_);
lean_dec_ref(v_P_904_);
goto v___jp_916_;
}
}
else
{
lean_dec_ref(v_arg_939_);
lean_del_object(v___x_936_);
lean_dec(v_uniq_934_);
lean_dec(v_name_933_);
lean_dec_ref_known(v_p_924_, 2);
lean_del_object(v___x_922_);
lean_dec(v_arg_906_);
lean_dec_ref(v_P_904_);
goto v___jp_916_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_p_924_, 2);
lean_del_object(v___x_922_);
lean_dec(v_val_920_);
lean_dec(v_arg_906_);
lean_dec_ref(v_P_904_);
goto v___jp_916_;
}
}
else
{
lean_dec_ref_known(v_p_924_, 2);
lean_del_object(v___x_922_);
lean_dec(v_val_920_);
lean_dec(v_arg_906_);
lean_dec_ref(v_P_904_);
goto v___jp_916_;
}
}
else
{
lean_dec_ref_known(v_p_924_, 2);
lean_del_object(v___x_922_);
lean_dec(v_val_920_);
lean_dec(v_arg_906_);
lean_dec_ref(v_P_904_);
goto v___jp_916_;
}
}
else
{
lean_dec_ref_known(v_p_924_, 2);
lean_del_object(v___x_922_);
lean_dec(v_val_920_);
lean_dec(v_arg_906_);
lean_dec_ref(v_P_904_);
goto v___jp_916_;
}
}
else
{
lean_dec_ref_known(v_p_924_, 2);
lean_del_object(v___x_922_);
lean_dec(v_val_920_);
lean_dec(v_arg_906_);
lean_dec_ref(v_P_904_);
goto v___jp_916_;
}
}
else
{
lean_dec_ref_known(v_p_924_, 2);
lean_del_object(v___x_922_);
lean_dec(v_val_920_);
lean_dec(v_arg_906_);
lean_dec_ref(v_P_904_);
goto v___jp_916_;
}
}
else
{
lean_dec_ref_known(v_p_924_, 2);
lean_del_object(v___x_922_);
lean_dec(v_val_920_);
lean_dec(v_arg_906_);
lean_dec_ref(v_P_904_);
goto v___jp_916_;
}
}
else
{
lean_dec_ref_known(v_p_924_, 2);
lean_del_object(v___x_922_);
lean_dec(v_val_920_);
lean_dec(v_arg_906_);
lean_dec_ref(v_P_904_);
goto v___jp_916_;
}
}
else
{
lean_dec_ref(v_p_924_);
lean_del_object(v___x_922_);
lean_dec(v_val_920_);
lean_dec(v_arg_906_);
lean_dec_ref(v_P_904_);
goto v___jp_916_;
}
}
}
else
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
lean_dec(v___x_919_);
lean_dec(v_arg_906_);
lean_dec_ref(v_P_904_);
v___x_1056_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6);
v___x_1057_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(v___x_1056_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
return v___x_1057_;
}
v___jp_916_:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = lean_box(0);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall_0interp(lean_interpreter_value* stack)
{
lean_object* v_P_904_ = stack[0].m_obj;
lean_object* v_00_u03a8_905_ = stack[1].m_obj;
lean_object* v_arg_906_ = stack[2].m_obj;
lean_object* v_a_907_ = stack[3].m_obj;
lean_object* v_a_908_ = stack[4].m_obj;
lean_object* v_a_909_ = stack[5].m_obj;
lean_object* v_a_910_ = stack[6].m_obj;
lean_object* v_a_911_ = stack[7].m_obj;
lean_object* v_a_912_ = stack[8].m_obj;
lean_object* v_a_913_ = stack[9].m_obj;
lean_object* v_a_914_ = stack[10].m_obj;
lean_object* v_res_1058_;
v_res_1058_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(v_P_904_, v_00_u03a8_905_, v_arg_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
stack->m_obj
 = v_res_1058_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___boxed(lean_object* v_P_1059_, lean_object* v_00_u03a8_1060_, lean_object* v_arg_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(v_P_1059_, v_00_u03a8_1060_, v_arg_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
return v_res_1071_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1072_ = lean_box(0);
v___x_1073_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v___x_1072_);
return v___x_1074_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg(){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0);
v___x_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1078_;
v_res_1078_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
stack->m_obj
 = v_res_1078_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___boxed(lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v_res_1080_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0(lean_object* v_00_u03b1_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_1091_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1082_ = stack[1].m_obj;
lean_object* v___y_1083_ = stack[2].m_obj;
lean_object* v___y_1084_ = stack[3].m_obj;
lean_object* v___y_1085_ = stack[4].m_obj;
lean_object* v___y_1086_ = stack[5].m_obj;
lean_object* v___y_1087_ = stack[6].m_obj;
lean_object* v___y_1088_ = stack[7].m_obj;
lean_object* v___y_1089_ = stack[8].m_obj;
lean_object* v_res_1092_;
v_res_1092_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0(lean_box(0), v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
stack->m_obj
 = v_res_1092_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___boxed(lean_object* v_00_u03b1_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0(v_00_u03b1_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1103_;
}
}
lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(lean_object* v_msg_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___f_1115_; lean_object* v___x_5045__overap_1116_; lean_object* v___x_1117_; 
v___f_1115_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3___closed__0));
v___x_5045__overap_1116_ = lean_panic_fn_borrowed(v___f_1115_, v_msg_1105_);
lean_inc(v___y_1113_);
lean_inc_ref(v___y_1112_);
lean_inc(v___y_1111_);
lean_inc_ref(v___y_1110_);
lean_inc(v___y_1109_);
lean_inc_ref(v___y_1108_);
lean_inc(v___y_1107_);
lean_inc_ref(v___y_1106_);
v___x_1117_ = lean_apply_9(v___x_5045__overap_1116_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, lean_box(0));
return v___x_1117_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1105_ = stack[0].m_obj;
lean_object* v___y_1106_ = stack[1].m_obj;
lean_object* v___y_1107_ = stack[2].m_obj;
lean_object* v___y_1108_ = stack[3].m_obj;
lean_object* v___y_1109_ = stack[4].m_obj;
lean_object* v___y_1110_ = stack[5].m_obj;
lean_object* v___y_1111_ = stack[6].m_obj;
lean_object* v___y_1112_ = stack[7].m_obj;
lean_object* v___y_1113_ = stack[8].m_obj;
lean_object* v_res_1118_;
v_res_1118_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(v_msg_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
stack->m_obj
 = v_res_1118_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3___boxed(lean_object* v_msg_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(v_msg_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
return v_res_1129_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0(lean_object* v_x_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; 
lean_inc(v___y_1134_);
lean_inc_ref(v___y_1133_);
lean_inc(v___y_1132_);
lean_inc_ref(v___y_1131_);
v___x_1140_ = lean_apply_9(v_x_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, lean_box(0));
return v___x_1140_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1130_ = stack[0].m_obj;
lean_object* v___y_1131_ = stack[1].m_obj;
lean_object* v___y_1132_ = stack[2].m_obj;
lean_object* v___y_1133_ = stack[3].m_obj;
lean_object* v___y_1134_ = stack[4].m_obj;
lean_object* v___y_1135_ = stack[5].m_obj;
lean_object* v___y_1136_ = stack[6].m_obj;
lean_object* v___y_1137_ = stack[7].m_obj;
lean_object* v___y_1138_ = stack[8].m_obj;
lean_object* v_res_1141_;
v_res_1141_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0(v_x_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
stack->m_obj
 = v_res_1141_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0___boxed(lean_object* v_x_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0(v_x_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
return v_res_1152_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(lean_object* v_mvarId_1153_, lean_object* v_x_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___f_1164_; lean_object* v___x_1165_; 
lean_inc(v___y_1158_);
lean_inc_ref(v___y_1157_);
lean_inc(v___y_1156_);
lean_inc_ref(v___y_1155_);
v___f_1164_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1164_, 0, v_x_1154_);
lean_closure_set(v___f_1164_, 1, v___y_1155_);
lean_closure_set(v___f_1164_, 2, v___y_1156_);
lean_closure_set(v___f_1164_, 3, v___y_1157_);
lean_closure_set(v___f_1164_, 4, v___y_1158_);
v___x_1165_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1153_, v___f_1164_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
if (lean_obj_tag(v___x_1165_) == 0)
{
return v___x_1165_;
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1165_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1153_ = stack[0].m_obj;
lean_object* v_x_1154_ = stack[1].m_obj;
lean_object* v___y_1155_ = stack[2].m_obj;
lean_object* v___y_1156_ = stack[3].m_obj;
lean_object* v___y_1157_ = stack[4].m_obj;
lean_object* v___y_1158_ = stack[5].m_obj;
lean_object* v___y_1159_ = stack[6].m_obj;
lean_object* v___y_1160_ = stack[7].m_obj;
lean_object* v___y_1161_ = stack[8].m_obj;
lean_object* v___y_1162_ = stack[9].m_obj;
lean_object* v_res_1174_;
v_res_1174_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_mvarId_1153_, v_x_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
stack->m_obj
 = v_res_1174_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___boxed(lean_object* v_mvarId_1175_, lean_object* v_x_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_mvarId_1175_, v_x_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
return v_res_1186_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4(lean_object* v_00_u03b1_1187_, lean_object* v_mvarId_1188_, lean_object* v_x_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_mvarId_1188_, v_x_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
return v___x_1199_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1188_ = stack[1].m_obj;
lean_object* v_x_1189_ = stack[2].m_obj;
lean_object* v___y_1190_ = stack[3].m_obj;
lean_object* v___y_1191_ = stack[4].m_obj;
lean_object* v___y_1192_ = stack[5].m_obj;
lean_object* v___y_1193_ = stack[6].m_obj;
lean_object* v___y_1194_ = stack[7].m_obj;
lean_object* v___y_1195_ = stack[8].m_obj;
lean_object* v___y_1196_ = stack[9].m_obj;
lean_object* v___y_1197_ = stack[10].m_obj;
lean_object* v_res_1200_;
v_res_1200_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4(lean_box(0), v_mvarId_1188_, v_x_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
stack->m_obj
 = v_res_1200_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___boxed(lean_object* v_00_u03b1_1201_, lean_object* v_mvarId_1202_, lean_object* v_x_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4(v_00_u03b1_1201_, v_mvarId_1202_, v_x_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0(lean_object* v___x_1216_, lean_object* v___x_1217_, lean_object* v___x_1218_, lean_object* v___x_1219_, lean_object* v___x_1220_, lean_object* v___x_1221_, lean_object* v___x_1222_, lean_object* v_fst_1223_, lean_object* v_fst_1224_, lean_object* v___x_1225_, lean_object* v_snd_1226_, lean_object* v_snd_1227_, lean_object* v_hgoal_1228_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1229_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__0));
v___x_1230_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__1));
v___x_1231_ = l_Lean_Name_mkStr5(v___x_1216_, v___x_1217_, v___x_1218_, v___x_1229_, v___x_1230_);
v___x_1232_ = l_Lean_mkConst(v___x_1231_, v___x_1219_);
lean_inc_ref(v___x_1222_);
lean_inc_ref_n(v___x_1221_, 2);
lean_inc(v___x_1220_);
v___x_1233_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v___x_1220_, v___x_1221_, v___x_1222_, v_fst_1223_);
v___x_1234_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v___x_1220_, v___x_1221_, v___x_1222_, v_fst_1224_);
v___x_1235_ = l_Lean_mkApp6(v___x_1232_, v___x_1221_, v___x_1233_, v___x_1234_, v___x_1225_, v_snd_1226_, v_hgoal_1228_);
v___x_1236_ = lean_apply_1(v_snd_1227_, v___x_1235_);
return v___x_1236_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__0));
v___x_1239_ = l_Lean_stringToMessageData(v___x_1238_);
return v___x_1239_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1(lean_object* v___x_1240_, lean_object* v___x_1241_, lean_object* v___x_1242_, lean_object* v___x_1243_, lean_object* v___x_1244_, lean_object* v_as_1245_, size_t v_sz_1246_, size_t v_i_1247_, lean_object* v_b_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_a_1259_; uint8_t v___x_1263_; 
v___x_1263_ = lean_usize_dec_lt(v_i_1247_, v_sz_1246_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; 
lean_dec_ref(v___x_1244_);
lean_dec_ref(v___x_1243_);
lean_dec_ref(v___x_1242_);
lean_dec(v___x_1241_);
lean_dec(v___x_1240_);
v___x_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1264_, 0, v_b_1248_);
return v___x_1264_;
}
else
{
lean_object* v_fst_1265_; lean_object* v_snd_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1320_; 
v_fst_1265_ = lean_ctor_get(v_b_1248_, 0);
v_snd_1266_ = lean_ctor_get(v_b_1248_, 1);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_b_1248_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1268_ = v_b_1248_;
v_isShared_1269_ = v_isSharedCheck_1320_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_snd_1266_);
lean_inc(v_fst_1265_);
lean_dec(v_b_1248_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1320_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v_a_1273_; lean_object* v___y_1275_; lean_object* v___x_1315_; 
v___x_1270_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_1271_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1272_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v_a_1273_ = lean_array_uget_borrowed(v_as_1245_, v_i_1247_);
lean_inc(v_a_1273_);
lean_inc(v_fst_1265_);
lean_inc_ref(v___x_1243_);
v___x_1315_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(v___x_1243_, v_fst_1265_, v_a_1273_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
if (lean_obj_tag(v_a_1316_) == 0)
{
lean_object* v___x_1317_; 
lean_dec_ref_known(v___x_1315_, 1);
lean_inc(v_a_1273_);
lean_inc(v_fst_1265_);
lean_inc_ref(v___x_1243_);
v___x_1317_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(v___x_1243_, v_fst_1265_, v_a_1273_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
if (lean_obj_tag(v_a_1318_) == 0)
{
lean_object* v___x_1319_; 
lean_dec_ref_known(v___x_1317_, 1);
lean_inc(v_a_1273_);
lean_inc(v_fst_1265_);
lean_inc_ref(v___x_1243_);
v___x_1319_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(v___x_1243_, v_fst_1265_, v_a_1273_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
v___y_1275_ = v___x_1319_;
goto v___jp_1274_;
}
else
{
v___y_1275_ = v___x_1317_;
goto v___jp_1274_;
}
}
else
{
v___y_1275_ = v___x_1317_;
goto v___jp_1274_;
}
}
else
{
v___y_1275_ = v___x_1315_;
goto v___jp_1274_;
}
}
else
{
v___y_1275_ = v___x_1315_;
goto v___jp_1274_;
}
v___jp_1274_:
{
if (lean_obj_tag(v___y_1275_) == 0)
{
lean_object* v_a_1276_; 
v_a_1276_ = lean_ctor_get(v___y_1275_, 0);
lean_inc(v_a_1276_);
lean_dec_ref_known(v___y_1275_, 1);
if (lean_obj_tag(v_a_1276_) == 0)
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1277_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1);
lean_inc(v_fst_1265_);
v___x_1278_ = l_Lean_MessageData_ofExpr(v_fst_1265_);
v___x_1279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_1281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
lean_inc(v_a_1273_);
v___x_1282_ = l_Lean_MessageData_ofSyntax(v_a_1273_);
v___x_1283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1281_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_1283_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v___x_1286_; 
lean_dec_ref_known(v___x_1284_, 1);
if (v_isShared_1269_ == 0)
{
v___x_1286_ = v___x_1268_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_fst_1265_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_snd_1266_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
v_a_1259_ = v___x_1286_;
goto v___jp_1258_;
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_del_object(v___x_1268_);
lean_dec(v_snd_1266_);
lean_dec(v_fst_1265_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v___x_1243_);
lean_dec_ref(v___x_1242_);
lean_dec(v___x_1241_);
lean_dec(v___x_1240_);
v_a_1288_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1284_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1284_);
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
else
{
lean_object* v_val_1296_; lean_object* v_fst_1297_; lean_object* v_snd_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1306_; 
lean_del_object(v___x_1268_);
v_val_1296_ = lean_ctor_get(v_a_1276_, 0);
lean_inc(v_val_1296_);
lean_dec_ref_known(v_a_1276_, 1);
v_fst_1297_ = lean_ctor_get(v_val_1296_, 0);
v_snd_1298_ = lean_ctor_get(v_val_1296_, 1);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_val_1296_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1300_ = v_val_1296_;
v_isShared_1301_ = v_isSharedCheck_1306_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_snd_1298_);
lean_inc(v_fst_1297_);
lean_dec(v_val_1296_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1306_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___f_1302_; lean_object* v___x_1304_; 
lean_inc_ref(v___x_1244_);
lean_inc(v_fst_1297_);
lean_inc_ref(v___x_1243_);
lean_inc_ref(v___x_1242_);
lean_inc(v___x_1241_);
lean_inc(v___x_1240_);
v___f_1302_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0), 13, 12);
lean_closure_set(v___f_1302_, 0, v___x_1270_);
lean_closure_set(v___f_1302_, 1, v___x_1271_);
lean_closure_set(v___f_1302_, 2, v___x_1272_);
lean_closure_set(v___f_1302_, 3, v___x_1240_);
lean_closure_set(v___f_1302_, 4, v___x_1241_);
lean_closure_set(v___f_1302_, 5, v___x_1242_);
lean_closure_set(v___f_1302_, 6, v___x_1243_);
lean_closure_set(v___f_1302_, 7, v_fst_1265_);
lean_closure_set(v___f_1302_, 8, v_fst_1297_);
lean_closure_set(v___f_1302_, 9, v___x_1244_);
lean_closure_set(v___f_1302_, 10, v_snd_1298_);
lean_closure_set(v___f_1302_, 11, v_snd_1266_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 1, v___f_1302_);
v___x_1304_ = v___x_1300_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_fst_1297_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___f_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
v_a_1259_ = v___x_1304_;
goto v___jp_1258_;
}
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_del_object(v___x_1268_);
lean_dec(v_snd_1266_);
lean_dec(v_fst_1265_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v___x_1243_);
lean_dec_ref(v___x_1242_);
lean_dec(v___x_1241_);
lean_dec(v___x_1240_);
v_a_1307_ = lean_ctor_get(v___y_1275_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___y_1275_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___y_1275_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___y_1275_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
}
v___jp_1258_:
{
size_t v___x_1260_; size_t v___x_1261_; 
v___x_1260_ = ((size_t)1ULL);
v___x_1261_ = lean_usize_add(v_i_1247_, v___x_1260_);
v_i_1247_ = v___x_1261_;
v_b_1248_ = v_a_1259_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1240_ = stack[0].m_obj;
lean_object* v___x_1241_ = stack[1].m_obj;
lean_object* v___x_1242_ = stack[2].m_obj;
lean_object* v___x_1243_ = stack[3].m_obj;
lean_object* v___x_1244_ = stack[4].m_obj;
lean_object* v_as_1245_ = stack[5].m_obj;
size_t v_sz_1246_ = stack[6].m_num;
size_t v_i_1247_ = stack[7].m_num;
lean_object* v_b_1248_ = stack[8].m_obj;
lean_object* v___y_1249_ = stack[9].m_obj;
lean_object* v___y_1250_ = stack[10].m_obj;
lean_object* v___y_1251_ = stack[11].m_obj;
lean_object* v___y_1252_ = stack[12].m_obj;
lean_object* v___y_1253_ = stack[13].m_obj;
lean_object* v___y_1254_ = stack[14].m_obj;
lean_object* v___y_1255_ = stack[15].m_obj;
lean_object* v___y_1256_ = stack[16].m_obj;
lean_object* v_res_1321_;
v_res_1321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1(v___x_1240_, v___x_1241_, v___x_1242_, v___x_1243_, v___x_1244_, v_as_1245_, v_sz_1246_, v_i_1247_, v_b_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
stack->m_obj
 = v_res_1321_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___boxed(lean_object** _args){
lean_object* v___x_1322_ = _args[0];
lean_object* v___x_1323_ = _args[1];
lean_object* v___x_1324_ = _args[2];
lean_object* v___x_1325_ = _args[3];
lean_object* v___x_1326_ = _args[4];
lean_object* v_as_1327_ = _args[5];
lean_object* v_sz_1328_ = _args[6];
lean_object* v_i_1329_ = _args[7];
lean_object* v_b_1330_ = _args[8];
lean_object* v___y_1331_ = _args[9];
lean_object* v___y_1332_ = _args[10];
lean_object* v___y_1333_ = _args[11];
lean_object* v___y_1334_ = _args[12];
lean_object* v___y_1335_ = _args[13];
lean_object* v___y_1336_ = _args[14];
lean_object* v___y_1337_ = _args[15];
lean_object* v___y_1338_ = _args[16];
lean_object* v___y_1339_ = _args[17];
_start:
{
size_t v_sz_boxed_1340_; size_t v_i_boxed_1341_; lean_object* v_res_1342_; 
v_sz_boxed_1340_ = lean_unbox_usize(v_sz_1328_);
lean_dec(v_sz_1328_);
v_i_boxed_1341_ = lean_unbox_usize(v_i_1329_);
lean_dec(v_i_1329_);
v_res_1342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1(v___x_1322_, v___x_1323_, v___x_1324_, v___x_1325_, v___x_1326_, v_as_1327_, v_sz_boxed_1340_, v_i_boxed_1341_, v_b_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec_ref(v_as_1327_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7___redArg(lean_object* v_x_1343_, lean_object* v_x_1344_, lean_object* v_x_1345_, lean_object* v_x_1346_){
_start:
{
lean_object* v_ks_1347_; lean_object* v_vs_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1372_; 
v_ks_1347_ = lean_ctor_get(v_x_1343_, 0);
v_vs_1348_ = lean_ctor_get(v_x_1343_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_x_1343_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1350_ = v_x_1343_;
v_isShared_1351_ = v_isSharedCheck_1372_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_vs_1348_);
lean_inc(v_ks_1347_);
lean_dec(v_x_1343_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1372_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; uint8_t v___x_1353_; 
v___x_1352_ = lean_array_get_size(v_ks_1347_);
v___x_1353_ = lean_nat_dec_lt(v_x_1344_, v___x_1352_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
lean_dec(v_x_1344_);
v___x_1354_ = lean_array_push(v_ks_1347_, v_x_1345_);
v___x_1355_ = lean_array_push(v_vs_1348_, v_x_1346_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 1, v___x_1355_);
lean_ctor_set(v___x_1350_, 0, v___x_1354_);
v___x_1357_ = v___x_1350_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
else
{
lean_object* v_k_x27_1359_; uint8_t v___x_1360_; 
v_k_x27_1359_ = lean_array_fget_borrowed(v_ks_1347_, v_x_1344_);
v___x_1360_ = l_Lean_instBEqMVarId_beq(v_x_1345_, v_k_x27_1359_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1362_; 
if (v_isShared_1351_ == 0)
{
v___x_1362_ = v___x_1350_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_ks_1347_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_vs_1348_);
v___x_1362_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = lean_unsigned_to_nat(1u);
v___x_1364_ = lean_nat_add(v_x_1344_, v___x_1363_);
lean_dec(v_x_1344_);
v_x_1343_ = v___x_1362_;
v_x_1344_ = v___x_1364_;
goto _start;
}
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1367_ = lean_array_fset(v_ks_1347_, v_x_1344_, v_x_1345_);
v___x_1368_ = lean_array_fset(v_vs_1348_, v_x_1344_, v_x_1346_);
lean_dec(v_x_1344_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 1, v___x_1368_);
lean_ctor_set(v___x_1350_, 0, v___x_1367_);
v___x_1370_ = v___x_1350_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6___redArg(lean_object* v_n_1373_, lean_object* v_k_1374_, lean_object* v_v_1375_){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_unsigned_to_nat(0u);
v___x_1377_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7___redArg(v_n_1373_, v___x_1376_, v_k_1374_, v_v_1375_);
return v___x_1377_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1378_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(lean_object* v_x_1379_, size_t v_x_1380_, size_t v_x_1381_, lean_object* v_x_1382_, lean_object* v_x_1383_){
_start:
{
if (lean_obj_tag(v_x_1379_) == 0)
{
lean_object* v_es_1384_; size_t v___x_1385_; size_t v___x_1386_; lean_object* v_j_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v_es_1384_ = lean_ctor_get(v_x_1379_, 0);
v___x_1385_ = ((size_t)31ULL);
v___x_1386_ = lean_usize_land(v_x_1380_, v___x_1385_);
v_j_1387_ = lean_usize_to_nat(v___x_1386_);
v___x_1388_ = lean_array_get_size(v_es_1384_);
v___x_1389_ = lean_nat_dec_lt(v_j_1387_, v___x_1388_);
if (v___x_1389_ == 0)
{
lean_dec(v_j_1387_);
lean_dec(v_x_1383_);
lean_dec(v_x_1382_);
return v_x_1379_;
}
else
{
lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1428_; 
lean_inc_ref(v_es_1384_);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_x_1379_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; 
v_unused_1429_ = lean_ctor_get(v_x_1379_, 0);
lean_dec(v_unused_1429_);
v___x_1391_ = v_x_1379_;
v_isShared_1392_ = v_isSharedCheck_1428_;
goto v_resetjp_1390_;
}
else
{
lean_dec(v_x_1379_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1428_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v_v_1393_; lean_object* v___x_1394_; lean_object* v_xs_x27_1395_; lean_object* v___y_1397_; 
v_v_1393_ = lean_array_fget(v_es_1384_, v_j_1387_);
v___x_1394_ = lean_box(0);
v_xs_x27_1395_ = lean_array_fset(v_es_1384_, v_j_1387_, v___x_1394_);
switch(lean_obj_tag(v_v_1393_))
{
case 0:
{
lean_object* v_key_1402_; lean_object* v_val_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1413_; 
v_key_1402_ = lean_ctor_get(v_v_1393_, 0);
v_val_1403_ = lean_ctor_get(v_v_1393_, 1);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_v_1393_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1405_ = v_v_1393_;
v_isShared_1406_ = v_isSharedCheck_1413_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_val_1403_);
lean_inc(v_key_1402_);
lean_dec(v_v_1393_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1413_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
uint8_t v___x_1407_; 
v___x_1407_ = l_Lean_instBEqMVarId_beq(v_x_1382_, v_key_1402_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
lean_del_object(v___x_1405_);
v___x_1408_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1402_, v_val_1403_, v_x_1382_, v_x_1383_);
v___x_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
v___y_1397_ = v___x_1409_;
goto v___jp_1396_;
}
else
{
lean_object* v___x_1411_; 
lean_dec(v_val_1403_);
lean_dec(v_key_1402_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 1, v_x_1383_);
lean_ctor_set(v___x_1405_, 0, v_x_1382_);
v___x_1411_ = v___x_1405_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_x_1382_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_x_1383_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
v___y_1397_ = v___x_1411_;
goto v___jp_1396_;
}
}
}
}
case 1:
{
lean_object* v_node_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1426_; 
v_node_1414_ = lean_ctor_get(v_v_1393_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_v_1393_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1416_ = v_v_1393_;
v_isShared_1417_ = v_isSharedCheck_1426_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_node_1414_);
lean_dec(v_v_1393_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1426_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
size_t v___x_1418_; size_t v___x_1419_; size_t v___x_1420_; size_t v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1418_ = ((size_t)5ULL);
v___x_1419_ = lean_usize_shift_right(v_x_1380_, v___x_1418_);
v___x_1420_ = ((size_t)1ULL);
v___x_1421_ = lean_usize_add(v_x_1381_, v___x_1420_);
v___x_1422_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_node_1414_, v___x_1419_, v___x_1421_, v_x_1382_, v_x_1383_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1422_);
v___x_1424_ = v___x_1416_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
v___y_1397_ = v___x_1424_;
goto v___jp_1396_;
}
}
}
default: 
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1427_, 0, v_x_1382_);
lean_ctor_set(v___x_1427_, 1, v_x_1383_);
v___y_1397_ = v___x_1427_;
goto v___jp_1396_;
}
}
v___jp_1396_:
{
lean_object* v___x_1398_; lean_object* v___x_1400_; 
v___x_1398_ = lean_array_fset(v_xs_x27_1395_, v_j_1387_, v___y_1397_);
lean_dec(v_j_1387_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1398_);
v___x_1400_ = v___x_1391_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
else
{
lean_object* v_ks_1430_; lean_object* v_vs_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1449_; 
v_ks_1430_ = lean_ctor_get(v_x_1379_, 0);
v_vs_1431_ = lean_ctor_get(v_x_1379_, 1);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_x_1379_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1433_ = v_x_1379_;
v_isShared_1434_ = v_isSharedCheck_1449_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_vs_1431_);
lean_inc(v_ks_1430_);
lean_dec(v_x_1379_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1449_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_ks_1430_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_vs_1431_);
v___x_1436_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v_newNode_1437_; size_t v___x_1438_; uint8_t v___x_1439_; 
v_newNode_1437_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6___redArg(v___x_1436_, v_x_1382_, v_x_1383_);
v___x_1438_ = ((size_t)7ULL);
v___x_1439_ = lean_usize_dec_le(v___x_1438_, v_x_1381_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v___x_1440_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1437_);
v___x_1441_ = lean_unsigned_to_nat(4u);
v___x_1442_ = lean_nat_dec_lt(v___x_1440_, v___x_1441_);
lean_dec(v___x_1440_);
if (v___x_1442_ == 0)
{
lean_object* v_ks_1443_; lean_object* v_vs_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v_ks_1443_ = lean_ctor_get(v_newNode_1437_, 0);
lean_inc_ref(v_ks_1443_);
v_vs_1444_ = lean_ctor_get(v_newNode_1437_, 1);
lean_inc_ref(v_vs_1444_);
lean_dec_ref(v_newNode_1437_);
v___x_1445_ = lean_unsigned_to_nat(0u);
v___x_1446_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0);
v___x_1447_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(v_x_1381_, v_ks_1443_, v_vs_1444_, v___x_1445_, v___x_1446_);
lean_dec_ref(v_vs_1444_);
lean_dec_ref(v_ks_1443_);
return v___x_1447_;
}
else
{
return v_newNode_1437_;
}
}
else
{
return v_newNode_1437_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1379_ = stack[0].m_obj;
size_t v_x_1380_ = stack[1].m_num;
size_t v_x_1381_ = stack[2].m_num;
lean_object* v_x_1382_ = stack[3].m_obj;
lean_object* v_x_1383_ = stack[4].m_obj;
lean_object* v_res_1450_;
v_res_1450_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_x_1379_, v_x_1380_, v_x_1381_, v_x_1382_, v_x_1383_);
stack->m_obj
 = v_res_1450_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(size_t v_depth_1451_, lean_object* v_keys_1452_, lean_object* v_vals_1453_, lean_object* v_i_1454_, lean_object* v_entries_1455_){
_start:
{
lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1456_ = lean_array_get_size(v_keys_1452_);
v___x_1457_ = lean_nat_dec_lt(v_i_1454_, v___x_1456_);
if (v___x_1457_ == 0)
{
lean_dec(v_i_1454_);
return v_entries_1455_;
}
else
{
lean_object* v_k_1458_; lean_object* v_v_1459_; uint64_t v___x_1460_; size_t v_h_1461_; size_t v___x_1462_; lean_object* v___x_1463_; size_t v___x_1464_; size_t v___x_1465_; size_t v___x_1466_; size_t v_h_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v_k_1458_ = lean_array_fget_borrowed(v_keys_1452_, v_i_1454_);
v_v_1459_ = lean_array_fget_borrowed(v_vals_1453_, v_i_1454_);
v___x_1460_ = l_Lean_instHashableMVarId_hash(v_k_1458_);
v_h_1461_ = lean_uint64_to_usize(v___x_1460_);
v___x_1462_ = ((size_t)5ULL);
v___x_1463_ = lean_unsigned_to_nat(1u);
v___x_1464_ = ((size_t)1ULL);
v___x_1465_ = lean_usize_sub(v_depth_1451_, v___x_1464_);
v___x_1466_ = lean_usize_mul(v___x_1462_, v___x_1465_);
v_h_1467_ = lean_usize_shift_right(v_h_1461_, v___x_1466_);
v___x_1468_ = lean_nat_add(v_i_1454_, v___x_1463_);
lean_dec(v_i_1454_);
lean_inc(v_v_1459_);
lean_inc(v_k_1458_);
v___x_1469_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_entries_1455_, v_h_1467_, v_depth_1451_, v_k_1458_, v_v_1459_);
v_i_1454_ = v___x_1468_;
v_entries_1455_ = v___x_1469_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1451_ = stack[0].m_num;
lean_object* v_keys_1452_ = stack[1].m_obj;
lean_object* v_vals_1453_ = stack[2].m_obj;
lean_object* v_i_1454_ = stack[3].m_obj;
lean_object* v_entries_1455_ = stack[4].m_obj;
lean_object* v_res_1471_;
v_res_1471_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(v_depth_1451_, v_keys_1452_, v_vals_1453_, v_i_1454_, v_entries_1455_);
stack->m_obj
 = v_res_1471_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_depth_1472_, lean_object* v_keys_1473_, lean_object* v_vals_1474_, lean_object* v_i_1475_, lean_object* v_entries_1476_){
_start:
{
size_t v_depth_boxed_1477_; lean_object* v_res_1478_; 
v_depth_boxed_1477_ = lean_unbox_usize(v_depth_1472_);
lean_dec(v_depth_1472_);
v_res_1478_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(v_depth_boxed_1477_, v_keys_1473_, v_vals_1474_, v_i_1475_, v_entries_1476_);
lean_dec_ref(v_vals_1474_);
lean_dec_ref(v_keys_1473_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_x_1479_, lean_object* v_x_1480_, lean_object* v_x_1481_, lean_object* v_x_1482_, lean_object* v_x_1483_){
_start:
{
size_t v_x_7639__boxed_1484_; size_t v_x_7640__boxed_1485_; lean_object* v_res_1486_; 
v_x_7639__boxed_1484_ = lean_unbox_usize(v_x_1480_);
lean_dec(v_x_1480_);
v_x_7640__boxed_1485_ = lean_unbox_usize(v_x_1481_);
lean_dec(v_x_1481_);
v_res_1486_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_x_1479_, v_x_7639__boxed_1484_, v_x_7640__boxed_1485_, v_x_1482_, v_x_1483_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2___redArg(lean_object* v_x_1487_, lean_object* v_x_1488_, lean_object* v_x_1489_){
_start:
{
uint64_t v___x_1490_; size_t v___x_1491_; size_t v___x_1492_; lean_object* v___x_1493_; 
v___x_1490_ = l_Lean_instHashableMVarId_hash(v_x_1488_);
v___x_1491_ = lean_uint64_to_usize(v___x_1490_);
v___x_1492_ = ((size_t)1ULL);
v___x_1493_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_x_1487_, v___x_1491_, v___x_1492_, v_x_1488_, v_x_1489_);
return v___x_1493_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(lean_object* v_mvarId_1494_, lean_object* v_val_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v___x_1498_; lean_object* v_mctx_1499_; lean_object* v_cache_1500_; lean_object* v_zetaDeltaFVarIds_1501_; lean_object* v_postponed_1502_; lean_object* v_diag_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1533_; 
v___x_1498_ = lean_st_ref_take(v___y_1496_);
v_mctx_1499_ = lean_ctor_get(v___x_1498_, 0);
v_cache_1500_ = lean_ctor_get(v___x_1498_, 1);
v_zetaDeltaFVarIds_1501_ = lean_ctor_get(v___x_1498_, 2);
v_postponed_1502_ = lean_ctor_get(v___x_1498_, 3);
v_diag_1503_ = lean_ctor_get(v___x_1498_, 4);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1505_ = v___x_1498_;
v_isShared_1506_ = v_isSharedCheck_1533_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_diag_1503_);
lean_inc(v_postponed_1502_);
lean_inc(v_zetaDeltaFVarIds_1501_);
lean_inc(v_cache_1500_);
lean_inc(v_mctx_1499_);
lean_dec(v___x_1498_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1533_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v_depth_1507_; lean_object* v_levelAssignDepth_1508_; lean_object* v_lmvarCounter_1509_; lean_object* v_mvarCounter_1510_; lean_object* v_lDecls_1511_; lean_object* v_decls_1512_; lean_object* v_userNames_1513_; lean_object* v_lAssignment_1514_; lean_object* v_eAssignment_1515_; lean_object* v_dAssignment_1516_; lean_object* v_instanceTypedMVars_1517_; lean_object* v_synthNormMemo_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1532_; 
v_depth_1507_ = lean_ctor_get(v_mctx_1499_, 0);
v_levelAssignDepth_1508_ = lean_ctor_get(v_mctx_1499_, 1);
v_lmvarCounter_1509_ = lean_ctor_get(v_mctx_1499_, 2);
v_mvarCounter_1510_ = lean_ctor_get(v_mctx_1499_, 3);
v_lDecls_1511_ = lean_ctor_get(v_mctx_1499_, 4);
v_decls_1512_ = lean_ctor_get(v_mctx_1499_, 5);
v_userNames_1513_ = lean_ctor_get(v_mctx_1499_, 6);
v_lAssignment_1514_ = lean_ctor_get(v_mctx_1499_, 7);
v_eAssignment_1515_ = lean_ctor_get(v_mctx_1499_, 8);
v_dAssignment_1516_ = lean_ctor_get(v_mctx_1499_, 9);
v_instanceTypedMVars_1517_ = lean_ctor_get(v_mctx_1499_, 10);
v_synthNormMemo_1518_ = lean_ctor_get(v_mctx_1499_, 11);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_mctx_1499_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1520_ = v_mctx_1499_;
v_isShared_1521_ = v_isSharedCheck_1532_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_synthNormMemo_1518_);
lean_inc(v_instanceTypedMVars_1517_);
lean_inc(v_dAssignment_1516_);
lean_inc(v_eAssignment_1515_);
lean_inc(v_lAssignment_1514_);
lean_inc(v_userNames_1513_);
lean_inc(v_decls_1512_);
lean_inc(v_lDecls_1511_);
lean_inc(v_mvarCounter_1510_);
lean_inc(v_lmvarCounter_1509_);
lean_inc(v_levelAssignDepth_1508_);
lean_inc(v_depth_1507_);
lean_dec(v_mctx_1499_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1532_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1522_ = lean_box(0);
v___x_1523_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2___redArg(v_eAssignment_1515_, v_mvarId_1494_, v_val_1495_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 8, v___x_1523_);
v___x_1525_ = v___x_1520_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_depth_1507_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_levelAssignDepth_1508_);
lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_lmvarCounter_1509_);
lean_ctor_set(v_reuseFailAlloc_1531_, 3, v_mvarCounter_1510_);
lean_ctor_set(v_reuseFailAlloc_1531_, 4, v_lDecls_1511_);
lean_ctor_set(v_reuseFailAlloc_1531_, 5, v_decls_1512_);
lean_ctor_set(v_reuseFailAlloc_1531_, 6, v_userNames_1513_);
lean_ctor_set(v_reuseFailAlloc_1531_, 7, v_lAssignment_1514_);
lean_ctor_set(v_reuseFailAlloc_1531_, 8, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1531_, 9, v_dAssignment_1516_);
lean_ctor_set(v_reuseFailAlloc_1531_, 10, v_instanceTypedMVars_1517_);
lean_ctor_set(v_reuseFailAlloc_1531_, 11, v_synthNormMemo_1518_);
v___x_1525_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1527_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1525_);
v___x_1527_ = v___x_1505_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_cache_1500_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_zetaDeltaFVarIds_1501_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_postponed_1502_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v_diag_1503_);
v___x_1527_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = lean_st_ref_put(v___y_1496_, v___x_1527_);
v___x_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1522_);
return v___x_1529_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1494_ = stack[0].m_obj;
lean_object* v_val_1495_ = stack[1].m_obj;
lean_object* v___y_1496_ = stack[2].m_obj;
lean_object* v_res_1534_;
v_res_1534_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_mvarId_1494_, v_val_1495_, v___y_1496_);
stack->m_obj
 = v_res_1534_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg___boxed(lean_object* v_mvarId_1535_, lean_object* v_val_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_mvarId_1535_, v_val_1536_, v___y_1537_);
lean_dec(v___y_1537_);
return v_res_1539_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1543_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__2));
v___x_1544_ = lean_unsigned_to_nat(33u);
v___x_1545_ = lean_unsigned_to_nat(105u);
v___x_1546_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__1));
v___x_1547_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15));
v___x_1548_ = l_mkPanicMessageWithDecl(v___x_1547_, v___x_1546_, v___x_1545_, v___x_1544_, v___x_1543_);
return v___x_1548_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__4));
v___x_1551_ = l_Lean_stringToMessageData(v___x_1550_);
return v___x_1551_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__6));
v___x_1554_ = l_Lean_stringToMessageData(v___x_1553_);
return v___x_1554_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0(lean_object* v___x_1555_, lean_object* v_snd_1556_, lean_object* v_hyp_1557_, lean_object* v___x_1558_, lean_object* v_args_1559_, lean_object* v_fst_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
if (lean_obj_tag(v___x_1555_) == 1)
{
lean_object* v_val_1570_; lean_object* v_focusHyp_1571_; lean_object* v_restHyps_1572_; lean_object* v_proof_1573_; lean_object* v___x_1574_; 
v_val_1570_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_val_1570_);
lean_dec_ref_known(v___x_1555_, 1);
v_focusHyp_1571_ = lean_ctor_get(v_val_1570_, 0);
lean_inc_ref_n(v_focusHyp_1571_, 2);
v_restHyps_1572_ = lean_ctor_get(v_val_1570_, 1);
lean_inc_ref(v_restHyps_1572_);
v_proof_1573_ = lean_ctor_get(v_val_1570_, 2);
lean_inc_ref(v_proof_1573_);
lean_dec(v_val_1570_);
v___x_1574_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_1571_);
if (lean_obj_tag(v___x_1574_) == 1)
{
lean_object* v_val_1575_; lean_object* v_u_1576_; lean_object* v_00_u03c3s_1577_; lean_object* v_hyps_1578_; lean_object* v_target_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1637_; 
v_val_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_val_1575_);
lean_dec_ref_known(v___x_1574_, 1);
v_u_1576_ = lean_ctor_get(v_snd_1556_, 0);
v_00_u03c3s_1577_ = lean_ctor_get(v_snd_1556_, 1);
v_hyps_1578_ = lean_ctor_get(v_snd_1556_, 2);
v_target_1579_ = lean_ctor_get(v_snd_1556_, 3);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_snd_1556_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1581_ = v_snd_1556_;
v_isShared_1582_ = v_isSharedCheck_1637_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_target_1579_);
lean_inc(v_hyps_1578_);
lean_inc(v_00_u03c3s_1577_);
lean_inc(v_u_1576_);
lean_dec(v_snd_1556_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1637_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
uint8_t v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = 0;
lean_inc_ref(v_00_u03c3s_1577_);
v___x_1584_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_hyp_1557_, v_00_u03c3s_1577_, v_val_1575_, v___x_1583_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; size_t v_sz_1596_; size_t v___x_1597_; lean_object* v___x_1598_; 
lean_dec_ref_known(v___x_1584_, 1);
v___x_1585_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_1586_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1587_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_1588_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1589_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__0));
v___x_1590_ = l_Lean_Name_mkStr6(v___x_1585_, v___x_1586_, v___x_1587_, v___x_1558_, v___x_1588_, v___x_1589_);
v___x_1591_ = lean_box(0);
lean_inc_n(v_u_1576_, 2);
v___x_1592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1592_, 0, v_u_1576_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
lean_inc_ref(v___x_1592_);
v___x_1593_ = l_Lean_mkConst(v___x_1590_, v___x_1592_);
lean_inc_ref_n(v_target_1579_, 2);
lean_inc_ref(v_focusHyp_1571_);
lean_inc_ref_n(v_restHyps_1572_, 2);
lean_inc_ref_n(v_00_u03c3s_1577_, 2);
v___x_1594_ = lean_alloc_closure((void*)(l_Lean_mkApp7), 8, 7);
lean_closure_set(v___x_1594_, 0, v___x_1593_);
lean_closure_set(v___x_1594_, 1, v_00_u03c3s_1577_);
lean_closure_set(v___x_1594_, 2, v_hyps_1578_);
lean_closure_set(v___x_1594_, 3, v_restHyps_1572_);
lean_closure_set(v___x_1594_, 4, v_focusHyp_1571_);
lean_closure_set(v___x_1594_, 5, v_target_1579_);
lean_closure_set(v___x_1594_, 6, v_proof_1573_);
v___x_1595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1595_, 0, v_focusHyp_1571_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v_sz_1596_ = lean_array_size(v_args_1559_);
v___x_1597_ = ((size_t)0ULL);
v___x_1598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1(v___x_1592_, v_u_1576_, v_00_u03c3s_1577_, v_restHyps_1572_, v_target_1579_, v_args_1559_, v_sz_1596_, v___x_1597_, v___x_1595_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v_fst_1600_; lean_object* v_snd_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1628_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
v_fst_1600_ = lean_ctor_get(v_a_1599_, 0);
v_snd_1601_ = lean_ctor_get(v_a_1599_, 1);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_a_1599_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1603_ = v_a_1599_;
v_isShared_1604_ = v_isSharedCheck_1628_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_snd_1601_);
lean_inc(v_fst_1600_);
lean_dec(v_a_1599_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1628_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v___x_1607_; 
lean_inc_ref(v_00_u03c3s_1577_);
lean_inc(v_u_1576_);
v___x_1605_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1576_, v_00_u03c3s_1577_, v_restHyps_1572_, v_fst_1600_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 2, v___x_1605_);
v___x_1607_ = v___x_1581_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_u_1576_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_00_u03c3s_1577_);
lean_ctor_set(v_reuseFailAlloc_1627_, 2, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1627_, 3, v_target_1579_);
v___x_1607_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1608_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1607_);
v___x_1609_ = lean_box(0);
v___x_1610_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1608_, v___x_1609_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1616_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc_n(v_a_1611_, 2);
lean_dec_ref_known(v___x_1610_, 1);
v___x_1612_ = lean_apply_1(v_snd_1601_, v_a_1611_);
v___x_1613_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_fst_1560_, v___x_1612_, v___y_1566_);
lean_dec_ref(v___x_1613_);
v___x_1614_ = l_Lean_Expr_mvarId_x21(v_a_1611_);
lean_dec(v_a_1611_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set_tag(v___x_1603_, 1);
lean_ctor_set(v___x_1603_, 1, v___x_1591_);
lean_ctor_set(v___x_1603_, 0, v___x_1614_);
v___x_1616_ = v___x_1603_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v___x_1591_);
v___x_1616_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1616_, v___y_1562_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
return v___x_1617_;
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_del_object(v___x_1603_);
lean_dec(v_snd_1601_);
lean_dec(v_fst_1560_);
v_a_1619_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1610_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1610_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_del_object(v___x_1581_);
lean_dec_ref(v_target_1579_);
lean_dec_ref(v_00_u03c3s_1577_);
lean_dec(v_u_1576_);
lean_dec_ref(v_restHyps_1572_);
lean_dec(v_fst_1560_);
v_a_1629_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1598_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1598_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
else
{
lean_del_object(v___x_1581_);
lean_dec_ref(v_target_1579_);
lean_dec_ref(v_hyps_1578_);
lean_dec_ref(v_00_u03c3s_1577_);
lean_dec(v_u_1576_);
lean_dec_ref(v_proof_1573_);
lean_dec_ref(v_restHyps_1572_);
lean_dec_ref(v_focusHyp_1571_);
lean_dec(v_fst_1560_);
lean_dec_ref(v___x_1558_);
return v___x_1584_;
}
}
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_dec(v___x_1574_);
lean_dec_ref(v_proof_1573_);
lean_dec_ref(v_restHyps_1572_);
lean_dec_ref(v_focusHyp_1571_);
lean_dec(v_fst_1560_);
lean_dec_ref(v___x_1558_);
lean_dec(v_hyp_1557_);
lean_dec_ref(v_snd_1556_);
v___x_1638_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3);
v___x_1639_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(v___x_1638_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
return v___x_1639_;
}
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
lean_dec(v_fst_1560_);
lean_dec_ref(v___x_1558_);
lean_dec_ref(v_snd_1556_);
lean_dec(v___x_1555_);
v___x_1640_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5);
v___x_1641_ = l_Lean_MessageData_ofSyntax(v_hyp_1557_);
v___x_1642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1640_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7);
v___x_1644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_1644_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
return v___x_1645_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1555_ = stack[0].m_obj;
lean_object* v_snd_1556_ = stack[1].m_obj;
lean_object* v_hyp_1557_ = stack[2].m_obj;
lean_object* v___x_1558_ = stack[3].m_obj;
lean_object* v_args_1559_ = stack[4].m_obj;
lean_object* v_fst_1560_ = stack[5].m_obj;
lean_object* v___y_1561_ = stack[6].m_obj;
lean_object* v___y_1562_ = stack[7].m_obj;
lean_object* v___y_1563_ = stack[8].m_obj;
lean_object* v___y_1564_ = stack[9].m_obj;
lean_object* v___y_1565_ = stack[10].m_obj;
lean_object* v___y_1566_ = stack[11].m_obj;
lean_object* v___y_1567_ = stack[12].m_obj;
lean_object* v___y_1568_ = stack[13].m_obj;
lean_object* v_res_1646_;
v_res_1646_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0(v___x_1555_, v_snd_1556_, v_hyp_1557_, v___x_1558_, v_args_1559_, v_fst_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
stack->m_obj
 = v_res_1646_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___boxed(lean_object* v___x_1647_, lean_object* v_snd_1648_, lean_object* v_hyp_1649_, lean_object* v___x_1650_, lean_object* v_args_1651_, lean_object* v_fst_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0(v___x_1647_, v_snd_1648_, v_hyp_1649_, v___x_1650_, v_args_1651_, v_fst_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec_ref(v_args_1651_);
return v_res_1662_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize(lean_object* v_x_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; 
v___x_1680_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1681_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2));
lean_inc(v_x_1670_);
v___x_1682_ = l_Lean_Syntax_isOfKind(v_x_1670_, v___x_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; 
lean_dec(v_x_1670_);
v___x_1683_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_1683_;
}
else
{
lean_object* v___x_1684_; lean_object* v_hyp_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v_args_1688_; lean_object* v___x_1689_; 
v___x_1684_ = lean_unsigned_to_nat(1u);
v_hyp_1685_ = l_Lean_Syntax_getArg(v_x_1670_, v___x_1684_);
v___x_1686_ = lean_unsigned_to_nat(2u);
v___x_1687_ = l_Lean_Syntax_getArg(v_x_1670_, v___x_1686_);
lean_dec(v_x_1670_);
v_args_1688_ = l_Lean_Syntax_getArgs(v___x_1687_);
lean_dec(v___x_1687_);
v___x_1689_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1672_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v_fst_1691_; lean_object* v_snd_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___y_1695_; lean_object* v___x_1696_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
lean_dec_ref_known(v___x_1689_, 1);
v_fst_1691_ = lean_ctor_get(v_a_1690_, 0);
lean_inc_n(v_fst_1691_, 2);
v_snd_1692_ = lean_ctor_get(v_a_1690_, 1);
lean_inc_n(v_snd_1692_, 2);
lean_dec(v_a_1690_);
v___x_1693_ = l_Lean_TSyntax_getId(v_hyp_1685_);
v___x_1694_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_snd_1692_, v___x_1693_);
lean_dec(v___x_1693_);
v___y_1695_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___boxed), 15, 6);
lean_closure_set(v___y_1695_, 0, v___x_1694_);
lean_closure_set(v___y_1695_, 1, v_snd_1692_);
lean_closure_set(v___y_1695_, 2, v_hyp_1685_);
lean_closure_set(v___y_1695_, 3, v___x_1680_);
lean_closure_set(v___y_1695_, 4, v_args_1688_);
lean_closure_set(v___y_1695_, 5, v_fst_1691_);
v___x_1696_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_fst_1691_, v___y_1695_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_);
return v___x_1696_;
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec_ref(v_args_1688_);
lean_dec(v_hyp_1685_);
v_a_1697_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1689_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1689_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1670_ = stack[0].m_obj;
lean_object* v_a_1671_ = stack[1].m_obj;
lean_object* v_a_1672_ = stack[2].m_obj;
lean_object* v_a_1673_ = stack[3].m_obj;
lean_object* v_a_1674_ = stack[4].m_obj;
lean_object* v_a_1675_ = stack[5].m_obj;
lean_object* v_a_1676_ = stack[6].m_obj;
lean_object* v_a_1677_ = stack[7].m_obj;
lean_object* v_a_1678_ = stack[8].m_obj;
lean_object* v_res_1705_;
v_res_1705_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize(v_x_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_);
stack->m_obj
 = v_res_1705_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___boxed(lean_object* v_x_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize(v_x_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
return v_res_1716_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2(lean_object* v_mvarId_1717_, lean_object* v_val_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_mvarId_1717_, v_val_1718_, v___y_1724_);
return v___x_1728_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1717_ = stack[0].m_obj;
lean_object* v_val_1718_ = stack[1].m_obj;
lean_object* v___y_1719_ = stack[2].m_obj;
lean_object* v___y_1720_ = stack[3].m_obj;
lean_object* v___y_1721_ = stack[4].m_obj;
lean_object* v___y_1722_ = stack[5].m_obj;
lean_object* v___y_1723_ = stack[6].m_obj;
lean_object* v___y_1724_ = stack[7].m_obj;
lean_object* v___y_1725_ = stack[8].m_obj;
lean_object* v___y_1726_ = stack[9].m_obj;
lean_object* v_res_1729_;
v_res_1729_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2(v_mvarId_1717_, v_val_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
stack->m_obj
 = v_res_1729_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___boxed(lean_object* v_mvarId_1730_, lean_object* v_val_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2(v_mvarId_1730_, v_val_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2(lean_object* v_00_u03b2_1742_, lean_object* v_x_1743_, lean_object* v_x_1744_, lean_object* v_x_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2___redArg(v_x_1743_, v_x_1744_, v_x_1745_);
return v___x_1746_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_1747_, lean_object* v_x_1748_, size_t v_x_1749_, size_t v_x_1750_, lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_x_1748_, v_x_1749_, v_x_1750_, v_x_1751_, v_x_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1748_ = stack[1].m_obj;
size_t v_x_1749_ = stack[2].m_num;
size_t v_x_1750_ = stack[3].m_num;
lean_object* v_x_1751_ = stack[4].m_obj;
lean_object* v_x_1752_ = stack[5].m_obj;
lean_object* v_res_1754_;
v_res_1754_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5(lean_box(0), v_x_1748_, v_x_1749_, v_x_1750_, v_x_1751_, v_x_1752_);
stack->m_obj
 = v_res_1754_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1755_, lean_object* v_x_1756_, lean_object* v_x_1757_, lean_object* v_x_1758_, lean_object* v_x_1759_, lean_object* v_x_1760_){
_start:
{
size_t v_x_8464__boxed_1761_; size_t v_x_8465__boxed_1762_; lean_object* v_res_1763_; 
v_x_8464__boxed_1761_ = lean_unbox_usize(v_x_1757_);
lean_dec(v_x_1757_);
v_x_8465__boxed_1762_ = lean_unbox_usize(v_x_1758_);
lean_dec(v_x_1758_);
v_res_1763_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5(v_00_u03b2_1755_, v_x_1756_, v_x_8464__boxed_1761_, v_x_8465__boxed_1762_, v_x_1759_, v_x_1760_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_1764_, lean_object* v_n_1765_, lean_object* v_k_1766_, lean_object* v_v_1767_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6___redArg(v_n_1765_, v_k_1766_, v_v_1767_);
return v___x_1768_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7(lean_object* v_00_u03b2_1769_, size_t v_depth_1770_, lean_object* v_keys_1771_, lean_object* v_vals_1772_, lean_object* v_heq_1773_, lean_object* v_i_1774_, lean_object* v_entries_1775_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(v_depth_1770_, v_keys_1771_, v_vals_1772_, v_i_1774_, v_entries_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1770_ = stack[1].m_num;
lean_object* v_keys_1771_ = stack[2].m_obj;
lean_object* v_vals_1772_ = stack[3].m_obj;
lean_object* v_i_1774_ = stack[5].m_obj;
lean_object* v_entries_1775_ = stack[6].m_obj;
lean_object* v_res_1777_;
v_res_1777_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7(lean_box(0), v_depth_1770_, v_keys_1771_, v_vals_1772_, lean_box(0), v_i_1774_, v_entries_1775_);
stack->m_obj
 = v_res_1777_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b2_1778_, lean_object* v_depth_1779_, lean_object* v_keys_1780_, lean_object* v_vals_1781_, lean_object* v_heq_1782_, lean_object* v_i_1783_, lean_object* v_entries_1784_){
_start:
{
size_t v_depth_boxed_1785_; lean_object* v_res_1786_; 
v_depth_boxed_1785_ = lean_unbox_usize(v_depth_1779_);
lean_dec(v_depth_1779_);
v_res_1786_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7(v_00_u03b2_1778_, v_depth_boxed_1785_, v_keys_1780_, v_vals_1781_, v_heq_1782_, v_i_1783_, v_entries_1784_);
lean_dec_ref(v_vals_1781_);
lean_dec_ref(v_keys_1780_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_1787_, lean_object* v_x_1788_, lean_object* v_x_1789_, lean_object* v_x_1790_, lean_object* v_x_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7___redArg(v_x_1788_, v_x_1789_, v_x_1790_, v_x_1791_);
return v___x_1792_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1(){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1802_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1803_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2));
v___x_1804_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1));
v___x_1805_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___boxed), 10, 0);
v___x_1806_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1802_, v___x_1803_, v___x_1804_, v___x_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1807_;
v_res_1807_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1();
stack->m_obj
 = v_res_1807_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___boxed(lean_object* v_a_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1();
return v_res_1809_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(lean_object* v___y_1810_){
_start:
{
lean_object* v___x_1812_; lean_object* v_ngen_1813_; lean_object* v_namePrefix_1814_; lean_object* v_idx_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1845_; 
v___x_1812_ = lean_st_ref_get(v___y_1810_);
v_ngen_1813_ = lean_ctor_get(v___x_1812_, 2);
lean_inc_ref(v_ngen_1813_);
lean_dec(v___x_1812_);
v_namePrefix_1814_ = lean_ctor_get(v_ngen_1813_, 0);
v_idx_1815_ = lean_ctor_get(v_ngen_1813_, 1);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_ngen_1813_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1817_ = v_ngen_1813_;
v_isShared_1818_ = v_isSharedCheck_1845_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_idx_1815_);
lean_inc(v_namePrefix_1814_);
lean_dec(v_ngen_1813_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1845_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v_r_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1823_; 
lean_inc(v_idx_1815_);
lean_inc(v_namePrefix_1814_);
v_r_1819_ = l_Lean_Name_num___override(v_namePrefix_1814_, v_idx_1815_);
v___x_1820_ = lean_unsigned_to_nat(1u);
v___x_1821_ = lean_nat_add(v_idx_1815_, v___x_1820_);
lean_dec(v_idx_1815_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 1, v___x_1821_);
v___x_1823_ = v___x_1817_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_namePrefix_1814_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1824_; lean_object* v_env_1825_; lean_object* v_nextMacroScope_1826_; lean_object* v_auxDeclNGen_1827_; lean_object* v_traceState_1828_; lean_object* v_cache_1829_; lean_object* v_recordedDeps_1830_; lean_object* v_messages_1831_; lean_object* v_infoState_1832_; lean_object* v_snapshotTasks_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1842_; 
v___x_1824_ = lean_st_ref_take(v___y_1810_);
v_env_1825_ = lean_ctor_get(v___x_1824_, 0);
v_nextMacroScope_1826_ = lean_ctor_get(v___x_1824_, 1);
v_auxDeclNGen_1827_ = lean_ctor_get(v___x_1824_, 3);
v_traceState_1828_ = lean_ctor_get(v___x_1824_, 4);
v_cache_1829_ = lean_ctor_get(v___x_1824_, 5);
v_recordedDeps_1830_ = lean_ctor_get(v___x_1824_, 6);
v_messages_1831_ = lean_ctor_get(v___x_1824_, 7);
v_infoState_1832_ = lean_ctor_get(v___x_1824_, 8);
v_snapshotTasks_1833_ = lean_ctor_get(v___x_1824_, 9);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1842_ == 0)
{
lean_object* v_unused_1843_; 
v_unused_1843_ = lean_ctor_get(v___x_1824_, 2);
lean_dec(v_unused_1843_);
v___x_1835_ = v___x_1824_;
v_isShared_1836_ = v_isSharedCheck_1842_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_snapshotTasks_1833_);
lean_inc(v_infoState_1832_);
lean_inc(v_messages_1831_);
lean_inc(v_recordedDeps_1830_);
lean_inc(v_cache_1829_);
lean_inc(v_traceState_1828_);
lean_inc(v_auxDeclNGen_1827_);
lean_inc(v_nextMacroScope_1826_);
lean_inc(v_env_1825_);
lean_dec(v___x_1824_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1842_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 2, v___x_1823_);
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_env_1825_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_nextMacroScope_1826_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1841_, 3, v_auxDeclNGen_1827_);
lean_ctor_set(v_reuseFailAlloc_1841_, 4, v_traceState_1828_);
lean_ctor_set(v_reuseFailAlloc_1841_, 5, v_cache_1829_);
lean_ctor_set(v_reuseFailAlloc_1841_, 6, v_recordedDeps_1830_);
lean_ctor_set(v_reuseFailAlloc_1841_, 7, v_messages_1831_);
lean_ctor_set(v_reuseFailAlloc_1841_, 8, v_infoState_1832_);
lean_ctor_set(v_reuseFailAlloc_1841_, 9, v_snapshotTasks_1833_);
v___x_1838_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = lean_st_ref_put(v___y_1810_, v___x_1838_);
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v_r_1819_);
return v___x_1840_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1810_ = stack[0].m_obj;
lean_object* v_res_1846_;
v_res_1846_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(v___y_1810_);
stack->m_obj
 = v_res_1846_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg___boxed(lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(v___y_1847_);
lean_dec(v___y_1847_);
return v_res_1849_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0(lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(v___y_1857_);
return v___x_1859_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1850_ = stack[0].m_obj;
lean_object* v___y_1851_ = stack[1].m_obj;
lean_object* v___y_1852_ = stack[2].m_obj;
lean_object* v___y_1853_ = stack[3].m_obj;
lean_object* v___y_1854_ = stack[4].m_obj;
lean_object* v___y_1855_ = stack[5].m_obj;
lean_object* v___y_1856_ = stack[6].m_obj;
lean_object* v___y_1857_ = stack[7].m_obj;
lean_object* v_res_1860_;
v_res_1860_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0(v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
stack->m_obj
 = v_res_1860_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___boxed(lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0(v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
return v_res_1870_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(lean_object* v_e_1871_, lean_object* v___y_1872_){
_start:
{
uint8_t v___x_1874_; 
v___x_1874_ = l_Lean_Expr_hasMVar(v_e_1871_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1875_; 
v___x_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1875_, 0, v_e_1871_);
return v___x_1875_;
}
else
{
lean_object* v___x_1876_; lean_object* v_mctx_1877_; lean_object* v___x_1878_; lean_object* v_fst_1879_; lean_object* v_snd_1880_; lean_object* v___x_1881_; lean_object* v_cache_1882_; lean_object* v_zetaDeltaFVarIds_1883_; lean_object* v_postponed_1884_; lean_object* v_diag_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1894_; 
v___x_1876_ = lean_st_ref_get(v___y_1872_);
v_mctx_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc_ref(v_mctx_1877_);
lean_dec(v___x_1876_);
v___x_1878_ = l_Lean_instantiateMVarsCore(v_mctx_1877_, v_e_1871_);
v_fst_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_fst_1879_);
v_snd_1880_ = lean_ctor_get(v___x_1878_, 1);
lean_inc(v_snd_1880_);
lean_dec_ref(v___x_1878_);
v___x_1881_ = lean_st_ref_take(v___y_1872_);
v_cache_1882_ = lean_ctor_get(v___x_1881_, 1);
v_zetaDeltaFVarIds_1883_ = lean_ctor_get(v___x_1881_, 2);
v_postponed_1884_ = lean_ctor_get(v___x_1881_, 3);
v_diag_1885_ = lean_ctor_get(v___x_1881_, 4);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1894_ == 0)
{
lean_object* v_unused_1895_; 
v_unused_1895_ = lean_ctor_get(v___x_1881_, 0);
lean_dec(v_unused_1895_);
v___x_1887_ = v___x_1881_;
v_isShared_1888_ = v_isSharedCheck_1894_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_diag_1885_);
lean_inc(v_postponed_1884_);
lean_inc(v_zetaDeltaFVarIds_1883_);
lean_inc(v_cache_1882_);
lean_dec(v___x_1881_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1894_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v_snd_1880_);
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_snd_1880_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_cache_1882_);
lean_ctor_set(v_reuseFailAlloc_1893_, 2, v_zetaDeltaFVarIds_1883_);
lean_ctor_set(v_reuseFailAlloc_1893_, 3, v_postponed_1884_);
lean_ctor_set(v_reuseFailAlloc_1893_, 4, v_diag_1885_);
v___x_1890_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_st_ref_put(v___y_1872_, v___x_1890_);
v___x_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1892_, 0, v_fst_1879_);
return v___x_1892_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1871_ = stack[0].m_obj;
lean_object* v___y_1872_ = stack[1].m_obj;
lean_object* v_res_1896_;
v_res_1896_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(v_e_1871_, v___y_1872_);
stack->m_obj
 = v_res_1896_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg___boxed(lean_object* v_e_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(v_e_1897_, v___y_1898_);
lean_dec(v___y_1898_);
return v_res_1900_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1(lean_object* v_e_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(v_e_1901_, v___y_1907_);
return v___x_1911_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1901_ = stack[0].m_obj;
lean_object* v___y_1902_ = stack[1].m_obj;
lean_object* v___y_1903_ = stack[2].m_obj;
lean_object* v___y_1904_ = stack[3].m_obj;
lean_object* v___y_1905_ = stack[4].m_obj;
lean_object* v___y_1906_ = stack[5].m_obj;
lean_object* v___y_1907_ = stack[6].m_obj;
lean_object* v___y_1908_ = stack[7].m_obj;
lean_object* v___y_1909_ = stack[8].m_obj;
lean_object* v_res_1912_;
v_res_1912_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1(v_e_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
stack->m_obj
 = v_res_1912_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___boxed(lean_object* v_e_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1(v_e_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
return v_res_1923_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2(lean_object* v___x_1924_, lean_object* v___x_1925_, lean_object* v___x_1926_, lean_object* v___x_1927_, lean_object* v___x_1928_, lean_object* v_as_1929_, size_t v_sz_1930_, size_t v_i_1931_, lean_object* v_b_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_a_1943_; uint8_t v___x_1947_; 
v___x_1947_ = lean_usize_dec_lt(v_i_1931_, v_sz_1930_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; 
lean_dec_ref(v___x_1928_);
lean_dec_ref(v___x_1927_);
lean_dec_ref(v___x_1926_);
lean_dec(v___x_1925_);
lean_dec(v___x_1924_);
v___x_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1948_, 0, v_b_1932_);
return v___x_1948_;
}
else
{
lean_object* v_fst_1949_; lean_object* v_snd_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_2004_; 
v_fst_1949_ = lean_ctor_get(v_b_1932_, 0);
v_snd_1950_ = lean_ctor_get(v_b_1932_, 1);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_b_1932_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1952_ = v_b_1932_;
v_isShared_1953_ = v_isSharedCheck_2004_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_snd_1950_);
lean_inc(v_fst_1949_);
lean_dec(v_b_1932_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_2004_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v_a_1957_; lean_object* v___y_1959_; lean_object* v___x_1999_; 
v___x_1954_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_1955_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1956_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v_a_1957_ = lean_array_uget_borrowed(v_as_1929_, v_i_1931_);
lean_inc(v_a_1957_);
lean_inc(v_fst_1949_);
lean_inc_ref(v___x_1927_);
v___x_1999_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(v___x_1927_, v_fst_1949_, v_a_1957_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
if (lean_obj_tag(v_a_2000_) == 0)
{
lean_object* v___x_2001_; 
lean_dec_ref_known(v___x_1999_, 1);
lean_inc(v_a_1957_);
lean_inc(v_fst_1949_);
lean_inc_ref(v___x_1927_);
v___x_2001_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(v___x_1927_, v_fst_1949_, v_a_1957_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
if (lean_obj_tag(v_a_2002_) == 0)
{
lean_object* v___x_2003_; 
lean_dec_ref_known(v___x_2001_, 1);
lean_inc(v_a_1957_);
lean_inc(v_fst_1949_);
lean_inc_ref(v___x_1927_);
v___x_2003_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(v___x_1927_, v_fst_1949_, v_a_1957_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
v___y_1959_ = v___x_2003_;
goto v___jp_1958_;
}
else
{
v___y_1959_ = v___x_2001_;
goto v___jp_1958_;
}
}
else
{
v___y_1959_ = v___x_2001_;
goto v___jp_1958_;
}
}
else
{
v___y_1959_ = v___x_1999_;
goto v___jp_1958_;
}
}
else
{
v___y_1959_ = v___x_1999_;
goto v___jp_1958_;
}
v___jp_1958_:
{
if (lean_obj_tag(v___y_1959_) == 0)
{
lean_object* v_a_1960_; 
v_a_1960_ = lean_ctor_get(v___y_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref_known(v___y_1959_, 1);
if (lean_obj_tag(v_a_1960_) == 0)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1961_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1);
lean_inc(v_fst_1949_);
v___x_1962_ = l_Lean_MessageData_ofExpr(v_fst_1949_);
v___x_1963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1961_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_1965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1963_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
lean_inc(v_a_1957_);
v___x_1966_ = l_Lean_MessageData_ofSyntax(v_a_1957_);
v___x_1967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1965_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_1967_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v___x_1970_; 
lean_dec_ref_known(v___x_1968_, 1);
if (v_isShared_1953_ == 0)
{
v___x_1970_ = v___x_1952_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_fst_1949_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_snd_1950_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
v_a_1943_ = v___x_1970_;
goto v___jp_1942_;
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_fst_1949_);
lean_dec_ref(v___x_1928_);
lean_dec_ref(v___x_1927_);
lean_dec_ref(v___x_1926_);
lean_dec(v___x_1925_);
lean_dec(v___x_1924_);
v_a_1972_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1968_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1968_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
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
lean_object* v_val_1980_; lean_object* v_fst_1981_; lean_object* v_snd_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1990_; 
lean_del_object(v___x_1952_);
v_val_1980_ = lean_ctor_get(v_a_1960_, 0);
lean_inc(v_val_1980_);
lean_dec_ref_known(v_a_1960_, 1);
v_fst_1981_ = lean_ctor_get(v_val_1980_, 0);
v_snd_1982_ = lean_ctor_get(v_val_1980_, 1);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_val_1980_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1984_ = v_val_1980_;
v_isShared_1985_ = v_isSharedCheck_1990_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_snd_1982_);
lean_inc(v_fst_1981_);
lean_dec(v_val_1980_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1990_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___f_1986_; lean_object* v___x_1988_; 
lean_inc_ref(v___x_1928_);
lean_inc(v_fst_1981_);
lean_inc_ref(v___x_1927_);
lean_inc_ref(v___x_1926_);
lean_inc(v___x_1925_);
lean_inc(v___x_1924_);
v___f_1986_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0), 13, 12);
lean_closure_set(v___f_1986_, 0, v___x_1954_);
lean_closure_set(v___f_1986_, 1, v___x_1955_);
lean_closure_set(v___f_1986_, 2, v___x_1956_);
lean_closure_set(v___f_1986_, 3, v___x_1924_);
lean_closure_set(v___f_1986_, 4, v___x_1925_);
lean_closure_set(v___f_1986_, 5, v___x_1926_);
lean_closure_set(v___f_1986_, 6, v___x_1927_);
lean_closure_set(v___f_1986_, 7, v_fst_1949_);
lean_closure_set(v___f_1986_, 8, v_fst_1981_);
lean_closure_set(v___f_1986_, 9, v___x_1928_);
lean_closure_set(v___f_1986_, 10, v_snd_1982_);
lean_closure_set(v___f_1986_, 11, v_snd_1950_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 1, v___f_1986_);
v___x_1988_ = v___x_1984_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_fst_1981_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v___f_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
v_a_1943_ = v___x_1988_;
goto v___jp_1942_;
}
}
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_fst_1949_);
lean_dec_ref(v___x_1928_);
lean_dec_ref(v___x_1927_);
lean_dec_ref(v___x_1926_);
lean_dec(v___x_1925_);
lean_dec(v___x_1924_);
v_a_1991_ = lean_ctor_get(v___y_1959_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___y_1959_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___y_1959_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___y_1959_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
}
v___jp_1942_:
{
size_t v___x_1944_; size_t v___x_1945_; 
v___x_1944_ = ((size_t)1ULL);
v___x_1945_ = lean_usize_add(v_i_1931_, v___x_1944_);
v_i_1931_ = v___x_1945_;
v_b_1932_ = v_a_1943_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1924_ = stack[0].m_obj;
lean_object* v___x_1925_ = stack[1].m_obj;
lean_object* v___x_1926_ = stack[2].m_obj;
lean_object* v___x_1927_ = stack[3].m_obj;
lean_object* v___x_1928_ = stack[4].m_obj;
lean_object* v_as_1929_ = stack[5].m_obj;
size_t v_sz_1930_ = stack[6].m_num;
size_t v_i_1931_ = stack[7].m_num;
lean_object* v_b_1932_ = stack[8].m_obj;
lean_object* v___y_1933_ = stack[9].m_obj;
lean_object* v___y_1934_ = stack[10].m_obj;
lean_object* v___y_1935_ = stack[11].m_obj;
lean_object* v___y_1936_ = stack[12].m_obj;
lean_object* v___y_1937_ = stack[13].m_obj;
lean_object* v___y_1938_ = stack[14].m_obj;
lean_object* v___y_1939_ = stack[15].m_obj;
lean_object* v___y_1940_ = stack[16].m_obj;
lean_object* v_res_2005_;
v_res_2005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2(v___x_1924_, v___x_1925_, v___x_1926_, v___x_1927_, v___x_1928_, v_as_1929_, v_sz_1930_, v_i_1931_, v_b_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
stack->m_obj
 = v_res_2005_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2___boxed(lean_object** _args){
lean_object* v___x_2006_ = _args[0];
lean_object* v___x_2007_ = _args[1];
lean_object* v___x_2008_ = _args[2];
lean_object* v___x_2009_ = _args[3];
lean_object* v___x_2010_ = _args[4];
lean_object* v_as_2011_ = _args[5];
lean_object* v_sz_2012_ = _args[6];
lean_object* v_i_2013_ = _args[7];
lean_object* v_b_2014_ = _args[8];
lean_object* v___y_2015_ = _args[9];
lean_object* v___y_2016_ = _args[10];
lean_object* v___y_2017_ = _args[11];
lean_object* v___y_2018_ = _args[12];
lean_object* v___y_2019_ = _args[13];
lean_object* v___y_2020_ = _args[14];
lean_object* v___y_2021_ = _args[15];
lean_object* v___y_2022_ = _args[16];
lean_object* v___y_2023_ = _args[17];
_start:
{
size_t v_sz_boxed_2024_; size_t v_i_boxed_2025_; lean_object* v_res_2026_; 
v_sz_boxed_2024_ = lean_unbox_usize(v_sz_2012_);
lean_dec(v_sz_2012_);
v_i_boxed_2025_ = lean_unbox_usize(v_i_2013_);
lean_dec(v_i_2013_);
v_res_2026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2(v___x_2006_, v___x_2007_, v___x_2008_, v___x_2009_, v___x_2010_, v_as_2011_, v_sz_boxed_2024_, v_i_boxed_2025_, v_b_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec_ref(v_as_2011_);
return v_res_2026_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2034_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__3));
v___x_2035_ = lean_unsigned_to_nat(33u);
v___x_2036_ = lean_unsigned_to_nat(175u);
v___x_2037_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__2));
v___x_2038_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15));
v___x_2039_ = l_mkPanicMessageWithDecl(v___x_2038_, v___x_2037_, v___x_2036_, v___x_2035_, v___x_2034_);
return v___x_2039_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0(lean_object* v___x_2040_, lean_object* v___x_2041_, uint8_t v___x_2042_, lean_object* v_u_2043_, lean_object* v_00_u03c3s_2044_, lean_object* v___x_2045_, lean_object* v_hyp_2046_, lean_object* v_hyps_2047_, lean_object* v_target_2048_, lean_object* v_args_2049_, lean_object* v_fst_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Lean_Elab_Tactic_elabTerm(v___x_2040_, v___x_2041_, v___x_2042_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2062_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc_n(v_a_2061_, 2);
lean_dec_ref_known(v___x_2060_, 1);
lean_inc(v___y_2058_);
lean_inc_ref(v___y_2057_);
lean_inc(v___y_2056_);
lean_inc_ref(v___y_2055_);
v___x_2062_ = lean_infer_type(v_a_2061_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref_known(v___x_2062_, 1);
v___x_2064_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_2065_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_2066_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_2067_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0));
v___x_2068_ = lean_box(0);
lean_inc(v_u_2043_);
v___x_2069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2069_, 0, v_u_2043_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
lean_inc_ref(v___x_2069_);
v___x_2070_ = l_Lean_mkConst(v___x_2067_, v___x_2069_);
lean_inc_ref(v_00_u03c3s_2044_);
v___x_2071_ = l_Lean_Expr_app___override(v___x_2070_, v_00_u03c3s_2044_);
v___x_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
v___x_2073_ = 0;
v___x_2074_ = lean_box(0);
v___x_2075_ = l_Lean_Meta_mkFreshExprMVar(v___x_2072_, v___x_2073_, v___x_2074_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc_n(v_a_2076_, 2);
lean_dec_ref_known(v___x_2075_, 1);
v___x_2077_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__5));
lean_inc_ref(v___x_2045_);
v___x_2078_ = l_Lean_Name_mkStr5(v___x_2064_, v___x_2065_, v___x_2066_, v___x_2045_, v___x_2077_);
lean_inc_ref(v___x_2069_);
v___x_2079_ = l_Lean_mkConst(v___x_2078_, v___x_2069_);
lean_inc_ref(v_00_u03c3s_2044_);
lean_inc(v_a_2063_);
v___x_2080_ = l_Lean_mkApp3(v___x_2079_, v_a_2063_, v_00_u03c3s_2044_, v_a_2076_);
v___x_2081_ = lean_box(0);
v___x_2082_ = l_Lean_Meta_synthInstance(v___x_2080_, v___x_2081_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2084_; lean_object* v_a_2085_; lean_object* v___x_2086_; lean_object* v_a_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; size_t v_sz_2097_; size_t v___x_2098_; lean_object* v___x_2099_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2082_, 1);
v___x_2084_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(v___y_2058_);
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref(v___x_2084_);
v___x_2086_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(v_a_2076_, v___y_2056_);
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
lean_dec_ref(v___x_2086_);
v___x_2088_ = l_Lean_TSyntax_getId(v_hyp_2046_);
v___x_2089_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
lean_ctor_set(v___x_2089_, 1, v_a_2085_);
lean_ctor_set(v___x_2089_, 2, v_a_2087_);
v___x_2090_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_2089_);
v___x_2091_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_2092_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__1));
v___x_2093_ = l_Lean_Name_mkStr6(v___x_2064_, v___x_2065_, v___x_2066_, v___x_2045_, v___x_2091_, v___x_2092_);
lean_inc_ref(v___x_2069_);
v___x_2094_ = l_Lean_mkConst(v___x_2093_, v___x_2069_);
lean_inc_ref_n(v_target_2048_, 2);
lean_inc_ref_n(v_hyps_2047_, 2);
lean_inc_ref(v___x_2090_);
lean_inc_ref_n(v_00_u03c3s_2044_, 2);
v___x_2095_ = lean_alloc_closure((void*)(l_Lean_mkApp8), 9, 8);
lean_closure_set(v___x_2095_, 0, v___x_2094_);
lean_closure_set(v___x_2095_, 1, v_00_u03c3s_2044_);
lean_closure_set(v___x_2095_, 2, v_a_2063_);
lean_closure_set(v___x_2095_, 3, v___x_2090_);
lean_closure_set(v___x_2095_, 4, v_hyps_2047_);
lean_closure_set(v___x_2095_, 5, v_target_2048_);
lean_closure_set(v___x_2095_, 6, v_a_2083_);
lean_closure_set(v___x_2095_, 7, v_a_2061_);
v___x_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2090_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v_sz_2097_ = lean_array_size(v_args_2049_);
v___x_2098_ = ((size_t)0ULL);
lean_inc(v_u_2043_);
v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2(v___x_2069_, v_u_2043_, v_00_u03c3s_2044_, v_hyps_2047_, v_target_2048_, v_args_2049_, v_sz_2097_, v___x_2098_, v___x_2096_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v_fst_2101_; lean_object* v_snd_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2131_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2099_, 1);
v_fst_2101_ = lean_ctor_get(v_a_2100_, 0);
v_snd_2102_ = lean_ctor_get(v_a_2100_, 1);
v_isSharedCheck_2131_ = !lean_is_exclusive(v_a_2100_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2104_ = v_a_2100_;
v_isShared_2105_ = v_isSharedCheck_2131_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_snd_2102_);
lean_inc(v_fst_2101_);
lean_dec(v_a_2100_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2131_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; 
lean_inc(v_fst_2101_);
v___x_2106_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_fst_2101_);
if (lean_obj_tag(v___x_2106_) == 1)
{
lean_object* v_val_2107_; lean_object* v___x_2108_; 
v_val_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_val_2107_);
lean_dec_ref_known(v___x_2106_, 1);
lean_inc_ref(v_00_u03c3s_2044_);
v___x_2108_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_hyp_2046_, v_00_u03c3s_2044_, v_val_2107_, v___x_2042_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
lean_dec_ref_known(v___x_2108_, 1);
lean_inc_ref(v_00_u03c3s_2044_);
lean_inc(v_u_2043_);
v___x_2109_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_2043_, v_00_u03c3s_2044_, v_hyps_2047_, v_fst_2101_);
v___x_2110_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2110_, 0, v_u_2043_);
lean_ctor_set(v___x_2110_, 1, v_00_u03c3s_2044_);
lean_ctor_set(v___x_2110_, 2, v___x_2109_);
lean_ctor_set(v___x_2110_, 3, v_target_2048_);
v___x_2111_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_2110_);
v___x_2112_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2111_, v___x_2074_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2118_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc_n(v_a_2113_, 2);
lean_dec_ref_known(v___x_2112_, 1);
v___x_2114_ = lean_apply_1(v_snd_2102_, v_a_2113_);
v___x_2115_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_fst_2050_, v___x_2114_, v___y_2056_);
lean_dec_ref(v___x_2115_);
v___x_2116_ = l_Lean_Expr_mvarId_x21(v_a_2113_);
lean_dec(v_a_2113_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set_tag(v___x_2104_, 1);
lean_ctor_set(v___x_2104_, 1, v___x_2068_);
lean_ctor_set(v___x_2104_, 0, v___x_2116_);
v___x_2118_ = v___x_2104_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2116_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v___x_2068_);
v___x_2118_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2119_; 
v___x_2119_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2118_, v___y_2052_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
return v___x_2119_;
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_del_object(v___x_2104_);
lean_dec(v_snd_2102_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v_fst_2050_);
v_a_2121_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2112_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2112_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
else
{
lean_del_object(v___x_2104_);
lean_dec(v_snd_2102_);
lean_dec(v_fst_2101_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v_fst_2050_);
lean_dec_ref(v_target_2048_);
lean_dec_ref(v_hyps_2047_);
lean_dec_ref(v_00_u03c3s_2044_);
lean_dec(v_u_2043_);
return v___x_2108_;
}
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
lean_dec(v___x_2106_);
lean_del_object(v___x_2104_);
lean_dec(v_snd_2102_);
lean_dec(v_fst_2101_);
lean_dec(v_fst_2050_);
lean_dec_ref(v_target_2048_);
lean_dec_ref(v_hyps_2047_);
lean_dec(v_hyp_2046_);
lean_dec_ref(v_00_u03c3s_2044_);
lean_dec(v_u_2043_);
v___x_2129_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4, &l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4);
v___x_2130_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(v___x_2129_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
return v___x_2130_;
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v_fst_2050_);
lean_dec_ref(v_target_2048_);
lean_dec_ref(v_hyps_2047_);
lean_dec(v_hyp_2046_);
lean_dec_ref(v_00_u03c3s_2044_);
lean_dec(v_u_2043_);
v_a_2132_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2099_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2099_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
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
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec(v_a_2076_);
lean_dec_ref_known(v___x_2069_, 2);
lean_dec(v_a_2063_);
lean_dec(v_a_2061_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v_fst_2050_);
lean_dec_ref(v_target_2048_);
lean_dec_ref(v_hyps_2047_);
lean_dec(v_hyp_2046_);
lean_dec_ref(v___x_2045_);
lean_dec_ref(v_00_u03c3s_2044_);
lean_dec(v_u_2043_);
v_a_2140_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2082_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2082_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec_ref_known(v___x_2069_, 2);
lean_dec(v_a_2063_);
lean_dec(v_a_2061_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v_fst_2050_);
lean_dec_ref(v_target_2048_);
lean_dec_ref(v_hyps_2047_);
lean_dec(v_hyp_2046_);
lean_dec_ref(v___x_2045_);
lean_dec_ref(v_00_u03c3s_2044_);
lean_dec(v_u_2043_);
v_a_2148_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2075_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2075_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec(v_a_2061_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v_fst_2050_);
lean_dec_ref(v_target_2048_);
lean_dec_ref(v_hyps_2047_);
lean_dec(v_hyp_2046_);
lean_dec_ref(v___x_2045_);
lean_dec_ref(v_00_u03c3s_2044_);
lean_dec(v_u_2043_);
v_a_2156_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2062_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2062_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v_fst_2050_);
lean_dec_ref(v_target_2048_);
lean_dec_ref(v_hyps_2047_);
lean_dec(v_hyp_2046_);
lean_dec_ref(v___x_2045_);
lean_dec_ref(v_00_u03c3s_2044_);
lean_dec(v_u_2043_);
v_a_2164_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2060_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2060_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2040_ = stack[0].m_obj;
lean_object* v___x_2041_ = stack[1].m_obj;
uint8_t v___x_2042_ = stack[2].m_num;
lean_object* v_u_2043_ = stack[3].m_obj;
lean_object* v_00_u03c3s_2044_ = stack[4].m_obj;
lean_object* v___x_2045_ = stack[5].m_obj;
lean_object* v_hyp_2046_ = stack[6].m_obj;
lean_object* v_hyps_2047_ = stack[7].m_obj;
lean_object* v_target_2048_ = stack[8].m_obj;
lean_object* v_args_2049_ = stack[9].m_obj;
lean_object* v_fst_2050_ = stack[10].m_obj;
lean_object* v___y_2051_ = stack[11].m_obj;
lean_object* v___y_2052_ = stack[12].m_obj;
lean_object* v___y_2053_ = stack[13].m_obj;
lean_object* v___y_2054_ = stack[14].m_obj;
lean_object* v___y_2055_ = stack[15].m_obj;
lean_object* v___y_2056_ = stack[16].m_obj;
lean_object* v___y_2057_ = stack[17].m_obj;
lean_object* v___y_2058_ = stack[18].m_obj;
lean_object* v_res_2172_;
v_res_2172_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0(v___x_2040_, v___x_2041_, v___x_2042_, v_u_2043_, v_00_u03c3s_2044_, v___x_2045_, v_hyp_2046_, v_hyps_2047_, v_target_2048_, v_args_2049_, v_fst_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
stack->m_obj
 = v_res_2172_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___boxed(lean_object** _args){
lean_object* v___x_2173_ = _args[0];
lean_object* v___x_2174_ = _args[1];
lean_object* v___x_2175_ = _args[2];
lean_object* v_u_2176_ = _args[3];
lean_object* v_00_u03c3s_2177_ = _args[4];
lean_object* v___x_2178_ = _args[5];
lean_object* v_hyp_2179_ = _args[6];
lean_object* v_hyps_2180_ = _args[7];
lean_object* v_target_2181_ = _args[8];
lean_object* v_args_2182_ = _args[9];
lean_object* v_fst_2183_ = _args[10];
lean_object* v___y_2184_ = _args[11];
lean_object* v___y_2185_ = _args[12];
lean_object* v___y_2186_ = _args[13];
lean_object* v___y_2187_ = _args[14];
lean_object* v___y_2188_ = _args[15];
lean_object* v___y_2189_ = _args[16];
lean_object* v___y_2190_ = _args[17];
lean_object* v___y_2191_ = _args[18];
lean_object* v___y_2192_ = _args[19];
_start:
{
uint8_t v___x_8538__boxed_2193_; lean_object* v_res_2194_; 
v___x_8538__boxed_2193_ = lean_unbox(v___x_2175_);
v_res_2194_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0(v___x_2173_, v___x_2174_, v___x_8538__boxed_2193_, v_u_2176_, v_00_u03c3s_2177_, v___x_2178_, v_hyp_2179_, v_hyps_2180_, v_target_2181_, v_args_2182_, v_fst_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v_args_2182_);
return v_res_2194_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure(lean_object* v_x_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; 
v___x_2218_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_2219_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1));
lean_inc(v_x_2208_);
v___x_2220_ = l_Lean_Syntax_isOfKind(v_x_2208_, v___x_2219_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2221_; 
lean_dec(v_x_2208_);
v___x_2221_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_2221_;
}
else
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; uint8_t v___x_2225_; 
v___x_2222_ = lean_unsigned_to_nat(1u);
v___x_2223_ = l_Lean_Syntax_getArg(v_x_2208_, v___x_2222_);
v___x_2224_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4));
lean_inc(v___x_2223_);
v___x_2225_ = l_Lean_Syntax_isOfKind(v___x_2223_, v___x_2224_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; 
lean_dec(v___x_2223_);
lean_dec(v_x_2208_);
v___x_2226_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_2226_;
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; uint8_t v___x_2230_; 
v___x_2227_ = lean_unsigned_to_nat(0u);
v___x_2228_ = lean_unsigned_to_nat(2u);
v___x_2229_ = l_Lean_Syntax_getArg(v_x_2208_, v___x_2228_);
v___x_2230_ = l_Lean_Syntax_matchesNull(v___x_2229_, v___x_2227_);
if (v___x_2230_ == 0)
{
lean_object* v___x_2231_; 
lean_dec(v___x_2223_);
lean_dec(v_x_2208_);
v___x_2231_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_2231_;
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v_hyp_2235_; lean_object* v_args_2236_; lean_object* v___x_2237_; 
v___x_2232_ = l_Lean_Syntax_getArg(v___x_2223_, v___x_2227_);
v___x_2233_ = l_Lean_Syntax_getArg(v___x_2223_, v___x_2222_);
lean_dec(v___x_2223_);
v___x_2234_ = lean_unsigned_to_nat(4u);
v_hyp_2235_ = l_Lean_Syntax_getArg(v_x_2208_, v___x_2234_);
lean_dec(v_x_2208_);
v_args_2236_ = l_Lean_Syntax_getArgs(v___x_2233_);
lean_dec(v___x_2233_);
v___x_2237_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_2210_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v_snd_2239_; lean_object* v_fst_2240_; lean_object* v_u_2241_; lean_object* v_00_u03c3s_2242_; lean_object* v_hyps_2243_; lean_object* v_target_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; lean_object* v___x_2247_; lean_object* v___f_2248_; lean_object* v___x_2249_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v___x_2237_, 1);
v_snd_2239_ = lean_ctor_get(v_a_2238_, 1);
lean_inc(v_snd_2239_);
v_fst_2240_ = lean_ctor_get(v_a_2238_, 0);
lean_inc_n(v_fst_2240_, 2);
lean_dec(v_a_2238_);
v_u_2241_ = lean_ctor_get(v_snd_2239_, 0);
lean_inc(v_u_2241_);
v_00_u03c3s_2242_ = lean_ctor_get(v_snd_2239_, 1);
lean_inc_ref(v_00_u03c3s_2242_);
v_hyps_2243_ = lean_ctor_get(v_snd_2239_, 2);
lean_inc_ref(v_hyps_2243_);
v_target_2244_ = lean_ctor_get(v_snd_2239_, 3);
lean_inc_ref(v_target_2244_);
lean_dec(v_snd_2239_);
v___x_2245_ = lean_box(0);
v___x_2246_ = 0;
v___x_2247_ = lean_box(v___x_2246_);
v___f_2248_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___boxed), 20, 11);
lean_closure_set(v___f_2248_, 0, v___x_2232_);
lean_closure_set(v___f_2248_, 1, v___x_2245_);
lean_closure_set(v___f_2248_, 2, v___x_2247_);
lean_closure_set(v___f_2248_, 3, v_u_2241_);
lean_closure_set(v___f_2248_, 4, v_00_u03c3s_2242_);
lean_closure_set(v___f_2248_, 5, v___x_2218_);
lean_closure_set(v___f_2248_, 6, v_hyp_2235_);
lean_closure_set(v___f_2248_, 7, v_hyps_2243_);
lean_closure_set(v___f_2248_, 8, v_target_2244_);
lean_closure_set(v___f_2248_, 9, v_args_2236_);
lean_closure_set(v___f_2248_, 10, v_fst_2240_);
v___x_2249_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_fst_2240_, v___f_2248_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
return v___x_2249_;
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec_ref(v_args_2236_);
lean_dec(v_hyp_2235_);
lean_dec(v___x_2232_);
v_a_2250_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2237_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2237_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2208_ = stack[0].m_obj;
lean_object* v_a_2209_ = stack[1].m_obj;
lean_object* v_a_2210_ = stack[2].m_obj;
lean_object* v_a_2211_ = stack[3].m_obj;
lean_object* v_a_2212_ = stack[4].m_obj;
lean_object* v_a_2213_ = stack[5].m_obj;
lean_object* v_a_2214_ = stack[6].m_obj;
lean_object* v_a_2215_ = stack[7].m_obj;
lean_object* v_a_2216_ = stack[8].m_obj;
lean_object* v_res_2258_;
v_res_2258_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure(v_x_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
stack->m_obj
 = v_res_2258_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___boxed(lean_object* v_x_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure(v_x_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
lean_dec(v_a_2263_);
lean_dec_ref(v_a_2262_);
lean_dec(v_a_2261_);
lean_dec_ref(v_a_2260_);
return v_res_2269_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1(){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2279_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2280_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1));
v___x_2281_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1));
v___x_2282_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___boxed), 10, 0);
v___x_2283_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2279_, v___x_2280_, v___x_2281_, v___x_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2284_;
v_res_2284_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1();
stack->m_obj
 = v_res_2284_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___boxed(lean_object* v_a_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1();
return v_res_2286_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Specialize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Specialize(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Specialize(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Specialize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Specialize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_ProofMode_Specialize(builtin);
}
#ifdef __cplusplus
}
#endif
