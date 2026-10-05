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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_(){
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2____boxed(lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_();
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(lean_object* v_msgData_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v___x_107_; lean_object* v_env_108_; uint8_t v___x_109_; lean_object* v_env_110_; lean_object* v___x_111_; lean_object* v_toCold_112_; lean_object* v_mctx_113_; lean_object* v_lctx_114_; lean_object* v_options_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_107_ = lean_st_ref_get(v___y_105_);
v_env_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc_ref(v_env_108_);
lean_dec(v___x_107_);
v___x_109_ = 0;
v_env_110_ = l_Lean_Environment_setRecordingDeps(v_env_108_, v___x_109_);
v___x_111_ = lean_st_ref_get(v___y_103_);
v_toCold_112_ = lean_ctor_get(v___y_104_, 0);
v_mctx_113_ = lean_ctor_get(v___x_111_, 0);
lean_inc_ref(v_mctx_113_);
lean_dec(v___x_111_);
v_lctx_114_ = lean_ctor_get(v___y_102_, 2);
v_options_115_ = lean_ctor_get(v_toCold_112_, 2);
lean_inc_ref(v_options_115_);
lean_inc_ref(v_lctx_114_);
v___x_116_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_116_, 0, v_env_110_);
lean_ctor_set(v___x_116_, 1, v_mctx_113_);
lean_ctor_set(v___x_116_, 2, v_lctx_114_);
lean_ctor_set(v___x_116_, 3, v_options_115_);
v___x_117_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v_msgData_101_);
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0___boxed(lean_object* v_msgData_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(v_msgData_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
return v_res_125_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_126_; double v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_float_of_nat(v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(lean_object* v_cls_131_, lean_object* v_msg_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_ref_138_; lean_object* v___x_139_; lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_185_; 
v_ref_138_ = lean_ctor_get(v___y_135_, 2);
v___x_139_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(v_msg_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
v_a_140_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_185_ == 0)
{
v___x_142_ = v___x_139_;
v_isShared_143_ = v_isSharedCheck_185_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_185_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v_traceState_145_; lean_object* v_env_146_; lean_object* v_nextMacroScope_147_; lean_object* v_ngen_148_; lean_object* v_auxDeclNGen_149_; lean_object* v_cache_150_; lean_object* v_recordedDeps_151_; lean_object* v_messages_152_; lean_object* v_infoState_153_; lean_object* v_snapshotTasks_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_184_; 
v___x_144_ = lean_st_ref_take(v___y_136_);
v_traceState_145_ = lean_ctor_get(v___x_144_, 4);
v_env_146_ = lean_ctor_get(v___x_144_, 0);
v_nextMacroScope_147_ = lean_ctor_get(v___x_144_, 1);
v_ngen_148_ = lean_ctor_get(v___x_144_, 2);
v_auxDeclNGen_149_ = lean_ctor_get(v___x_144_, 3);
v_cache_150_ = lean_ctor_get(v___x_144_, 5);
v_recordedDeps_151_ = lean_ctor_get(v___x_144_, 6);
v_messages_152_ = lean_ctor_get(v___x_144_, 7);
v_infoState_153_ = lean_ctor_get(v___x_144_, 8);
v_snapshotTasks_154_ = lean_ctor_get(v___x_144_, 9);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_184_ == 0)
{
v___x_156_ = v___x_144_;
v_isShared_157_ = v_isSharedCheck_184_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_snapshotTasks_154_);
lean_inc(v_infoState_153_);
lean_inc(v_messages_152_);
lean_inc(v_recordedDeps_151_);
lean_inc(v_cache_150_);
lean_inc(v_traceState_145_);
lean_inc(v_auxDeclNGen_149_);
lean_inc(v_ngen_148_);
lean_inc(v_nextMacroScope_147_);
lean_inc(v_env_146_);
lean_dec(v___x_144_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_184_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
uint64_t v_tid_158_; lean_object* v_traces_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_183_; 
v_tid_158_ = lean_ctor_get_uint64(v_traceState_145_, sizeof(void*)*1);
v_traces_159_ = lean_ctor_get(v_traceState_145_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v_traceState_145_);
if (v_isSharedCheck_183_ == 0)
{
v___x_161_ = v_traceState_145_;
v_isShared_162_ = v_isSharedCheck_183_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_traces_159_);
lean_dec(v_traceState_145_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_183_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_164_; double v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_163_ = lean_box(0);
v___x_164_ = lean_box(0);
v___x_165_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0);
v___x_166_ = 0;
v___x_167_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__1));
v___x_168_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_168_, 0, v_cls_131_);
lean_ctor_set(v___x_168_, 1, v___x_164_);
lean_ctor_set(v___x_168_, 2, v___x_167_);
lean_ctor_set_float(v___x_168_, sizeof(void*)*3, v___x_165_);
lean_ctor_set_float(v___x_168_, sizeof(void*)*3 + 8, v___x_165_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*3 + 16, v___x_166_);
v___x_169_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__2));
v___x_170_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set(v___x_170_, 1, v_a_140_);
lean_ctor_set(v___x_170_, 2, v___x_169_);
lean_inc(v_ref_138_);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v_ref_138_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = l_Lean_PersistentArray_push___redArg(v_traces_159_, v___x_171_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_172_);
v___x_174_ = v___x_161_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_172_);
lean_ctor_set_uint64(v_reuseFailAlloc_182_, sizeof(void*)*1, v_tid_158_);
v___x_174_ = v_reuseFailAlloc_182_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_176_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 4, v___x_174_);
v___x_176_ = v___x_156_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_env_146_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_nextMacroScope_147_);
lean_ctor_set(v_reuseFailAlloc_181_, 2, v_ngen_148_);
lean_ctor_set(v_reuseFailAlloc_181_, 3, v_auxDeclNGen_149_);
lean_ctor_set(v_reuseFailAlloc_181_, 4, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_181_, 5, v_cache_150_);
lean_ctor_set(v_reuseFailAlloc_181_, 6, v_recordedDeps_151_);
lean_ctor_set(v_reuseFailAlloc_181_, 7, v_messages_152_);
lean_ctor_set(v_reuseFailAlloc_181_, 8, v_infoState_153_);
lean_ctor_set(v_reuseFailAlloc_181_, 9, v_snapshotTasks_154_);
v___x_176_ = v_reuseFailAlloc_181_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_177_ = lean_st_ref_put(v___y_136_, v___x_176_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_163_);
v___x_179_ = v___x_142_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_163_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___boxed(lean_object* v_cls_186_, lean_object* v_msg_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v_cls_186_, v_msg_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(lean_object* v_msg_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_ref_200_; lean_object* v___x_201_; lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_210_; 
v_ref_200_ = lean_ctor_get(v___y_197_, 2);
v___x_201_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(v_msg_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
v_a_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_210_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_210_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_210_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_208_; 
lean_inc(v_ref_200_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v_ref_200_);
lean_ctor_set(v___x_206_, 1, v_a_202_);
if (v_isShared_205_ == 0)
{
lean_ctor_set_tag(v___x_204_, 1);
lean_ctor_set(v___x_204_, 0, v___x_206_);
v___x_208_ = v___x_204_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg___boxed(lean_object* v_msg_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v_msg_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_217_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__5));
v___x_231_ = l_Lean_stringToMessageData(v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__7));
v___x_234_ = l_Lean_stringToMessageData(v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_239_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__10));
v___x_240_ = l_Lean_Name_append(v___x_239_, v___x_238_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__12));
v___x_243_ = l_Lean_stringToMessageData(v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__14));
v___x_246_ = l_Lean_stringToMessageData(v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(lean_object* v_P_247_, lean_object* v_QR_248_, lean_object* v_arg_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
uint8_t v___x_262_; 
v___x_262_ = l_Lean_Syntax_isIdent(v_arg_249_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec(v_arg_249_);
lean_dec_ref(v_QR_248_);
lean_dec_ref(v_P_247_);
v___x_263_ = lean_box(0);
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
else
{
lean_object* v___x_265_; 
lean_inc_ref(v_QR_248_);
v___x_265_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_QR_248_);
if (lean_obj_tag(v___x_265_) == 1)
{
lean_object* v_val_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_423_; 
v_val_266_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_423_ == 0)
{
v___x_268_ = v___x_265_;
v_isShared_269_ = v_isSharedCheck_423_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_val_266_);
lean_dec(v___x_265_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_423_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v_p_270_; 
v_p_270_ = lean_ctor_get(v_val_266_, 2);
lean_inc_ref(v_p_270_);
if (lean_obj_tag(v_p_270_) == 5)
{
lean_object* v_fn_271_; 
v_fn_271_ = lean_ctor_get(v_p_270_, 0);
if (lean_obj_tag(v_fn_271_) == 5)
{
lean_object* v_fn_272_; 
v_fn_272_ = lean_ctor_get(v_fn_271_, 0);
if (lean_obj_tag(v_fn_272_) == 5)
{
lean_object* v_fn_273_; 
v_fn_273_ = lean_ctor_get(v_fn_272_, 0);
if (lean_obj_tag(v_fn_273_) == 4)
{
lean_object* v_declName_274_; 
v_declName_274_ = lean_ctor_get(v_fn_273_, 0);
if (lean_obj_tag(v_declName_274_) == 1)
{
lean_object* v_pre_275_; 
v_pre_275_ = lean_ctor_get(v_declName_274_, 0);
if (lean_obj_tag(v_pre_275_) == 1)
{
lean_object* v_pre_276_; 
v_pre_276_ = lean_ctor_get(v_pre_275_, 0);
if (lean_obj_tag(v_pre_276_) == 1)
{
lean_object* v_pre_277_; 
v_pre_277_ = lean_ctor_get(v_pre_276_, 0);
if (lean_obj_tag(v_pre_277_) == 1)
{
lean_object* v_pre_278_; 
v_pre_278_ = lean_ctor_get(v_pre_277_, 0);
if (lean_obj_tag(v_pre_278_) == 0)
{
lean_object* v_name_279_; lean_object* v_uniq_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_421_; 
v_name_279_ = lean_ctor_get(v_val_266_, 0);
v_uniq_280_ = lean_ctor_get(v_val_266_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v_val_266_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v_val_266_, 2);
lean_dec(v_unused_422_);
v___x_282_ = v_val_266_;
v_isShared_283_ = v_isSharedCheck_421_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_uniq_280_);
lean_inc(v_name_279_);
lean_dec(v_val_266_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_421_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v_arg_284_; lean_object* v_arg_285_; lean_object* v_arg_286_; lean_object* v_us_287_; lean_object* v_str_288_; lean_object* v_str_289_; lean_object* v_str_290_; lean_object* v_str_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v_arg_284_ = lean_ctor_get(v_p_270_, 1);
v_arg_285_ = lean_ctor_get(v_fn_271_, 1);
v_arg_286_ = lean_ctor_get(v_fn_272_, 1);
v_us_287_ = lean_ctor_get(v_fn_273_, 1);
v_str_288_ = lean_ctor_get(v_declName_274_, 1);
v_str_289_ = lean_ctor_get(v_pre_275_, 1);
v_str_290_ = lean_ctor_get(v_pre_276_, 1);
v_str_291_ = lean_ctor_get(v_pre_277_, 1);
v___x_292_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_293_ = lean_string_dec_eq(v_str_291_, v___x_292_);
if (v___x_293_ == 0)
{
lean_del_object(v___x_282_);
lean_dec(v_uniq_280_);
lean_dec(v_name_279_);
lean_dec_ref_known(v_p_270_, 2);
lean_del_object(v___x_268_);
lean_dec(v_arg_249_);
lean_dec_ref(v_QR_248_);
lean_dec_ref(v_P_247_);
goto v___jp_259_;
}
else
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_295_ = lean_string_dec_eq(v_str_290_, v___x_294_);
if (v___x_295_ == 0)
{
lean_del_object(v___x_282_);
lean_dec(v_uniq_280_);
lean_dec(v_name_279_);
lean_dec_ref_known(v_p_270_, 2);
lean_del_object(v___x_268_);
lean_dec(v_arg_249_);
lean_dec_ref(v_QR_248_);
lean_dec_ref(v_P_247_);
goto v___jp_259_;
}
else
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_297_ = lean_string_dec_eq(v_str_289_, v___x_296_);
if (v___x_297_ == 0)
{
lean_del_object(v___x_282_);
lean_dec(v_uniq_280_);
lean_dec(v_name_279_);
lean_dec_ref_known(v_p_270_, 2);
lean_del_object(v___x_268_);
lean_dec(v_arg_249_);
lean_dec_ref(v_QR_248_);
lean_dec_ref(v_P_247_);
goto v___jp_259_;
}
else
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__2));
v___x_299_ = lean_string_dec_eq(v_str_288_, v___x_298_);
if (v___x_299_ == 0)
{
lean_del_object(v___x_282_);
lean_dec(v_uniq_280_);
lean_dec(v_name_279_);
lean_dec_ref_known(v_p_270_, 2);
lean_del_object(v___x_268_);
lean_dec(v_arg_249_);
lean_dec_ref(v_QR_248_);
lean_dec_ref(v_P_247_);
goto v___jp_259_;
}
else
{
if (lean_obj_tag(v_us_287_) == 1)
{
lean_object* v_tail_300_; 
v_tail_300_ = lean_ctor_get(v_us_287_, 1);
if (lean_obj_tag(v_tail_300_) == 0)
{
lean_object* v_head_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_head_301_ = lean_ctor_get(v_us_287_, 0);
lean_inc_ref(v_P_247_);
lean_inc_ref_n(v_arg_286_, 2);
lean_inc_n(v_head_301_, 2);
v___x_302_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_head_301_, v_arg_286_, v_P_247_, v_QR_248_);
v___x_303_ = l_Lean_Syntax_getId(v_arg_249_);
v___x_304_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(v_head_301_, v_arg_286_, v___x_302_, v___x_303_);
lean_dec(v___x_303_);
if (lean_obj_tag(v___x_304_) == 1)
{
lean_object* v_val_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_416_; 
lean_del_object(v___x_268_);
v_val_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_416_ == 0)
{
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_416_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_val_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_416_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v_focusHyp_309_; lean_object* v_restHyps_310_; lean_object* v_proof_311_; lean_object* v___x_312_; 
v_focusHyp_309_ = lean_ctor_get(v_val_305_, 0);
lean_inc_ref_n(v_focusHyp_309_, 2);
v_restHyps_310_ = lean_ctor_get(v_val_305_, 1);
lean_inc_ref(v_restHyps_310_);
v_proof_311_ = lean_ctor_get(v_val_305_, 2);
lean_inc_ref(v_proof_311_);
lean_dec(v_val_305_);
v___x_312_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_309_);
if (lean_obj_tag(v___x_312_) == 1)
{
lean_object* v_val_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_411_; 
lean_del_object(v___x_307_);
v_val_313_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_411_ == 0)
{
v___x_315_ = v___x_312_;
v_isShared_316_ = v_isSharedCheck_411_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_val_313_);
lean_dec(v___x_312_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_411_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
uint8_t v___x_317_; lean_object* v___x_318_; 
v___x_317_ = 0;
lean_inc_ref(v_arg_286_);
v___x_318_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_arg_249_, v_arg_286_, v_val_313_, v___x_317_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_401_; 
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_401_ == 0)
{
lean_object* v_unused_402_; 
v_unused_402_ = lean_ctor_get(v___x_318_, 0);
lean_dec(v_unused_402_);
v___x_320_ = v___x_318_;
v_isShared_321_ = v_isSharedCheck_401_;
goto v_resetjp_319_;
}
else
{
lean_dec(v___x_318_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_401_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v_toCold_322_; lean_object* v_options_323_; lean_object* v_inheritedTraceOptions_324_; uint8_t v_hasTrace_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; 
v_toCold_322_ = lean_ctor_get(v_a_256_, 0);
v_options_323_ = lean_ctor_get(v_toCold_322_, 2);
v_inheritedTraceOptions_324_ = lean_ctor_get(v_toCold_322_, 11);
v_hasTrace_325_ = lean_ctor_get_uint8(v_options_323_, sizeof(void*)*1);
v___x_326_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4));
lean_inc_ref(v_us_287_);
v___x_327_ = l_Lean_mkConst(v___x_326_, v_us_287_);
lean_inc_ref(v_arg_284_);
lean_inc_ref(v_focusHyp_309_);
lean_inc_ref(v_P_247_);
lean_inc_ref(v_arg_286_);
v___x_328_ = l_Lean_mkApp6(v___x_327_, v_arg_286_, v_P_247_, v_restHyps_310_, v_focusHyp_309_, v_arg_284_, v_proof_311_);
if (v_hasTrace_325_ == 0)
{
lean_dec_ref(v_P_247_);
v___y_342_ = v_a_250_;
v___y_343_ = v_a_251_;
v___y_344_ = v_a_252_;
v___y_345_ = v_a_253_;
v___y_346_ = v_a_254_;
v___y_347_ = v_a_255_;
v___y_348_ = v_a_256_;
v___y_349_ = v_a_257_;
goto v___jp_341_;
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_377_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_378_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11);
v___x_379_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_324_, v_options_323_, v___x_378_);
if (v___x_379_ == 0)
{
lean_dec_ref(v_P_247_);
v___y_342_ = v_a_250_;
v___y_343_ = v_a_251_;
v___y_344_ = v_a_252_;
v___y_345_ = v_a_253_;
v___y_346_ = v_a_254_;
v___y_347_ = v_a_255_;
v___y_348_ = v_a_256_;
v___y_349_ = v_a_257_;
goto v___jp_341_;
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_380_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13);
lean_inc_ref(v_p_270_);
v___x_381_ = l_Lean_MessageData_ofExpr(v_p_270_);
v___x_382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
lean_inc_ref(v_focusHyp_309_);
v___x_385_ = l_Lean_MessageData_ofExpr(v_focusHyp_309_);
v___x_386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15);
v___x_388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
lean_inc_ref(v_arg_284_);
lean_inc_ref(v_arg_286_);
lean_inc(v_head_301_);
v___x_389_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_head_301_, v_arg_286_, v_P_247_, v_arg_284_);
v___x_390_ = l_Lean_MessageData_ofExpr(v___x_389_);
v___x_391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_388_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v___x_377_, v___x_391_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_dec_ref_known(v___x_392_, 1);
v___y_342_ = v_a_250_;
v___y_343_ = v_a_251_;
v___y_344_ = v_a_252_;
v___y_345_ = v_a_253_;
v___y_346_ = v_a_254_;
v___y_347_ = v_a_255_;
v___y_348_ = v_a_256_;
v___y_349_ = v_a_257_;
goto v___jp_341_;
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec_ref(v___x_328_);
lean_del_object(v___x_320_);
lean_del_object(v___x_315_);
lean_dec_ref(v_focusHyp_309_);
lean_del_object(v___x_282_);
lean_dec(v_uniq_280_);
lean_dec(v_name_279_);
lean_dec_ref_known(v_p_270_, 2);
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
}
}
v___jp_329_:
{
lean_object* v___x_331_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 2, v_arg_284_);
v___x_331_ = v___x_282_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_name_279_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_uniq_280_);
lean_ctor_set(v_reuseFailAlloc_340_, 2, v_arg_284_);
v___x_331_ = v_reuseFailAlloc_340_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_332_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_331_);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_328_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_333_);
v___x_335_ = v___x_315_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_333_);
v___x_335_ = v_reuseFailAlloc_339_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_337_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v___x_335_);
v___x_337_ = v___x_320_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_335_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
v___jp_341_:
{
lean_object* v___x_350_; 
lean_inc_ref(v_arg_285_);
lean_inc_ref(v_focusHyp_309_);
v___x_350_ = l_Lean_Meta_isExprDefEq(v_focusHyp_309_, v_arg_285_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; uint8_t v___x_352_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_a_351_);
lean_dec_ref_known(v___x_350_, 1);
v___x_352_ = lean_unbox(v_a_351_);
lean_dec(v_a_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
lean_dec_ref(v___x_328_);
lean_del_object(v___x_320_);
lean_del_object(v___x_315_);
lean_del_object(v___x_282_);
lean_dec(v_uniq_280_);
lean_dec(v_name_279_);
v___x_353_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6);
v___x_354_ = l_Lean_MessageData_ofExpr(v_p_270_);
v___x_355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_353_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
v___x_356_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_355_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
v___x_358_ = l_Lean_MessageData_ofExpr(v_focusHyp_309_);
v___x_359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_359_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
else
{
lean_inc_ref(v_arg_284_);
lean_dec_ref(v_focusHyp_309_);
lean_dec_ref_known(v_p_270_, 2);
goto v___jp_329_;
}
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_dec_ref(v___x_328_);
lean_del_object(v___x_320_);
lean_del_object(v___x_315_);
lean_dec_ref(v_focusHyp_309_);
lean_del_object(v___x_282_);
lean_dec(v_uniq_280_);
lean_dec(v_name_279_);
lean_dec_ref_known(v_p_270_, 2);
v_a_369_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_350_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_350_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_del_object(v___x_315_);
lean_dec_ref(v_proof_311_);
lean_dec_ref(v_restHyps_310_);
lean_dec_ref(v_focusHyp_309_);
lean_del_object(v___x_282_);
lean_dec(v_uniq_280_);
lean_dec(v_name_279_);
lean_dec_ref_known(v_p_270_, 2);
lean_dec_ref(v_P_247_);
v_a_403_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_318_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_318_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
else
{
lean_object* v___x_412_; lean_object* v___x_414_; 
lean_dec(v___x_312_);
lean_dec_ref(v_proof_311_);
lean_dec_ref(v_restHyps_310_);
lean_dec_ref(v_focusHyp_309_);
lean_del_object(v___x_282_);
lean_dec(v_uniq_280_);
lean_dec(v_name_279_);
lean_dec_ref_known(v_p_270_, 2);
lean_dec(v_arg_249_);
lean_dec_ref(v_P_247_);
v___x_412_ = lean_box(0);
if (v_isShared_308_ == 0)
{
lean_ctor_set_tag(v___x_307_, 0);
lean_ctor_set(v___x_307_, 0, v___x_412_);
v___x_414_ = v___x_307_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
else
{
lean_object* v___x_417_; lean_object* v___x_419_; 
lean_dec(v___x_304_);
lean_del_object(v___x_282_);
lean_dec(v_uniq_280_);
lean_dec(v_name_279_);
lean_dec_ref_known(v_p_270_, 2);
lean_dec(v_arg_249_);
lean_dec_ref(v_P_247_);
v___x_417_ = lean_box(0);
if (v_isShared_269_ == 0)
{
lean_ctor_set_tag(v___x_268_, 0);
lean_ctor_set(v___x_268_, 0, v___x_417_);
v___x_419_ = v___x_268_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
else
{
lean_del_object(v___x_282_);
lean_dec(v_uniq_280_);
lean_dec(v_name_279_);
lean_dec_ref_known(v_p_270_, 2);
lean_del_object(v___x_268_);
lean_dec(v_arg_249_);
lean_dec_ref(v_QR_248_);
lean_dec_ref(v_P_247_);
goto v___jp_259_;
}
}
else
{
lean_del_object(v___x_282_);
lean_dec(v_uniq_280_);
lean_dec(v_name_279_);
lean_dec_ref_known(v_p_270_, 2);
lean_del_object(v___x_268_);
lean_dec(v_arg_249_);
lean_dec_ref(v_QR_248_);
lean_dec_ref(v_P_247_);
goto v___jp_259_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_p_270_, 2);
lean_del_object(v___x_268_);
lean_dec(v_val_266_);
lean_dec(v_arg_249_);
lean_dec_ref(v_QR_248_);
lean_dec_ref(v_P_247_);
goto v___jp_259_;
}
}
else
{
lean_dec_ref_known(v_p_270_, 2);
lean_del_object(v___x_268_);
lean_dec(v_val_266_);
lean_dec(v_arg_249_);
lean_dec_ref(v_QR_248_);
lean_dec_ref(v_P_247_);
goto v___jp_259_;
}
}
else
{
lean_dec_ref_known(v_p_270_, 2);
lean_del_object(v___x_268_);
lean_dec(v_val_266_);
lean_dec(v_arg_249_);
lean_dec_ref(v_QR_248_);
lean_dec_ref(v_P_247_);
goto v___jp_259_;
}
}
else
{
lean_dec_ref_known(v_p_270_, 2);
lean_del_object(v___x_268_);
lean_dec(v_val_266_);
lean_dec(v_arg_249_);
lean_dec_ref(v_QR_248_);
lean_dec_ref(v_P_247_);
goto v___jp_259_;
}
}
else
{
lean_dec_ref_known(v_p_270_, 2);
lean_del_object(v___x_268_);
lean_dec(v_val_266_);
lean_dec(v_arg_249_);
lean_dec_ref(v_QR_248_);
lean_dec_ref(v_P_247_);
goto v___jp_259_;
}
}
else
{
lean_dec_ref_known(v_p_270_, 2);
lean_del_object(v___x_268_);
lean_dec(v_val_266_);
lean_dec(v_arg_249_);
lean_dec_ref(v_QR_248_);
lean_dec_ref(v_P_247_);
goto v___jp_259_;
}
}
else
{
lean_dec_ref_known(v_p_270_, 2);
lean_del_object(v___x_268_);
lean_dec(v_val_266_);
lean_dec(v_arg_249_);
lean_dec_ref(v_QR_248_);
lean_dec_ref(v_P_247_);
goto v___jp_259_;
}
}
else
{
lean_dec_ref_known(v_p_270_, 2);
lean_del_object(v___x_268_);
lean_dec(v_val_266_);
lean_dec(v_arg_249_);
lean_dec_ref(v_QR_248_);
lean_dec_ref(v_P_247_);
goto v___jp_259_;
}
}
else
{
lean_dec_ref(v_p_270_);
lean_del_object(v___x_268_);
lean_dec(v_val_266_);
lean_dec(v_arg_249_);
lean_dec_ref(v_QR_248_);
lean_dec_ref(v_P_247_);
goto v___jp_259_;
}
}
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec(v___x_265_);
lean_dec(v_arg_249_);
lean_dec_ref(v_QR_248_);
lean_dec_ref(v_P_247_);
v___x_424_ = lean_box(0);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
}
v___jp_259_:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_box(0);
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___boxed(lean_object* v_P_426_, lean_object* v_QR_427_, lean_object* v_arg_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(v_P_426_, v_QR_427_, v_arg_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0(lean_object* v_00_u03b1_439_, lean_object* v_msg_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v_msg_440_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___boxed(lean_object* v_00_u03b1_451_, lean_object* v_msg_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0(v_00_u03b1_451_, v_msg_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1(lean_object* v_cls_463_, lean_object* v_msg_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v_cls_463_, v_msg_464_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___boxed(lean_object* v_cls_475_, lean_object* v_msg_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1(v_cls_475_, v_msg_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v_res_486_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0(void){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_instMonadEIO___redArg();
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(lean_object* v_msg_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v_toApplicative_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_598_; 
v___x_504_ = lean_obj_once(&l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0, &l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0);
v___x_505_ = l_StateRefT_x27_instMonad___redArg(v___x_504_);
v_toApplicative_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v___x_505_, 1);
lean_dec(v_unused_599_);
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_598_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_toApplicative_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_598_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v_toFunctor_510_; lean_object* v_toSeq_511_; lean_object* v_toSeqLeft_512_; lean_object* v_toSeqRight_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_596_; 
v_toFunctor_510_ = lean_ctor_get(v_toApplicative_506_, 0);
v_toSeq_511_ = lean_ctor_get(v_toApplicative_506_, 2);
v_toSeqLeft_512_ = lean_ctor_get(v_toApplicative_506_, 3);
v_toSeqRight_513_ = lean_ctor_get(v_toApplicative_506_, 4);
v_isSharedCheck_596_ = !lean_is_exclusive(v_toApplicative_506_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; 
v_unused_597_ = lean_ctor_get(v_toApplicative_506_, 1);
lean_dec(v_unused_597_);
v___x_515_ = v_toApplicative_506_;
v_isShared_516_ = v_isSharedCheck_596_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_toSeqRight_513_);
lean_inc(v_toSeqLeft_512_);
lean_inc(v_toSeq_511_);
lean_inc(v_toFunctor_510_);
lean_dec(v_toApplicative_506_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_596_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___f_517_; lean_object* v___f_518_; lean_object* v___f_519_; lean_object* v___f_520_; lean_object* v___x_521_; lean_object* v___f_522_; lean_object* v___f_523_; lean_object* v___f_524_; lean_object* v___x_526_; 
v___f_517_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__1));
v___f_518_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__2));
lean_inc_ref(v_toFunctor_510_);
v___f_519_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_519_, 0, v_toFunctor_510_);
v___f_520_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_520_, 0, v_toFunctor_510_);
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v___f_519_);
lean_ctor_set(v___x_521_, 1, v___f_520_);
v___f_522_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_522_, 0, v_toSeqRight_513_);
v___f_523_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_523_, 0, v_toSeqLeft_512_);
v___f_524_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_524_, 0, v_toSeq_511_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 4, v___f_522_);
lean_ctor_set(v___x_515_, 3, v___f_523_);
lean_ctor_set(v___x_515_, 2, v___f_524_);
lean_ctor_set(v___x_515_, 1, v___f_517_);
lean_ctor_set(v___x_515_, 0, v___x_521_);
v___x_526_ = v___x_515_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v___f_517_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v___f_524_);
lean_ctor_set(v_reuseFailAlloc_595_, 3, v___f_523_);
lean_ctor_set(v_reuseFailAlloc_595_, 4, v___f_522_);
v___x_526_ = v_reuseFailAlloc_595_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_528_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v___f_518_);
lean_ctor_set(v___x_508_, 0, v___x_526_);
v___x_528_ = v___x_508_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v___f_518_);
v___x_528_ = v_reuseFailAlloc_594_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_529_; lean_object* v_toApplicative_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_592_; 
v___x_529_ = l_StateRefT_x27_instMonad___redArg(v___x_528_);
v_toApplicative_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_592_ == 0)
{
lean_object* v_unused_593_; 
v_unused_593_ = lean_ctor_get(v___x_529_, 1);
lean_dec(v_unused_593_);
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_592_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_toApplicative_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_592_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_toFunctor_534_; lean_object* v_toSeq_535_; lean_object* v_toSeqLeft_536_; lean_object* v_toSeqRight_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_590_; 
v_toFunctor_534_ = lean_ctor_get(v_toApplicative_530_, 0);
v_toSeq_535_ = lean_ctor_get(v_toApplicative_530_, 2);
v_toSeqLeft_536_ = lean_ctor_get(v_toApplicative_530_, 3);
v_toSeqRight_537_ = lean_ctor_get(v_toApplicative_530_, 4);
v_isSharedCheck_590_ = !lean_is_exclusive(v_toApplicative_530_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; 
v_unused_591_ = lean_ctor_get(v_toApplicative_530_, 1);
lean_dec(v_unused_591_);
v___x_539_ = v_toApplicative_530_;
v_isShared_540_ = v_isSharedCheck_590_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_toSeqRight_537_);
lean_inc(v_toSeqLeft_536_);
lean_inc(v_toSeq_535_);
lean_inc(v_toFunctor_534_);
lean_dec(v_toApplicative_530_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_590_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___f_541_; lean_object* v___f_542_; lean_object* v___f_543_; lean_object* v___f_544_; lean_object* v___x_545_; lean_object* v___f_546_; lean_object* v___f_547_; lean_object* v___f_548_; lean_object* v___x_550_; 
v___f_541_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__3));
v___f_542_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__4));
lean_inc_ref(v_toFunctor_534_);
v___f_543_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_543_, 0, v_toFunctor_534_);
v___f_544_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_544_, 0, v_toFunctor_534_);
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v___f_543_);
lean_ctor_set(v___x_545_, 1, v___f_544_);
v___f_546_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_546_, 0, v_toSeqRight_537_);
v___f_547_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_547_, 0, v_toSeqLeft_536_);
v___f_548_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_548_, 0, v_toSeq_535_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 4, v___f_546_);
lean_ctor_set(v___x_539_, 3, v___f_547_);
lean_ctor_set(v___x_539_, 2, v___f_548_);
lean_ctor_set(v___x_539_, 1, v___f_541_);
lean_ctor_set(v___x_539_, 0, v___x_545_);
v___x_550_ = v___x_539_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v___f_541_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v___f_548_);
lean_ctor_set(v_reuseFailAlloc_589_, 3, v___f_547_);
lean_ctor_set(v_reuseFailAlloc_589_, 4, v___f_546_);
v___x_550_ = v_reuseFailAlloc_589_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_552_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 1, v___f_542_);
lean_ctor_set(v___x_532_, 0, v___x_550_);
v___x_552_ = v___x_532_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___f_542_);
v___x_552_ = v_reuseFailAlloc_588_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; lean_object* v_toApplicative_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_586_; 
v___x_553_ = l_StateRefT_x27_instMonad___redArg(v___x_552_);
v_toApplicative_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_586_ == 0)
{
lean_object* v_unused_587_; 
v_unused_587_ = lean_ctor_get(v___x_553_, 1);
lean_dec(v_unused_587_);
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_586_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_toApplicative_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_586_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v_toFunctor_558_; lean_object* v_toSeq_559_; lean_object* v_toSeqLeft_560_; lean_object* v_toSeqRight_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_584_; 
v_toFunctor_558_ = lean_ctor_get(v_toApplicative_554_, 0);
v_toSeq_559_ = lean_ctor_get(v_toApplicative_554_, 2);
v_toSeqLeft_560_ = lean_ctor_get(v_toApplicative_554_, 3);
v_toSeqRight_561_ = lean_ctor_get(v_toApplicative_554_, 4);
v_isSharedCheck_584_ = !lean_is_exclusive(v_toApplicative_554_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; 
v_unused_585_ = lean_ctor_get(v_toApplicative_554_, 1);
lean_dec(v_unused_585_);
v___x_563_ = v_toApplicative_554_;
v_isShared_564_ = v_isSharedCheck_584_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_toSeqRight_561_);
lean_inc(v_toSeqLeft_560_);
lean_inc(v_toSeq_559_);
lean_inc(v_toFunctor_558_);
lean_dec(v_toApplicative_554_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_584_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___f_565_; lean_object* v___f_566_; lean_object* v___f_567_; lean_object* v___f_568_; lean_object* v___x_569_; lean_object* v___f_570_; lean_object* v___f_571_; lean_object* v___f_572_; lean_object* v___x_574_; 
v___f_565_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__5));
v___f_566_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__6));
lean_inc_ref(v_toFunctor_558_);
v___f_567_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_567_, 0, v_toFunctor_558_);
v___f_568_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_568_, 0, v_toFunctor_558_);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v___f_567_);
lean_ctor_set(v___x_569_, 1, v___f_568_);
v___f_570_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_570_, 0, v_toSeqRight_561_);
v___f_571_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_571_, 0, v_toSeqLeft_560_);
v___f_572_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_572_, 0, v_toSeq_559_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 4, v___f_570_);
lean_ctor_set(v___x_563_, 3, v___f_571_);
lean_ctor_set(v___x_563_, 2, v___f_572_);
lean_ctor_set(v___x_563_, 1, v___f_565_);
lean_ctor_set(v___x_563_, 0, v___x_569_);
v___x_574_ = v___x_563_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v___f_565_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v___f_572_);
lean_ctor_set(v_reuseFailAlloc_583_, 3, v___f_571_);
lean_ctor_set(v_reuseFailAlloc_583_, 4, v___f_570_);
v___x_574_ = v_reuseFailAlloc_583_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_576_; 
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 1, v___f_566_);
lean_ctor_set(v___x_556_, 0, v___x_574_);
v___x_576_ = v___x_556_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v___f_566_);
v___x_576_ = v_reuseFailAlloc_582_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_10473__overap_580_; lean_object* v___x_581_; 
v___x_577_ = l_StateRefT_x27_instMonad___redArg(v___x_576_);
v___x_578_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_578_, 0, lean_box(0));
lean_closure_set(v___x_578_, 1, lean_box(0));
lean_closure_set(v___x_578_, 2, v___x_577_);
v___x_579_ = l_OptionT_instInhabitedOfPure___redArg(v___x_578_);
v___x_10473__overap_580_ = lean_panic_fn_borrowed(v___x_579_, v_msg_494_);
lean_dec(v___x_579_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc(v___y_498_);
lean_inc_ref(v___y_497_);
lean_inc(v___y_496_);
lean_inc_ref(v___y_495_);
v___x_581_ = lean_apply_9(v___x_10473__overap_580_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, lean_box(0));
return v___x_581_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___boxed(lean_object* v_msg_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(v_msg_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
return v_res_610_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_box(0);
v___x_612_ = l_Lean_mkSort(v___x_611_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0);
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__9));
v___x_641_ = l_Lean_stringToMessageData(v___x_640_);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_660_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__17));
v___x_661_ = lean_unsigned_to_nat(37u);
v___x_662_ = lean_unsigned_to_nat(45u);
v___x_663_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__16));
v___x_664_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15));
v___x_665_ = l_mkPanicMessageWithDecl(v___x_664_, v___x_663_, v___x_662_, v___x_661_, v___x_660_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(lean_object* v_P_666_, lean_object* v_QR_667_, lean_object* v_arg_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_QR_667_);
if (lean_obj_tag(v___x_681_) == 1)
{
lean_object* v_val_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_860_; 
v_val_682_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_860_ == 0)
{
v___x_684_ = v___x_681_;
v_isShared_685_ = v_isSharedCheck_860_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_val_682_);
lean_dec(v___x_681_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_860_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v_p_686_; 
v_p_686_ = lean_ctor_get(v_val_682_, 2);
lean_inc_ref(v_p_686_);
if (lean_obj_tag(v_p_686_) == 5)
{
lean_object* v_name_687_; lean_object* v_uniq_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_858_; 
v_name_687_ = lean_ctor_get(v_val_682_, 0);
v_uniq_688_ = lean_ctor_get(v_val_682_, 1);
v_isSharedCheck_858_ = !lean_is_exclusive(v_val_682_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v_val_682_, 2);
lean_dec(v_unused_859_);
v___x_690_ = v_val_682_;
v_isShared_691_ = v_isSharedCheck_858_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_uniq_688_);
lean_inc(v_name_687_);
lean_dec(v_val_682_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_858_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v_fn_692_; lean_object* v_arg_693_; lean_object* v___y_695_; 
v_fn_692_ = lean_ctor_get(v_p_686_, 0);
v_arg_693_ = lean_ctor_get(v_p_686_, 1);
lean_inc_ref(v_arg_693_);
if (lean_obj_tag(v_fn_692_) == 5)
{
lean_object* v_fn_705_; 
v_fn_705_ = lean_ctor_get(v_fn_692_, 0);
if (lean_obj_tag(v_fn_705_) == 5)
{
lean_object* v_fn_706_; 
v_fn_706_ = lean_ctor_get(v_fn_705_, 0);
if (lean_obj_tag(v_fn_706_) == 4)
{
lean_object* v_declName_707_; 
v_declName_707_ = lean_ctor_get(v_fn_706_, 0);
if (lean_obj_tag(v_declName_707_) == 1)
{
lean_object* v_pre_708_; 
v_pre_708_ = lean_ctor_get(v_declName_707_, 0);
if (lean_obj_tag(v_pre_708_) == 1)
{
lean_object* v_pre_709_; 
v_pre_709_ = lean_ctor_get(v_pre_708_, 0);
if (lean_obj_tag(v_pre_709_) == 1)
{
lean_object* v_pre_710_; 
v_pre_710_ = lean_ctor_get(v_pre_709_, 0);
if (lean_obj_tag(v_pre_710_) == 1)
{
lean_object* v_pre_711_; 
v_pre_711_ = lean_ctor_get(v_pre_710_, 0);
if (lean_obj_tag(v_pre_711_) == 0)
{
lean_object* v_arg_712_; lean_object* v_arg_713_; lean_object* v_us_714_; lean_object* v_str_715_; lean_object* v_str_716_; lean_object* v_str_717_; lean_object* v_str_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v_arg_712_ = lean_ctor_get(v_fn_692_, 1);
lean_inc_ref(v_arg_712_);
v_arg_713_ = lean_ctor_get(v_fn_705_, 1);
lean_inc_ref(v_arg_713_);
v_us_714_ = lean_ctor_get(v_fn_706_, 1);
v_str_715_ = lean_ctor_get(v_declName_707_, 1);
v_str_716_ = lean_ctor_get(v_pre_708_, 1);
v_str_717_ = lean_ctor_get(v_pre_709_, 1);
v_str_718_ = lean_ctor_get(v_pre_710_, 1);
v___x_719_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_720_ = lean_string_dec_eq(v_str_718_, v___x_719_);
if (v___x_720_ == 0)
{
lean_dec_ref(v_arg_713_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec_ref_known(v_p_686_, 2);
lean_dec(v_name_687_);
lean_del_object(v___x_684_);
lean_dec(v_arg_668_);
lean_dec_ref(v_P_666_);
goto v___jp_678_;
}
else
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_722_ = lean_string_dec_eq(v_str_717_, v___x_721_);
if (v___x_722_ == 0)
{
lean_dec_ref(v_arg_713_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec_ref_known(v_p_686_, 2);
lean_dec(v_name_687_);
lean_del_object(v___x_684_);
lean_dec(v_arg_668_);
lean_dec_ref(v_P_666_);
goto v___jp_678_;
}
else
{
lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_723_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_724_ = lean_string_dec_eq(v_str_716_, v___x_723_);
if (v___x_724_ == 0)
{
lean_dec_ref(v_arg_713_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec_ref_known(v_p_686_, 2);
lean_dec(v_name_687_);
lean_del_object(v___x_684_);
lean_dec(v_arg_668_);
lean_dec_ref(v_P_666_);
goto v___jp_678_;
}
else
{
lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_725_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__2));
v___x_726_ = lean_string_dec_eq(v_str_715_, v___x_725_);
if (v___x_726_ == 0)
{
lean_dec_ref(v_arg_713_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec_ref_known(v_p_686_, 2);
lean_dec(v_name_687_);
lean_del_object(v___x_684_);
lean_dec(v_arg_668_);
lean_dec_ref(v_P_666_);
goto v___jp_678_;
}
else
{
if (lean_obj_tag(v_us_714_) == 1)
{
lean_object* v_tail_727_; 
v_tail_727_ = lean_ctor_get(v_us_714_, 1);
if (lean_obj_tag(v_tail_727_) == 0)
{
lean_object* v_head_728_; lean_object* v___x_729_; uint8_t v___x_730_; lean_object* v___x_731_; 
v_head_728_ = lean_ctor_get(v_us_714_, 0);
lean_inc(v_head_728_);
v___x_729_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1);
v___x_730_ = 0;
v___x_731_ = l_Lean_Meta_mkFreshExprMVar(v___x_729_, v___x_730_, v_pre_711_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc_n(v_a_732_, 2);
lean_dec_ref_known(v___x_731_, 1);
v___x_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_733_, 0, v_a_732_);
v___x_734_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2));
v___x_735_ = lean_box(0);
v___x_736_ = l_Lean_Elab_Tactic_elabTermWithHoles(v_arg_668_, v___x_733_, v___x_734_, v___x_726_, v___x_735_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v_fst_738_; lean_object* v_snd_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_834_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref_known(v___x_736_, 1);
v_fst_738_ = lean_ctor_get(v_a_737_, 0);
v_snd_739_ = lean_ctor_get(v_a_737_, 1);
v_isSharedCheck_834_ = !lean_is_exclusive(v_a_737_);
if (v_isSharedCheck_834_ == 0)
{
v___x_741_ = v_a_737_;
v_isShared_742_ = v_isSharedCheck_834_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_snd_739_);
lean_inc(v_fst_738_);
lean_dec(v_a_737_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_834_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v_00_u03c6_747_; lean_object* v_h_u03c6_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___x_817_; 
v___x_743_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4));
lean_inc_ref(v_us_714_);
v___x_744_ = l_Lean_mkConst(v___x_743_, v_us_714_);
lean_inc(v_a_732_);
lean_inc_ref(v_arg_712_);
lean_inc_ref(v_arg_713_);
v___x_745_ = l_Lean_mkApp3(v___x_744_, v_arg_713_, v_arg_712_, v_a_732_);
v___x_817_ = l_Lean_Meta_synthInstance_x3f(v___x_745_, v___x_735_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_817_, 1);
if (lean_obj_tag(v_a_818_) == 1)
{
lean_object* v_val_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_val_819_ = lean_ctor_get(v_a_818_, 0);
lean_inc(v_val_819_);
lean_dec_ref_known(v_a_818_, 1);
v___x_820_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12));
lean_inc_ref_n(v_us_714_, 2);
v___x_821_ = l_Lean_mkConst(v___x_820_, v_us_714_);
lean_inc_ref_n(v_arg_712_, 2);
lean_inc_ref_n(v_arg_713_, 2);
v___x_822_ = l_Lean_mkApp5(v___x_821_, v_arg_713_, v_a_732_, v_arg_712_, v_val_819_, v_fst_738_);
v___x_823_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14));
v___x_824_ = l_Lean_mkConst(v___x_823_, v_us_714_);
v___x_825_ = l_Lean_mkAppB(v___x_824_, v_arg_713_, v_arg_712_);
v_00_u03c6_747_ = v___x_825_;
v_h_u03c6_748_ = v___x_822_;
v___y_749_ = v_a_670_;
v___y_750_ = v_a_673_;
v___y_751_ = v_a_674_;
v___y_752_ = v_a_675_;
v___y_753_ = v_a_676_;
goto v___jp_746_;
}
else
{
lean_dec(v_a_818_);
v_00_u03c6_747_ = v_a_732_;
v_h_u03c6_748_ = v_fst_738_;
v___y_749_ = v_a_670_;
v___y_750_ = v_a_673_;
v___y_751_ = v_a_674_;
v___y_752_ = v_a_675_;
v___y_753_ = v_a_676_;
goto v___jp_746_;
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_del_object(v___x_741_);
lean_dec(v_snd_739_);
lean_dec(v_fst_738_);
lean_dec(v_a_732_);
lean_dec(v_head_728_);
lean_dec_ref(v_arg_713_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec(v_name_687_);
lean_dec_ref_known(v_p_686_, 2);
lean_del_object(v___x_684_);
lean_dec_ref(v_P_666_);
v_a_826_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_817_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_817_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
v___jp_746_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_754_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6));
lean_inc_ref(v_us_714_);
v___x_755_ = l_Lean_mkConst(v___x_754_, v_us_714_);
lean_inc_ref(v_arg_712_);
lean_inc_ref(v_arg_713_);
lean_inc_ref(v_00_u03c6_747_);
v___x_756_ = l_Lean_mkApp3(v___x_755_, v_00_u03c6_747_, v_arg_713_, v_arg_712_);
v___x_757_ = l_Lean_Meta_synthInstance_x3f(v___x_756_, v___x_735_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_808_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_808_ == 0)
{
v___x_760_ = v___x_757_;
v_isShared_761_ = v_isSharedCheck_808_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_808_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
if (lean_obj_tag(v_a_758_) == 1)
{
lean_object* v_val_762_; lean_object* v___x_763_; 
lean_del_object(v___x_760_);
v_val_762_ = lean_ctor_get(v_a_758_, 0);
lean_inc(v_val_762_);
lean_dec_ref_known(v_a_758_, 1);
v___x_763_ = l_Lean_Elab_Tactic_pushGoals___redArg(v_snd_739_, v___y_749_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_toCold_764_; lean_object* v_options_765_; lean_object* v_inheritedTraceOptions_766_; uint8_t v_hasTrace_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
lean_dec_ref_known(v___x_763_, 1);
v_toCold_764_ = lean_ctor_get(v___y_752_, 0);
v_options_765_ = lean_ctor_get(v_toCold_764_, 2);
v_inheritedTraceOptions_766_ = lean_ctor_get(v_toCold_764_, 11);
v_hasTrace_767_ = lean_ctor_get_uint8(v_options_765_, sizeof(void*)*1);
v___x_768_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8));
lean_inc_ref(v_us_714_);
v___x_769_ = l_Lean_mkConst(v___x_768_, v_us_714_);
lean_inc_ref(v_arg_693_);
lean_inc_ref(v_arg_712_);
lean_inc_ref(v_P_666_);
lean_inc_ref(v_arg_713_);
v___x_770_ = l_Lean_mkApp7(v___x_769_, v_arg_713_, v_00_u03c6_747_, v_P_666_, v_arg_712_, v_arg_693_, v_val_762_, v_h_u03c6_748_);
if (v_hasTrace_767_ == 0)
{
lean_del_object(v___x_741_);
lean_dec(v_head_728_);
lean_dec_ref(v_arg_713_);
lean_dec_ref(v_arg_712_);
lean_dec_ref_known(v_p_686_, 2);
lean_dec_ref(v_P_666_);
v___y_695_ = v___x_770_;
goto v___jp_694_;
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_771_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_772_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11);
v___x_773_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_766_, v_options_765_, v___x_772_);
if (v___x_773_ == 0)
{
lean_del_object(v___x_741_);
lean_dec(v_head_728_);
lean_dec_ref(v_arg_713_);
lean_dec_ref(v_arg_712_);
lean_dec_ref_known(v_p_686_, 2);
lean_dec_ref(v_P_666_);
v___y_695_ = v___x_770_;
goto v___jp_694_;
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_774_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10);
v___x_775_ = l_Lean_MessageData_ofExpr(v_p_686_);
if (v_isShared_742_ == 0)
{
lean_ctor_set_tag(v___x_741_, 7);
lean_ctor_set(v___x_741_, 1, v___x_775_);
lean_ctor_set(v___x_741_, 0, v___x_774_);
v___x_777_ = v___x_741_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v___x_775_);
v___x_777_ = v_reuseFailAlloc_796_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_778_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_777_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = l_Lean_MessageData_ofExpr(v_arg_712_);
v___x_781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15);
v___x_783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_781_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
lean_inc_ref(v_arg_693_);
v___x_784_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_head_728_, v_arg_713_, v_P_666_, v_arg_693_);
v___x_785_ = l_Lean_MessageData_ofExpr(v___x_784_);
v___x_786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_783_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v___x_771_, v___x_786_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_dec_ref_known(v___x_787_, 1);
v___y_695_ = v___x_770_;
goto v___jp_694_;
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec_ref(v___x_770_);
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec(v_name_687_);
lean_del_object(v___x_684_);
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec(v_val_762_);
lean_dec_ref(v_h_u03c6_748_);
lean_dec_ref(v_00_u03c6_747_);
lean_del_object(v___x_741_);
lean_dec(v_head_728_);
lean_dec_ref(v_arg_713_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec(v_name_687_);
lean_dec_ref_known(v_p_686_, 2);
lean_del_object(v___x_684_);
lean_dec_ref(v_P_666_);
v_a_797_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_763_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_763_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
else
{
lean_object* v___x_806_; 
lean_dec(v_a_758_);
lean_dec_ref(v_h_u03c6_748_);
lean_dec_ref(v_00_u03c6_747_);
lean_del_object(v___x_741_);
lean_dec(v_snd_739_);
lean_dec(v_head_728_);
lean_dec_ref(v_arg_713_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec(v_name_687_);
lean_dec_ref_known(v_p_686_, 2);
lean_del_object(v___x_684_);
lean_dec_ref(v_P_666_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v___x_735_);
v___x_806_ = v___x_760_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_735_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v_h_u03c6_748_);
lean_dec_ref(v_00_u03c6_747_);
lean_del_object(v___x_741_);
lean_dec(v_snd_739_);
lean_dec(v_head_728_);
lean_dec_ref(v_arg_713_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec(v_name_687_);
lean_dec_ref_known(v_p_686_, 2);
lean_del_object(v___x_684_);
lean_dec_ref(v_P_666_);
v_a_809_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_757_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_757_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
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
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_849_; 
lean_dec(v_a_732_);
lean_dec(v_head_728_);
lean_dec_ref(v_arg_713_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec(v_name_687_);
lean_dec_ref_known(v_p_686_, 2);
lean_del_object(v___x_684_);
lean_dec_ref(v_P_666_);
v_a_835_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_849_ == 0)
{
v___x_837_ = v___x_736_;
v_isShared_838_ = v_isSharedCheck_849_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_736_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_849_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
uint8_t v___y_840_; uint8_t v___x_847_; 
v___x_847_ = l_Lean_Exception_isInterrupt(v_a_835_);
if (v___x_847_ == 0)
{
uint8_t v___x_848_; 
lean_inc(v_a_835_);
v___x_848_ = l_Lean_Exception_isRuntime(v_a_835_);
v___y_840_ = v___x_848_;
goto v___jp_839_;
}
else
{
v___y_840_ = v___x_847_;
goto v___jp_839_;
}
v___jp_839_:
{
if (v___y_840_ == 0)
{
lean_object* v___x_842_; 
lean_dec(v_a_835_);
if (v_isShared_838_ == 0)
{
lean_ctor_set_tag(v___x_837_, 0);
lean_ctor_set(v___x_837_, 0, v___x_735_);
v___x_842_ = v___x_837_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_735_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
else
{
lean_object* v___x_845_; 
if (v_isShared_838_ == 0)
{
v___x_845_ = v___x_837_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_835_);
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
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec(v_head_728_);
lean_dec_ref(v_arg_713_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec_ref_known(v_p_686_, 2);
lean_dec(v_name_687_);
lean_del_object(v___x_684_);
lean_dec(v_arg_668_);
lean_dec_ref(v_P_666_);
v_a_850_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_731_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_731_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
else
{
lean_dec_ref(v_arg_713_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec_ref_known(v_p_686_, 2);
lean_dec(v_name_687_);
lean_del_object(v___x_684_);
lean_dec(v_arg_668_);
lean_dec_ref(v_P_666_);
goto v___jp_678_;
}
}
else
{
lean_dec_ref(v_arg_713_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec_ref_known(v_p_686_, 2);
lean_dec(v_name_687_);
lean_del_object(v___x_684_);
lean_dec(v_arg_668_);
lean_dec_ref(v_P_666_);
goto v___jp_678_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec_ref_known(v_p_686_, 2);
lean_dec(v_name_687_);
lean_del_object(v___x_684_);
lean_dec(v_arg_668_);
lean_dec_ref(v_P_666_);
goto v___jp_678_;
}
}
else
{
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec_ref_known(v_p_686_, 2);
lean_dec(v_name_687_);
lean_del_object(v___x_684_);
lean_dec(v_arg_668_);
lean_dec_ref(v_P_666_);
goto v___jp_678_;
}
}
else
{
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec_ref_known(v_p_686_, 2);
lean_dec(v_name_687_);
lean_del_object(v___x_684_);
lean_dec(v_arg_668_);
lean_dec_ref(v_P_666_);
goto v___jp_678_;
}
}
else
{
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec_ref_known(v_p_686_, 2);
lean_dec(v_name_687_);
lean_del_object(v___x_684_);
lean_dec(v_arg_668_);
lean_dec_ref(v_P_666_);
goto v___jp_678_;
}
}
else
{
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec_ref_known(v_p_686_, 2);
lean_dec(v_name_687_);
lean_del_object(v___x_684_);
lean_dec(v_arg_668_);
lean_dec_ref(v_P_666_);
goto v___jp_678_;
}
}
else
{
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec_ref_known(v_p_686_, 2);
lean_dec(v_name_687_);
lean_del_object(v___x_684_);
lean_dec(v_arg_668_);
lean_dec_ref(v_P_666_);
goto v___jp_678_;
}
}
else
{
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec_ref_known(v_p_686_, 2);
lean_dec(v_name_687_);
lean_del_object(v___x_684_);
lean_dec(v_arg_668_);
lean_dec_ref(v_P_666_);
goto v___jp_678_;
}
}
else
{
lean_dec_ref(v_arg_693_);
lean_del_object(v___x_690_);
lean_dec(v_uniq_688_);
lean_dec_ref_known(v_p_686_, 2);
lean_dec(v_name_687_);
lean_del_object(v___x_684_);
lean_dec(v_arg_668_);
lean_dec_ref(v_P_666_);
goto v___jp_678_;
}
v___jp_694_:
{
lean_object* v___x_697_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 2, v_arg_693_);
v___x_697_ = v___x_690_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_name_687_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_uniq_688_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_arg_693_);
v___x_697_ = v_reuseFailAlloc_704_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_698_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_697_);
v___x_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v___y_695_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_699_);
v___x_701_ = v___x_684_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_699_);
v___x_701_ = v_reuseFailAlloc_703_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_702_; 
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
return v___x_702_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_686_);
lean_del_object(v___x_684_);
lean_dec(v_val_682_);
lean_dec(v_arg_668_);
lean_dec_ref(v_P_666_);
goto v___jp_678_;
}
}
}
else
{
lean_object* v___x_861_; lean_object* v___x_862_; 
lean_dec(v___x_681_);
lean_dec(v_arg_668_);
lean_dec_ref(v_P_666_);
v___x_861_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18);
v___x_862_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(v___x_861_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
return v___x_862_;
}
v___jp_678_:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_box(0);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___boxed(lean_object* v_P_863_, lean_object* v_QR_864_, lean_object* v_arg_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(v_P_863_, v_QR_864_, v_arg_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
return v_res_875_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__2));
v___x_886_ = l_Lean_stringToMessageData(v___x_885_);
return v___x_886_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_889_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__5));
v___x_890_ = lean_unsigned_to_nat(36u);
v___x_891_ = lean_unsigned_to_nat(73u);
v___x_892_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__4));
v___x_893_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15));
v___x_894_ = l_mkPanicMessageWithDecl(v___x_893_, v___x_892_, v___x_891_, v___x_890_, v___x_889_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(lean_object* v_P_895_, lean_object* v_00_u03a8_896_, lean_object* v_arg_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_00_u03a8_896_);
if (lean_obj_tag(v___x_910_) == 1)
{
lean_object* v_val_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_1046_; 
v_val_911_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_913_ = v___x_910_;
v_isShared_914_ = v_isSharedCheck_1046_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_val_911_);
lean_dec(v___x_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_1046_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v_p_915_; 
v_p_915_ = lean_ctor_get(v_val_911_, 2);
lean_inc_ref(v_p_915_);
if (lean_obj_tag(v_p_915_) == 5)
{
lean_object* v_fn_916_; 
v_fn_916_ = lean_ctor_get(v_p_915_, 0);
if (lean_obj_tag(v_fn_916_) == 5)
{
lean_object* v_fn_917_; 
v_fn_917_ = lean_ctor_get(v_fn_916_, 0);
if (lean_obj_tag(v_fn_917_) == 5)
{
lean_object* v_fn_918_; 
v_fn_918_ = lean_ctor_get(v_fn_917_, 0);
if (lean_obj_tag(v_fn_918_) == 4)
{
lean_object* v_declName_919_; 
v_declName_919_ = lean_ctor_get(v_fn_918_, 0);
if (lean_obj_tag(v_declName_919_) == 1)
{
lean_object* v_pre_920_; 
v_pre_920_ = lean_ctor_get(v_declName_919_, 0);
if (lean_obj_tag(v_pre_920_) == 1)
{
lean_object* v_pre_921_; 
v_pre_921_ = lean_ctor_get(v_pre_920_, 0);
if (lean_obj_tag(v_pre_921_) == 1)
{
lean_object* v_pre_922_; 
v_pre_922_ = lean_ctor_get(v_pre_921_, 0);
if (lean_obj_tag(v_pre_922_) == 1)
{
lean_object* v_pre_923_; 
v_pre_923_ = lean_ctor_get(v_pre_922_, 0);
if (lean_obj_tag(v_pre_923_) == 0)
{
lean_object* v_name_924_; lean_object* v_uniq_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_1044_; 
v_name_924_ = lean_ctor_get(v_val_911_, 0);
v_uniq_925_ = lean_ctor_get(v_val_911_, 1);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_val_911_);
if (v_isSharedCheck_1044_ == 0)
{
lean_object* v_unused_1045_; 
v_unused_1045_ = lean_ctor_get(v_val_911_, 2);
lean_dec(v_unused_1045_);
v___x_927_ = v_val_911_;
v_isShared_928_ = v_isSharedCheck_1044_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_uniq_925_);
lean_inc(v_name_924_);
lean_dec(v_val_911_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_1044_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v_arg_929_; lean_object* v_arg_930_; lean_object* v_arg_931_; lean_object* v_us_932_; lean_object* v_str_933_; lean_object* v_str_934_; lean_object* v_str_935_; lean_object* v_str_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
v_arg_929_ = lean_ctor_get(v_p_915_, 1);
v_arg_930_ = lean_ctor_get(v_fn_916_, 1);
lean_inc_ref(v_arg_930_);
v_arg_931_ = lean_ctor_get(v_fn_917_, 1);
v_us_932_ = lean_ctor_get(v_fn_918_, 1);
v_str_933_ = lean_ctor_get(v_declName_919_, 1);
v_str_934_ = lean_ctor_get(v_pre_920_, 1);
v_str_935_ = lean_ctor_get(v_pre_921_, 1);
v_str_936_ = lean_ctor_get(v_pre_922_, 1);
v___x_937_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_938_ = lean_string_dec_eq(v_str_936_, v___x_937_);
if (v___x_938_ == 0)
{
lean_dec_ref(v_arg_930_);
lean_del_object(v___x_927_);
lean_dec(v_uniq_925_);
lean_dec(v_name_924_);
lean_dec_ref_known(v_p_915_, 2);
lean_del_object(v___x_913_);
lean_dec(v_arg_897_);
lean_dec_ref(v_P_895_);
goto v___jp_907_;
}
else
{
lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_939_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_940_ = lean_string_dec_eq(v_str_935_, v___x_939_);
if (v___x_940_ == 0)
{
lean_dec_ref(v_arg_930_);
lean_del_object(v___x_927_);
lean_dec(v_uniq_925_);
lean_dec(v_name_924_);
lean_dec_ref_known(v_p_915_, 2);
lean_del_object(v___x_913_);
lean_dec(v_arg_897_);
lean_dec_ref(v_P_895_);
goto v___jp_907_;
}
else
{
lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_941_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_942_ = lean_string_dec_eq(v_str_934_, v___x_941_);
if (v___x_942_ == 0)
{
lean_dec_ref(v_arg_930_);
lean_del_object(v___x_927_);
lean_dec(v_uniq_925_);
lean_dec(v_name_924_);
lean_dec_ref_known(v_p_915_, 2);
lean_del_object(v___x_913_);
lean_dec(v_arg_897_);
lean_dec_ref(v_P_895_);
goto v___jp_907_;
}
else
{
lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_943_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__0));
v___x_944_ = lean_string_dec_eq(v_str_933_, v___x_943_);
if (v___x_944_ == 0)
{
lean_dec_ref(v_arg_930_);
lean_del_object(v___x_927_);
lean_dec(v_uniq_925_);
lean_dec(v_name_924_);
lean_dec_ref_known(v_p_915_, 2);
lean_del_object(v___x_913_);
lean_dec(v_arg_897_);
lean_dec_ref(v_P_895_);
goto v___jp_907_;
}
else
{
if (lean_obj_tag(v_us_932_) == 1)
{
lean_object* v_tail_945_; 
v_tail_945_ = lean_ctor_get(v_us_932_, 1);
lean_inc(v_tail_945_);
if (lean_obj_tag(v_tail_945_) == 1)
{
lean_object* v_tail_946_; 
v_tail_946_ = lean_ctor_get(v_tail_945_, 1);
if (lean_obj_tag(v_tail_946_) == 0)
{
lean_object* v_head_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_1042_; 
v_head_947_ = lean_ctor_get(v_tail_945_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_tail_945_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; 
v_unused_1043_ = lean_ctor_get(v_tail_945_, 1);
lean_dec(v_unused_1043_);
v___x_949_ = v_tail_945_;
v_isShared_950_ = v_isSharedCheck_1042_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_head_947_);
lean_dec(v_tail_945_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_1042_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
lean_inc_ref(v_arg_931_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v_arg_931_);
v___x_952_ = v___x_913_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_arg_931_);
v___x_952_ = v_reuseFailAlloc_1041_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_953_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2));
v___x_954_ = lean_box(0);
v___x_955_ = l_Lean_Elab_Tactic_elabTermWithHoles(v_arg_897_, v___x_952_, v___x_953_, v___x_944_, v___x_954_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v_fst_957_; lean_object* v_snd_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_1025_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref_known(v___x_955_, 1);
v_fst_957_ = lean_ctor_get(v_a_956_, 0);
v_snd_958_ = lean_ctor_get(v_a_956_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_a_956_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_960_ = v_a_956_;
v_isShared_961_ = v_isSharedCheck_1025_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_snd_958_);
lean_inc(v_fst_957_);
lean_dec(v_a_956_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_1025_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_Elab_Tactic_pushGoals___redArg(v_snd_958_, v_a_899_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_1015_; 
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_1015_ == 0)
{
lean_object* v_unused_1016_; 
v_unused_1016_ = lean_ctor_get(v___x_962_, 0);
lean_dec(v_unused_1016_);
v___x_964_ = v___x_962_;
v_isShared_965_ = v_isSharedCheck_1015_;
goto v_resetjp_963_;
}
else
{
lean_dec(v___x_962_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_1015_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v_toCold_966_; lean_object* v_options_967_; lean_object* v_inheritedTraceOptions_968_; uint8_t v_hasTrace_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_toCold_966_ = lean_ctor_get(v_a_904_, 0);
v_options_967_ = lean_ctor_get(v_toCold_966_, 2);
v_inheritedTraceOptions_968_ = lean_ctor_get(v_toCold_966_, 11);
v_hasTrace_969_ = lean_ctor_get_uint8(v_options_967_, sizeof(void*)*1);
v___x_970_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1));
lean_inc_ref(v_us_932_);
v___x_971_ = l_Lean_mkConst(v___x_970_, v_us_932_);
lean_inc_n(v_fst_957_, 2);
lean_inc_ref(v_P_895_);
lean_inc_ref_n(v_arg_929_, 2);
lean_inc_ref(v_arg_930_);
lean_inc_ref(v_arg_931_);
v___x_972_ = l_Lean_mkApp5(v___x_971_, v_arg_931_, v_arg_930_, v_arg_929_, v_P_895_, v_fst_957_);
v___x_973_ = lean_unsigned_to_nat(1u);
v___x_974_ = lean_mk_empty_array_with_capacity(v___x_973_);
v___x_975_ = lean_array_push(v___x_974_, v_fst_957_);
v___x_976_ = l_Lean_Expr_beta(v_arg_929_, v___x_975_);
if (v_hasTrace_969_ == 0)
{
lean_dec(v_fst_957_);
lean_del_object(v___x_949_);
lean_dec(v_head_947_);
lean_dec_ref(v_arg_930_);
lean_dec_ref_known(v_p_915_, 2);
lean_dec_ref(v_P_895_);
goto v___jp_977_;
}
else
{
lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_989_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_990_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11);
v___x_991_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_968_, v_options_967_, v___x_990_);
if (v___x_991_ == 0)
{
lean_dec(v_fst_957_);
lean_del_object(v___x_949_);
lean_dec(v_head_947_);
lean_dec_ref(v_arg_930_);
lean_dec_ref_known(v_p_915_, 2);
lean_dec_ref(v_P_895_);
goto v___jp_977_;
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_992_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3);
v___x_993_ = l_Lean_MessageData_ofExpr(v_p_915_);
if (v_isShared_950_ == 0)
{
lean_ctor_set_tag(v___x_949_, 7);
lean_ctor_set(v___x_949_, 1, v___x_993_);
lean_ctor_set(v___x_949_, 0, v___x_992_);
v___x_995_ = v___x_949_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v___x_993_);
v___x_995_ = v_reuseFailAlloc_1014_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_996_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = l_Lean_MessageData_ofExpr(v_fst_957_);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
lean_inc_ref(v___x_976_);
v___x_1002_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_head_947_, v_arg_930_, v_P_895_, v___x_976_);
v___x_1003_ = l_Lean_MessageData_ofExpr(v___x_1002_);
v___x_1004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1001_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v___x_989_, v___x_1004_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_dec_ref_known(v___x_1005_, 1);
goto v___jp_977_;
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec_ref(v___x_976_);
lean_dec_ref(v___x_972_);
lean_del_object(v___x_964_);
lean_del_object(v___x_960_);
lean_del_object(v___x_927_);
lean_dec(v_uniq_925_);
lean_dec(v_name_924_);
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
}
v___jp_977_:
{
lean_object* v___x_979_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 2, v___x_976_);
v___x_979_ = v___x_927_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_name_924_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_uniq_925_);
lean_ctor_set(v_reuseFailAlloc_988_, 2, v___x_976_);
v___x_979_ = v_reuseFailAlloc_988_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_980_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_979_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 1, v___x_972_);
lean_ctor_set(v___x_960_, 0, v___x_980_);
v___x_982_ = v___x_960_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_972_);
v___x_982_ = v_reuseFailAlloc_987_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_983_);
v___x_985_ = v___x_964_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_del_object(v___x_960_);
lean_dec(v_fst_957_);
lean_del_object(v___x_949_);
lean_dec(v_head_947_);
lean_dec_ref(v_arg_930_);
lean_del_object(v___x_927_);
lean_dec(v_uniq_925_);
lean_dec(v_name_924_);
lean_dec_ref_known(v_p_915_, 2);
lean_dec_ref(v_P_895_);
v_a_1017_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_962_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_962_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1040_; 
lean_del_object(v___x_949_);
lean_dec(v_head_947_);
lean_dec_ref(v_arg_930_);
lean_del_object(v___x_927_);
lean_dec(v_uniq_925_);
lean_dec(v_name_924_);
lean_dec_ref_known(v_p_915_, 2);
lean_dec_ref(v_P_895_);
v_a_1026_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1028_ = v___x_955_;
v_isShared_1029_ = v_isSharedCheck_1040_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_955_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1040_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
uint8_t v___y_1031_; uint8_t v___x_1038_; 
v___x_1038_ = l_Lean_Exception_isInterrupt(v_a_1026_);
if (v___x_1038_ == 0)
{
uint8_t v___x_1039_; 
lean_inc(v_a_1026_);
v___x_1039_ = l_Lean_Exception_isRuntime(v_a_1026_);
v___y_1031_ = v___x_1039_;
goto v___jp_1030_;
}
else
{
v___y_1031_ = v___x_1038_;
goto v___jp_1030_;
}
v___jp_1030_:
{
if (v___y_1031_ == 0)
{
lean_object* v___x_1033_; 
lean_dec(v_a_1026_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set_tag(v___x_1028_, 0);
lean_ctor_set(v___x_1028_, 0, v___x_954_);
v___x_1033_ = v___x_1028_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_954_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
else
{
lean_object* v___x_1036_; 
if (v_isShared_1029_ == 0)
{
v___x_1036_ = v___x_1028_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1026_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
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
lean_dec_ref_known(v_tail_945_, 2);
lean_dec_ref(v_arg_930_);
lean_del_object(v___x_927_);
lean_dec(v_uniq_925_);
lean_dec(v_name_924_);
lean_dec_ref_known(v_p_915_, 2);
lean_del_object(v___x_913_);
lean_dec(v_arg_897_);
lean_dec_ref(v_P_895_);
goto v___jp_907_;
}
}
else
{
lean_dec(v_tail_945_);
lean_dec_ref(v_arg_930_);
lean_del_object(v___x_927_);
lean_dec(v_uniq_925_);
lean_dec(v_name_924_);
lean_dec_ref_known(v_p_915_, 2);
lean_del_object(v___x_913_);
lean_dec(v_arg_897_);
lean_dec_ref(v_P_895_);
goto v___jp_907_;
}
}
else
{
lean_dec_ref(v_arg_930_);
lean_del_object(v___x_927_);
lean_dec(v_uniq_925_);
lean_dec(v_name_924_);
lean_dec_ref_known(v_p_915_, 2);
lean_del_object(v___x_913_);
lean_dec(v_arg_897_);
lean_dec_ref(v_P_895_);
goto v___jp_907_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_p_915_, 2);
lean_del_object(v___x_913_);
lean_dec(v_val_911_);
lean_dec(v_arg_897_);
lean_dec_ref(v_P_895_);
goto v___jp_907_;
}
}
else
{
lean_dec_ref_known(v_p_915_, 2);
lean_del_object(v___x_913_);
lean_dec(v_val_911_);
lean_dec(v_arg_897_);
lean_dec_ref(v_P_895_);
goto v___jp_907_;
}
}
else
{
lean_dec_ref_known(v_p_915_, 2);
lean_del_object(v___x_913_);
lean_dec(v_val_911_);
lean_dec(v_arg_897_);
lean_dec_ref(v_P_895_);
goto v___jp_907_;
}
}
else
{
lean_dec_ref_known(v_p_915_, 2);
lean_del_object(v___x_913_);
lean_dec(v_val_911_);
lean_dec(v_arg_897_);
lean_dec_ref(v_P_895_);
goto v___jp_907_;
}
}
else
{
lean_dec_ref_known(v_p_915_, 2);
lean_del_object(v___x_913_);
lean_dec(v_val_911_);
lean_dec(v_arg_897_);
lean_dec_ref(v_P_895_);
goto v___jp_907_;
}
}
else
{
lean_dec_ref_known(v_p_915_, 2);
lean_del_object(v___x_913_);
lean_dec(v_val_911_);
lean_dec(v_arg_897_);
lean_dec_ref(v_P_895_);
goto v___jp_907_;
}
}
else
{
lean_dec_ref_known(v_p_915_, 2);
lean_del_object(v___x_913_);
lean_dec(v_val_911_);
lean_dec(v_arg_897_);
lean_dec_ref(v_P_895_);
goto v___jp_907_;
}
}
else
{
lean_dec_ref_known(v_p_915_, 2);
lean_del_object(v___x_913_);
lean_dec(v_val_911_);
lean_dec(v_arg_897_);
lean_dec_ref(v_P_895_);
goto v___jp_907_;
}
}
else
{
lean_dec_ref(v_p_915_);
lean_del_object(v___x_913_);
lean_dec(v_val_911_);
lean_dec(v_arg_897_);
lean_dec_ref(v_P_895_);
goto v___jp_907_;
}
}
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_dec(v___x_910_);
lean_dec(v_arg_897_);
lean_dec_ref(v_P_895_);
v___x_1047_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6);
v___x_1048_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(v___x_1047_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
return v___x_1048_;
}
v___jp_907_:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_box(0);
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
return v___x_909_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___boxed(lean_object* v_P_1049_, lean_object* v_00_u03a8_1050_, lean_object* v_arg_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(v_P_1049_, v_00_u03a8_1050_, v_arg_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
return v_res_1061_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = lean_box(0);
v___x_1063_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v___x_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg(){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0);
v___x_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___boxed(lean_object* v___y_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0(lean_object* v_00_u03b1_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___boxed(lean_object* v_00_u03b1_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0(v_00_u03b1_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(lean_object* v_msg_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v___f_1103_; lean_object* v___x_5045__overap_1104_; lean_object* v___x_1105_; 
v___f_1103_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3___closed__0));
v___x_5045__overap_1104_ = lean_panic_fn_borrowed(v___f_1103_, v_msg_1093_);
lean_inc(v___y_1101_);
lean_inc_ref(v___y_1100_);
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1096_);
lean_inc(v___y_1095_);
lean_inc_ref(v___y_1094_);
v___x_1105_ = lean_apply_9(v___x_5045__overap_1104_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, lean_box(0));
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3___boxed(lean_object* v_msg_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(v_msg_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0(lean_object* v_x_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; 
lean_inc(v___y_1121_);
lean_inc_ref(v___y_1120_);
lean_inc(v___y_1119_);
lean_inc_ref(v___y_1118_);
v___x_1127_ = lean_apply_9(v_x_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, lean_box(0));
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0___boxed(lean_object* v_x_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0(v_x_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(lean_object* v_mvarId_1139_, lean_object* v_x_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___f_1150_; lean_object* v___x_1151_; 
lean_inc(v___y_1144_);
lean_inc_ref(v___y_1143_);
lean_inc(v___y_1142_);
lean_inc_ref(v___y_1141_);
v___f_1150_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1150_, 0, v_x_1140_);
lean_closure_set(v___f_1150_, 1, v___y_1141_);
lean_closure_set(v___f_1150_, 2, v___y_1142_);
lean_closure_set(v___f_1150_, 3, v___y_1143_);
lean_closure_set(v___f_1150_, 4, v___y_1144_);
v___x_1151_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1139_, v___f_1150_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
if (lean_obj_tag(v___x_1151_) == 0)
{
return v___x_1151_;
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1151_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___boxed(lean_object* v_mvarId_1160_, lean_object* v_x_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_mvarId_1160_, v_x_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4(lean_object* v_00_u03b1_1172_, lean_object* v_mvarId_1173_, lean_object* v_x_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_mvarId_1173_, v_x_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___boxed(lean_object* v_00_u03b1_1185_, lean_object* v_mvarId_1186_, lean_object* v_x_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4(v_00_u03b1_1185_, v_mvarId_1186_, v_x_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0(lean_object* v___x_1200_, lean_object* v___x_1201_, lean_object* v___x_1202_, lean_object* v___x_1203_, lean_object* v___x_1204_, lean_object* v___x_1205_, lean_object* v___x_1206_, lean_object* v_fst_1207_, lean_object* v_fst_1208_, lean_object* v___x_1209_, lean_object* v_snd_1210_, lean_object* v_snd_1211_, lean_object* v_hgoal_1212_){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1213_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__0));
v___x_1214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__1));
v___x_1215_ = l_Lean_Name_mkStr5(v___x_1200_, v___x_1201_, v___x_1202_, v___x_1213_, v___x_1214_);
v___x_1216_ = l_Lean_mkConst(v___x_1215_, v___x_1203_);
lean_inc_ref(v___x_1206_);
lean_inc_ref_n(v___x_1205_, 2);
lean_inc(v___x_1204_);
v___x_1217_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v___x_1204_, v___x_1205_, v___x_1206_, v_fst_1207_);
v___x_1218_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v___x_1204_, v___x_1205_, v___x_1206_, v_fst_1208_);
v___x_1219_ = l_Lean_mkApp6(v___x_1216_, v___x_1205_, v___x_1217_, v___x_1218_, v___x_1209_, v_snd_1210_, v_hgoal_1212_);
v___x_1220_ = lean_apply_1(v_snd_1211_, v___x_1219_);
return v___x_1220_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__0));
v___x_1223_ = l_Lean_stringToMessageData(v___x_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1(lean_object* v___x_1224_, lean_object* v___x_1225_, lean_object* v___x_1226_, lean_object* v___x_1227_, lean_object* v___x_1228_, lean_object* v_as_1229_, size_t v_sz_1230_, size_t v_i_1231_, lean_object* v_b_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_a_1243_; uint8_t v___x_1247_; 
v___x_1247_ = lean_usize_dec_lt(v_i_1231_, v_sz_1230_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; 
lean_dec_ref(v___x_1228_);
lean_dec_ref(v___x_1227_);
lean_dec_ref(v___x_1226_);
lean_dec(v___x_1225_);
lean_dec(v___x_1224_);
v___x_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1248_, 0, v_b_1232_);
return v___x_1248_;
}
else
{
lean_object* v_fst_1249_; lean_object* v_snd_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1304_; 
v_fst_1249_ = lean_ctor_get(v_b_1232_, 0);
v_snd_1250_ = lean_ctor_get(v_b_1232_, 1);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_b_1232_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1252_ = v_b_1232_;
v_isShared_1253_ = v_isSharedCheck_1304_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_snd_1250_);
lean_inc(v_fst_1249_);
lean_dec(v_b_1232_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1304_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v_a_1257_; lean_object* v___y_1259_; lean_object* v___x_1299_; 
v___x_1254_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_1255_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1256_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v_a_1257_ = lean_array_uget_borrowed(v_as_1229_, v_i_1231_);
lean_inc(v_a_1257_);
lean_inc(v_fst_1249_);
lean_inc_ref(v___x_1227_);
v___x_1299_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(v___x_1227_, v_fst_1249_, v_a_1257_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
if (lean_obj_tag(v_a_1300_) == 0)
{
lean_object* v___x_1301_; 
lean_dec_ref_known(v___x_1299_, 1);
lean_inc(v_a_1257_);
lean_inc(v_fst_1249_);
lean_inc_ref(v___x_1227_);
v___x_1301_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(v___x_1227_, v_fst_1249_, v_a_1257_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
if (lean_obj_tag(v_a_1302_) == 0)
{
lean_object* v___x_1303_; 
lean_dec_ref_known(v___x_1301_, 1);
lean_inc(v_a_1257_);
lean_inc(v_fst_1249_);
lean_inc_ref(v___x_1227_);
v___x_1303_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(v___x_1227_, v_fst_1249_, v_a_1257_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
v___y_1259_ = v___x_1303_;
goto v___jp_1258_;
}
else
{
v___y_1259_ = v___x_1301_;
goto v___jp_1258_;
}
}
else
{
v___y_1259_ = v___x_1301_;
goto v___jp_1258_;
}
}
else
{
v___y_1259_ = v___x_1299_;
goto v___jp_1258_;
}
}
else
{
v___y_1259_ = v___x_1299_;
goto v___jp_1258_;
}
v___jp_1258_:
{
if (lean_obj_tag(v___y_1259_) == 0)
{
lean_object* v_a_1260_; 
v_a_1260_ = lean_ctor_get(v___y_1259_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___y_1259_, 1);
if (lean_obj_tag(v_a_1260_) == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1261_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1);
lean_inc(v_fst_1249_);
v___x_1262_ = l_Lean_MessageData_ofExpr(v_fst_1249_);
v___x_1263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1261_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
v___x_1264_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_1265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1263_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
lean_inc(v_a_1257_);
v___x_1266_ = l_Lean_MessageData_ofSyntax(v_a_1257_);
v___x_1267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1265_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v___x_1268_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_1267_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v___x_1270_; 
lean_dec_ref_known(v___x_1268_, 1);
if (v_isShared_1253_ == 0)
{
v___x_1270_ = v___x_1252_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_fst_1249_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_snd_1250_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
v_a_1243_ = v___x_1270_;
goto v___jp_1242_;
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_del_object(v___x_1252_);
lean_dec(v_snd_1250_);
lean_dec(v_fst_1249_);
lean_dec_ref(v___x_1228_);
lean_dec_ref(v___x_1227_);
lean_dec_ref(v___x_1226_);
lean_dec(v___x_1225_);
lean_dec(v___x_1224_);
v_a_1272_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1268_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1268_);
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
else
{
lean_object* v_val_1280_; lean_object* v_fst_1281_; lean_object* v_snd_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1290_; 
lean_del_object(v___x_1252_);
v_val_1280_ = lean_ctor_get(v_a_1260_, 0);
lean_inc(v_val_1280_);
lean_dec_ref_known(v_a_1260_, 1);
v_fst_1281_ = lean_ctor_get(v_val_1280_, 0);
v_snd_1282_ = lean_ctor_get(v_val_1280_, 1);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_val_1280_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1284_ = v_val_1280_;
v_isShared_1285_ = v_isSharedCheck_1290_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_snd_1282_);
lean_inc(v_fst_1281_);
lean_dec(v_val_1280_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1290_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___f_1286_; lean_object* v___x_1288_; 
lean_inc_ref(v___x_1228_);
lean_inc(v_fst_1281_);
lean_inc_ref(v___x_1227_);
lean_inc_ref(v___x_1226_);
lean_inc(v___x_1225_);
lean_inc(v___x_1224_);
v___f_1286_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0), 13, 12);
lean_closure_set(v___f_1286_, 0, v___x_1254_);
lean_closure_set(v___f_1286_, 1, v___x_1255_);
lean_closure_set(v___f_1286_, 2, v___x_1256_);
lean_closure_set(v___f_1286_, 3, v___x_1224_);
lean_closure_set(v___f_1286_, 4, v___x_1225_);
lean_closure_set(v___f_1286_, 5, v___x_1226_);
lean_closure_set(v___f_1286_, 6, v___x_1227_);
lean_closure_set(v___f_1286_, 7, v_fst_1249_);
lean_closure_set(v___f_1286_, 8, v_fst_1281_);
lean_closure_set(v___f_1286_, 9, v___x_1228_);
lean_closure_set(v___f_1286_, 10, v_snd_1282_);
lean_closure_set(v___f_1286_, 11, v_snd_1250_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 1, v___f_1286_);
v___x_1288_ = v___x_1284_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_fst_1281_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v___f_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
v_a_1243_ = v___x_1288_;
goto v___jp_1242_;
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_del_object(v___x_1252_);
lean_dec(v_snd_1250_);
lean_dec(v_fst_1249_);
lean_dec_ref(v___x_1228_);
lean_dec_ref(v___x_1227_);
lean_dec_ref(v___x_1226_);
lean_dec(v___x_1225_);
lean_dec(v___x_1224_);
v_a_1291_ = lean_ctor_get(v___y_1259_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___y_1259_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___y_1259_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___y_1259_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
}
v___jp_1242_:
{
size_t v___x_1244_; size_t v___x_1245_; 
v___x_1244_ = ((size_t)1ULL);
v___x_1245_ = lean_usize_add(v_i_1231_, v___x_1244_);
v_i_1231_ = v___x_1245_;
v_b_1232_ = v_a_1243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___boxed(lean_object** _args){
lean_object* v___x_1305_ = _args[0];
lean_object* v___x_1306_ = _args[1];
lean_object* v___x_1307_ = _args[2];
lean_object* v___x_1308_ = _args[3];
lean_object* v___x_1309_ = _args[4];
lean_object* v_as_1310_ = _args[5];
lean_object* v_sz_1311_ = _args[6];
lean_object* v_i_1312_ = _args[7];
lean_object* v_b_1313_ = _args[8];
lean_object* v___y_1314_ = _args[9];
lean_object* v___y_1315_ = _args[10];
lean_object* v___y_1316_ = _args[11];
lean_object* v___y_1317_ = _args[12];
lean_object* v___y_1318_ = _args[13];
lean_object* v___y_1319_ = _args[14];
lean_object* v___y_1320_ = _args[15];
lean_object* v___y_1321_ = _args[16];
lean_object* v___y_1322_ = _args[17];
_start:
{
size_t v_sz_boxed_1323_; size_t v_i_boxed_1324_; lean_object* v_res_1325_; 
v_sz_boxed_1323_ = lean_unbox_usize(v_sz_1311_);
lean_dec(v_sz_1311_);
v_i_boxed_1324_ = lean_unbox_usize(v_i_1312_);
lean_dec(v_i_1312_);
v_res_1325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1(v___x_1305_, v___x_1306_, v___x_1307_, v___x_1308_, v___x_1309_, v_as_1310_, v_sz_boxed_1323_, v_i_boxed_1324_, v_b_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec_ref(v_as_1310_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7___redArg(lean_object* v_x_1326_, lean_object* v_x_1327_, lean_object* v_x_1328_, lean_object* v_x_1329_){
_start:
{
lean_object* v_ks_1330_; lean_object* v_vs_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1355_; 
v_ks_1330_ = lean_ctor_get(v_x_1326_, 0);
v_vs_1331_ = lean_ctor_get(v_x_1326_, 1);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_x_1326_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1333_ = v_x_1326_;
v_isShared_1334_ = v_isSharedCheck_1355_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_vs_1331_);
lean_inc(v_ks_1330_);
lean_dec(v_x_1326_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1355_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; uint8_t v___x_1336_; 
v___x_1335_ = lean_array_get_size(v_ks_1330_);
v___x_1336_ = lean_nat_dec_lt(v_x_1327_, v___x_1335_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
lean_dec(v_x_1327_);
v___x_1337_ = lean_array_push(v_ks_1330_, v_x_1328_);
v___x_1338_ = lean_array_push(v_vs_1331_, v_x_1329_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 1, v___x_1338_);
lean_ctor_set(v___x_1333_, 0, v___x_1337_);
v___x_1340_ = v___x_1333_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1337_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
else
{
lean_object* v_k_x27_1342_; uint8_t v___x_1343_; 
v_k_x27_1342_ = lean_array_fget_borrowed(v_ks_1330_, v_x_1327_);
v___x_1343_ = l_Lean_instBEqMVarId_beq(v_x_1328_, v_k_x27_1342_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1345_; 
if (v_isShared_1334_ == 0)
{
v___x_1345_ = v___x_1333_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_ks_1330_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_vs_1331_);
v___x_1345_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_unsigned_to_nat(1u);
v___x_1347_ = lean_nat_add(v_x_1327_, v___x_1346_);
lean_dec(v_x_1327_);
v_x_1326_ = v___x_1345_;
v_x_1327_ = v___x_1347_;
goto _start;
}
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1350_ = lean_array_fset(v_ks_1330_, v_x_1327_, v_x_1328_);
v___x_1351_ = lean_array_fset(v_vs_1331_, v_x_1327_, v_x_1329_);
lean_dec(v_x_1327_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 1, v___x_1351_);
lean_ctor_set(v___x_1333_, 0, v___x_1350_);
v___x_1353_ = v___x_1333_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6___redArg(lean_object* v_n_1356_, lean_object* v_k_1357_, lean_object* v_v_1358_){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = lean_unsigned_to_nat(0u);
v___x_1360_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7___redArg(v_n_1356_, v___x_1359_, v_k_1357_, v_v_1358_);
return v___x_1360_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(lean_object* v_x_1362_, size_t v_x_1363_, size_t v_x_1364_, lean_object* v_x_1365_, lean_object* v_x_1366_){
_start:
{
if (lean_obj_tag(v_x_1362_) == 0)
{
lean_object* v_es_1367_; size_t v___x_1368_; size_t v___x_1369_; lean_object* v_j_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v_es_1367_ = lean_ctor_get(v_x_1362_, 0);
v___x_1368_ = ((size_t)31ULL);
v___x_1369_ = lean_usize_land(v_x_1363_, v___x_1368_);
v_j_1370_ = lean_usize_to_nat(v___x_1369_);
v___x_1371_ = lean_array_get_size(v_es_1367_);
v___x_1372_ = lean_nat_dec_lt(v_j_1370_, v___x_1371_);
if (v___x_1372_ == 0)
{
lean_dec(v_j_1370_);
lean_dec(v_x_1366_);
lean_dec(v_x_1365_);
return v_x_1362_;
}
else
{
lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1411_; 
lean_inc_ref(v_es_1367_);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_x_1362_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v_x_1362_, 0);
lean_dec(v_unused_1412_);
v___x_1374_ = v_x_1362_;
v_isShared_1375_ = v_isSharedCheck_1411_;
goto v_resetjp_1373_;
}
else
{
lean_dec(v_x_1362_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1411_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v_v_1376_; lean_object* v___x_1377_; lean_object* v_xs_x27_1378_; lean_object* v___y_1380_; 
v_v_1376_ = lean_array_fget(v_es_1367_, v_j_1370_);
v___x_1377_ = lean_box(0);
v_xs_x27_1378_ = lean_array_fset(v_es_1367_, v_j_1370_, v___x_1377_);
switch(lean_obj_tag(v_v_1376_))
{
case 0:
{
lean_object* v_key_1385_; lean_object* v_val_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1396_; 
v_key_1385_ = lean_ctor_get(v_v_1376_, 0);
v_val_1386_ = lean_ctor_get(v_v_1376_, 1);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_v_1376_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1388_ = v_v_1376_;
v_isShared_1389_ = v_isSharedCheck_1396_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_val_1386_);
lean_inc(v_key_1385_);
lean_dec(v_v_1376_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1396_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
uint8_t v___x_1390_; 
v___x_1390_ = l_Lean_instBEqMVarId_beq(v_x_1365_, v_key_1385_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_del_object(v___x_1388_);
v___x_1391_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1385_, v_val_1386_, v_x_1365_, v_x_1366_);
v___x_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
v___y_1380_ = v___x_1392_;
goto v___jp_1379_;
}
else
{
lean_object* v___x_1394_; 
lean_dec(v_val_1386_);
lean_dec(v_key_1385_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 1, v_x_1366_);
lean_ctor_set(v___x_1388_, 0, v_x_1365_);
v___x_1394_ = v___x_1388_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_x_1365_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_x_1366_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
v___y_1380_ = v___x_1394_;
goto v___jp_1379_;
}
}
}
}
case 1:
{
lean_object* v_node_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1409_; 
v_node_1397_ = lean_ctor_get(v_v_1376_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_v_1376_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1399_ = v_v_1376_;
v_isShared_1400_ = v_isSharedCheck_1409_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_node_1397_);
lean_dec(v_v_1376_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1409_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
size_t v___x_1401_; size_t v___x_1402_; size_t v___x_1403_; size_t v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1401_ = ((size_t)5ULL);
v___x_1402_ = lean_usize_shift_right(v_x_1363_, v___x_1401_);
v___x_1403_ = ((size_t)1ULL);
v___x_1404_ = lean_usize_add(v_x_1364_, v___x_1403_);
v___x_1405_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_node_1397_, v___x_1402_, v___x_1404_, v_x_1365_, v_x_1366_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1405_);
v___x_1407_ = v___x_1399_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
v___y_1380_ = v___x_1407_;
goto v___jp_1379_;
}
}
}
default: 
{
lean_object* v___x_1410_; 
v___x_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1410_, 0, v_x_1365_);
lean_ctor_set(v___x_1410_, 1, v_x_1366_);
v___y_1380_ = v___x_1410_;
goto v___jp_1379_;
}
}
v___jp_1379_:
{
lean_object* v___x_1381_; lean_object* v___x_1383_; 
v___x_1381_ = lean_array_fset(v_xs_x27_1378_, v_j_1370_, v___y_1380_);
lean_dec(v_j_1370_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v___x_1381_);
v___x_1383_ = v___x_1374_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
else
{
lean_object* v_ks_1413_; lean_object* v_vs_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1432_; 
v_ks_1413_ = lean_ctor_get(v_x_1362_, 0);
v_vs_1414_ = lean_ctor_get(v_x_1362_, 1);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_x_1362_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1416_ = v_x_1362_;
v_isShared_1417_ = v_isSharedCheck_1432_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_vs_1414_);
lean_inc(v_ks_1413_);
lean_dec(v_x_1362_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1432_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_ks_1413_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_vs_1414_);
v___x_1419_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v_newNode_1420_; size_t v___x_1421_; uint8_t v___x_1422_; 
v_newNode_1420_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6___redArg(v___x_1419_, v_x_1365_, v_x_1366_);
v___x_1421_ = ((size_t)7ULL);
v___x_1422_ = lean_usize_dec_le(v___x_1421_, v_x_1364_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1423_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1420_);
v___x_1424_ = lean_unsigned_to_nat(4u);
v___x_1425_ = lean_nat_dec_lt(v___x_1423_, v___x_1424_);
lean_dec(v___x_1423_);
if (v___x_1425_ == 0)
{
lean_object* v_ks_1426_; lean_object* v_vs_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v_ks_1426_ = lean_ctor_get(v_newNode_1420_, 0);
lean_inc_ref(v_ks_1426_);
v_vs_1427_ = lean_ctor_get(v_newNode_1420_, 1);
lean_inc_ref(v_vs_1427_);
lean_dec_ref(v_newNode_1420_);
v___x_1428_ = lean_unsigned_to_nat(0u);
v___x_1429_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0);
v___x_1430_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(v_x_1364_, v_ks_1426_, v_vs_1427_, v___x_1428_, v___x_1429_);
lean_dec_ref(v_vs_1427_);
lean_dec_ref(v_ks_1426_);
return v___x_1430_;
}
else
{
return v_newNode_1420_;
}
}
else
{
return v_newNode_1420_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(size_t v_depth_1433_, lean_object* v_keys_1434_, lean_object* v_vals_1435_, lean_object* v_i_1436_, lean_object* v_entries_1437_){
_start:
{
lean_object* v___x_1438_; uint8_t v___x_1439_; 
v___x_1438_ = lean_array_get_size(v_keys_1434_);
v___x_1439_ = lean_nat_dec_lt(v_i_1436_, v___x_1438_);
if (v___x_1439_ == 0)
{
lean_dec(v_i_1436_);
return v_entries_1437_;
}
else
{
lean_object* v_k_1440_; lean_object* v_v_1441_; uint64_t v___x_1442_; size_t v_h_1443_; size_t v___x_1444_; lean_object* v___x_1445_; size_t v___x_1446_; size_t v___x_1447_; size_t v___x_1448_; size_t v_h_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v_k_1440_ = lean_array_fget_borrowed(v_keys_1434_, v_i_1436_);
v_v_1441_ = lean_array_fget_borrowed(v_vals_1435_, v_i_1436_);
v___x_1442_ = l_Lean_instHashableMVarId_hash(v_k_1440_);
v_h_1443_ = lean_uint64_to_usize(v___x_1442_);
v___x_1444_ = ((size_t)5ULL);
v___x_1445_ = lean_unsigned_to_nat(1u);
v___x_1446_ = ((size_t)1ULL);
v___x_1447_ = lean_usize_sub(v_depth_1433_, v___x_1446_);
v___x_1448_ = lean_usize_mul(v___x_1444_, v___x_1447_);
v_h_1449_ = lean_usize_shift_right(v_h_1443_, v___x_1448_);
v___x_1450_ = lean_nat_add(v_i_1436_, v___x_1445_);
lean_dec(v_i_1436_);
lean_inc(v_v_1441_);
lean_inc(v_k_1440_);
v___x_1451_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_entries_1437_, v_h_1449_, v_depth_1433_, v_k_1440_, v_v_1441_);
v_i_1436_ = v___x_1450_;
v_entries_1437_ = v___x_1451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_depth_1453_, lean_object* v_keys_1454_, lean_object* v_vals_1455_, lean_object* v_i_1456_, lean_object* v_entries_1457_){
_start:
{
size_t v_depth_boxed_1458_; lean_object* v_res_1459_; 
v_depth_boxed_1458_ = lean_unbox_usize(v_depth_1453_);
lean_dec(v_depth_1453_);
v_res_1459_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(v_depth_boxed_1458_, v_keys_1454_, v_vals_1455_, v_i_1456_, v_entries_1457_);
lean_dec_ref(v_vals_1455_);
lean_dec_ref(v_keys_1454_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_x_1460_, lean_object* v_x_1461_, lean_object* v_x_1462_, lean_object* v_x_1463_, lean_object* v_x_1464_){
_start:
{
size_t v_x_7384__boxed_1465_; size_t v_x_7385__boxed_1466_; lean_object* v_res_1467_; 
v_x_7384__boxed_1465_ = lean_unbox_usize(v_x_1461_);
lean_dec(v_x_1461_);
v_x_7385__boxed_1466_ = lean_unbox_usize(v_x_1462_);
lean_dec(v_x_1462_);
v_res_1467_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_x_1460_, v_x_7384__boxed_1465_, v_x_7385__boxed_1466_, v_x_1463_, v_x_1464_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2___redArg(lean_object* v_x_1468_, lean_object* v_x_1469_, lean_object* v_x_1470_){
_start:
{
uint64_t v___x_1471_; size_t v___x_1472_; size_t v___x_1473_; lean_object* v___x_1474_; 
v___x_1471_ = l_Lean_instHashableMVarId_hash(v_x_1469_);
v___x_1472_ = lean_uint64_to_usize(v___x_1471_);
v___x_1473_ = ((size_t)1ULL);
v___x_1474_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_x_1468_, v___x_1472_, v___x_1473_, v_x_1469_, v_x_1470_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(lean_object* v_mvarId_1475_, lean_object* v_val_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1479_; lean_object* v_mctx_1480_; lean_object* v_cache_1481_; lean_object* v_zetaDeltaFVarIds_1482_; lean_object* v_postponed_1483_; lean_object* v_diag_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1514_; 
v___x_1479_ = lean_st_ref_take(v___y_1477_);
v_mctx_1480_ = lean_ctor_get(v___x_1479_, 0);
v_cache_1481_ = lean_ctor_get(v___x_1479_, 1);
v_zetaDeltaFVarIds_1482_ = lean_ctor_get(v___x_1479_, 2);
v_postponed_1483_ = lean_ctor_get(v___x_1479_, 3);
v_diag_1484_ = lean_ctor_get(v___x_1479_, 4);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1486_ = v___x_1479_;
v_isShared_1487_ = v_isSharedCheck_1514_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_diag_1484_);
lean_inc(v_postponed_1483_);
lean_inc(v_zetaDeltaFVarIds_1482_);
lean_inc(v_cache_1481_);
lean_inc(v_mctx_1480_);
lean_dec(v___x_1479_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1514_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v_depth_1488_; lean_object* v_levelAssignDepth_1489_; lean_object* v_lmvarCounter_1490_; lean_object* v_mvarCounter_1491_; lean_object* v_lDecls_1492_; lean_object* v_decls_1493_; lean_object* v_userNames_1494_; lean_object* v_lAssignment_1495_; lean_object* v_eAssignment_1496_; lean_object* v_dAssignment_1497_; lean_object* v_instanceTypedMVars_1498_; lean_object* v_synthNormMemo_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1513_; 
v_depth_1488_ = lean_ctor_get(v_mctx_1480_, 0);
v_levelAssignDepth_1489_ = lean_ctor_get(v_mctx_1480_, 1);
v_lmvarCounter_1490_ = lean_ctor_get(v_mctx_1480_, 2);
v_mvarCounter_1491_ = lean_ctor_get(v_mctx_1480_, 3);
v_lDecls_1492_ = lean_ctor_get(v_mctx_1480_, 4);
v_decls_1493_ = lean_ctor_get(v_mctx_1480_, 5);
v_userNames_1494_ = lean_ctor_get(v_mctx_1480_, 6);
v_lAssignment_1495_ = lean_ctor_get(v_mctx_1480_, 7);
v_eAssignment_1496_ = lean_ctor_get(v_mctx_1480_, 8);
v_dAssignment_1497_ = lean_ctor_get(v_mctx_1480_, 9);
v_instanceTypedMVars_1498_ = lean_ctor_get(v_mctx_1480_, 10);
v_synthNormMemo_1499_ = lean_ctor_get(v_mctx_1480_, 11);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_mctx_1480_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1501_ = v_mctx_1480_;
v_isShared_1502_ = v_isSharedCheck_1513_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_synthNormMemo_1499_);
lean_inc(v_instanceTypedMVars_1498_);
lean_inc(v_dAssignment_1497_);
lean_inc(v_eAssignment_1496_);
lean_inc(v_lAssignment_1495_);
lean_inc(v_userNames_1494_);
lean_inc(v_decls_1493_);
lean_inc(v_lDecls_1492_);
lean_inc(v_mvarCounter_1491_);
lean_inc(v_lmvarCounter_1490_);
lean_inc(v_levelAssignDepth_1489_);
lean_inc(v_depth_1488_);
lean_dec(v_mctx_1480_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1513_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1503_ = lean_box(0);
v___x_1504_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2___redArg(v_eAssignment_1496_, v_mvarId_1475_, v_val_1476_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 8, v___x_1504_);
v___x_1506_ = v___x_1501_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_depth_1488_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_levelAssignDepth_1489_);
lean_ctor_set(v_reuseFailAlloc_1512_, 2, v_lmvarCounter_1490_);
lean_ctor_set(v_reuseFailAlloc_1512_, 3, v_mvarCounter_1491_);
lean_ctor_set(v_reuseFailAlloc_1512_, 4, v_lDecls_1492_);
lean_ctor_set(v_reuseFailAlloc_1512_, 5, v_decls_1493_);
lean_ctor_set(v_reuseFailAlloc_1512_, 6, v_userNames_1494_);
lean_ctor_set(v_reuseFailAlloc_1512_, 7, v_lAssignment_1495_);
lean_ctor_set(v_reuseFailAlloc_1512_, 8, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1512_, 9, v_dAssignment_1497_);
lean_ctor_set(v_reuseFailAlloc_1512_, 10, v_instanceTypedMVars_1498_);
lean_ctor_set(v_reuseFailAlloc_1512_, 11, v_synthNormMemo_1499_);
v___x_1506_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1508_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1506_);
v___x_1508_ = v___x_1486_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_cache_1481_);
lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_zetaDeltaFVarIds_1482_);
lean_ctor_set(v_reuseFailAlloc_1511_, 3, v_postponed_1483_);
lean_ctor_set(v_reuseFailAlloc_1511_, 4, v_diag_1484_);
v___x_1508_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = lean_st_ref_put(v___y_1477_, v___x_1508_);
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1503_);
return v___x_1510_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg___boxed(lean_object* v_mvarId_1515_, lean_object* v_val_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_mvarId_1515_, v_val_1516_, v___y_1517_);
lean_dec(v___y_1517_);
return v_res_1519_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1523_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__2));
v___x_1524_ = lean_unsigned_to_nat(33u);
v___x_1525_ = lean_unsigned_to_nat(105u);
v___x_1526_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__1));
v___x_1527_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15));
v___x_1528_ = l_mkPanicMessageWithDecl(v___x_1527_, v___x_1526_, v___x_1525_, v___x_1524_, v___x_1523_);
return v___x_1528_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__4));
v___x_1531_ = l_Lean_stringToMessageData(v___x_1530_);
return v___x_1531_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__6));
v___x_1534_ = l_Lean_stringToMessageData(v___x_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0(lean_object* v___x_1535_, lean_object* v_snd_1536_, lean_object* v_hyp_1537_, lean_object* v___x_1538_, lean_object* v_args_1539_, lean_object* v_fst_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
if (lean_obj_tag(v___x_1535_) == 1)
{
lean_object* v_val_1550_; lean_object* v_focusHyp_1551_; lean_object* v_restHyps_1552_; lean_object* v_proof_1553_; lean_object* v___x_1554_; 
v_val_1550_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_val_1550_);
lean_dec_ref_known(v___x_1535_, 1);
v_focusHyp_1551_ = lean_ctor_get(v_val_1550_, 0);
lean_inc_ref_n(v_focusHyp_1551_, 2);
v_restHyps_1552_ = lean_ctor_get(v_val_1550_, 1);
lean_inc_ref(v_restHyps_1552_);
v_proof_1553_ = lean_ctor_get(v_val_1550_, 2);
lean_inc_ref(v_proof_1553_);
lean_dec(v_val_1550_);
v___x_1554_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_1551_);
if (lean_obj_tag(v___x_1554_) == 1)
{
lean_object* v_val_1555_; lean_object* v_u_1556_; lean_object* v_00_u03c3s_1557_; lean_object* v_hyps_1558_; lean_object* v_target_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1617_; 
v_val_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_val_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v_u_1556_ = lean_ctor_get(v_snd_1536_, 0);
v_00_u03c3s_1557_ = lean_ctor_get(v_snd_1536_, 1);
v_hyps_1558_ = lean_ctor_get(v_snd_1536_, 2);
v_target_1559_ = lean_ctor_get(v_snd_1536_, 3);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_snd_1536_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1561_ = v_snd_1536_;
v_isShared_1562_ = v_isSharedCheck_1617_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_target_1559_);
lean_inc(v_hyps_1558_);
lean_inc(v_00_u03c3s_1557_);
lean_inc(v_u_1556_);
lean_dec(v_snd_1536_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1617_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
uint8_t v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = 0;
lean_inc_ref(v_00_u03c3s_1557_);
v___x_1564_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_hyp_1537_, v_00_u03c3s_1557_, v_val_1555_, v___x_1563_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; size_t v_sz_1576_; size_t v___x_1577_; lean_object* v___x_1578_; 
lean_dec_ref_known(v___x_1564_, 1);
v___x_1565_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_1566_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1567_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_1568_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1569_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__0));
v___x_1570_ = l_Lean_Name_mkStr6(v___x_1565_, v___x_1566_, v___x_1567_, v___x_1538_, v___x_1568_, v___x_1569_);
v___x_1571_ = lean_box(0);
lean_inc_n(v_u_1556_, 2);
v___x_1572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1572_, 0, v_u_1556_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
lean_inc_ref(v___x_1572_);
v___x_1573_ = l_Lean_mkConst(v___x_1570_, v___x_1572_);
lean_inc_ref_n(v_target_1559_, 2);
lean_inc_ref(v_focusHyp_1551_);
lean_inc_ref_n(v_restHyps_1552_, 2);
lean_inc_ref_n(v_00_u03c3s_1557_, 2);
v___x_1574_ = lean_alloc_closure((void*)(l_Lean_mkApp7), 8, 7);
lean_closure_set(v___x_1574_, 0, v___x_1573_);
lean_closure_set(v___x_1574_, 1, v_00_u03c3s_1557_);
lean_closure_set(v___x_1574_, 2, v_hyps_1558_);
lean_closure_set(v___x_1574_, 3, v_restHyps_1552_);
lean_closure_set(v___x_1574_, 4, v_focusHyp_1551_);
lean_closure_set(v___x_1574_, 5, v_target_1559_);
lean_closure_set(v___x_1574_, 6, v_proof_1553_);
v___x_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1575_, 0, v_focusHyp_1551_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v_sz_1576_ = lean_array_size(v_args_1539_);
v___x_1577_ = ((size_t)0ULL);
v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1(v___x_1572_, v_u_1556_, v_00_u03c3s_1557_, v_restHyps_1552_, v_target_1559_, v_args_1539_, v_sz_1576_, v___x_1577_, v___x_1575_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v_fst_1580_; lean_object* v_snd_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1608_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___x_1578_, 1);
v_fst_1580_ = lean_ctor_get(v_a_1579_, 0);
v_snd_1581_ = lean_ctor_get(v_a_1579_, 1);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_a_1579_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1583_ = v_a_1579_;
v_isShared_1584_ = v_isSharedCheck_1608_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_snd_1581_);
lean_inc(v_fst_1580_);
lean_dec(v_a_1579_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1608_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1585_; lean_object* v___x_1587_; 
lean_inc_ref(v_00_u03c3s_1557_);
lean_inc(v_u_1556_);
v___x_1585_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1556_, v_00_u03c3s_1557_, v_restHyps_1552_, v_fst_1580_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 2, v___x_1585_);
v___x_1587_ = v___x_1561_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_u_1556_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_00_u03c3s_1557_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v_target_1559_);
v___x_1587_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1588_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1587_);
v___x_1589_ = lean_box(0);
v___x_1590_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1588_, v___x_1589_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1596_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc_n(v_a_1591_, 2);
lean_dec_ref_known(v___x_1590_, 1);
v___x_1592_ = lean_apply_1(v_snd_1581_, v_a_1591_);
v___x_1593_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_fst_1540_, v___x_1592_, v___y_1546_);
lean_dec_ref(v___x_1593_);
v___x_1594_ = l_Lean_Expr_mvarId_x21(v_a_1591_);
lean_dec(v_a_1591_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set_tag(v___x_1583_, 1);
lean_ctor_set(v___x_1583_, 1, v___x_1571_);
lean_ctor_set(v___x_1583_, 0, v___x_1594_);
v___x_1596_ = v___x_1583_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v___x_1571_);
v___x_1596_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1596_, v___y_1542_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
return v___x_1597_;
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_del_object(v___x_1583_);
lean_dec(v_snd_1581_);
lean_dec(v_fst_1540_);
v_a_1599_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1590_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1590_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_del_object(v___x_1561_);
lean_dec_ref(v_target_1559_);
lean_dec_ref(v_00_u03c3s_1557_);
lean_dec(v_u_1556_);
lean_dec_ref(v_restHyps_1552_);
lean_dec(v_fst_1540_);
v_a_1609_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1578_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1578_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
else
{
lean_del_object(v___x_1561_);
lean_dec_ref(v_target_1559_);
lean_dec_ref(v_hyps_1558_);
lean_dec_ref(v_00_u03c3s_1557_);
lean_dec(v_u_1556_);
lean_dec_ref(v_proof_1553_);
lean_dec_ref(v_restHyps_1552_);
lean_dec_ref(v_focusHyp_1551_);
lean_dec(v_fst_1540_);
lean_dec_ref(v___x_1538_);
return v___x_1564_;
}
}
}
else
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_dec(v___x_1554_);
lean_dec_ref(v_proof_1553_);
lean_dec_ref(v_restHyps_1552_);
lean_dec_ref(v_focusHyp_1551_);
lean_dec(v_fst_1540_);
lean_dec_ref(v___x_1538_);
lean_dec(v_hyp_1537_);
lean_dec_ref(v_snd_1536_);
v___x_1618_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3);
v___x_1619_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(v___x_1618_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
return v___x_1619_;
}
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_dec(v_fst_1540_);
lean_dec_ref(v___x_1538_);
lean_dec_ref(v_snd_1536_);
lean_dec(v___x_1535_);
v___x_1620_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5);
v___x_1621_ = l_Lean_MessageData_ofSyntax(v_hyp_1537_);
v___x_1622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1620_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7);
v___x_1624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1622_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_1624_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
return v___x_1625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___boxed(lean_object* v___x_1626_, lean_object* v_snd_1627_, lean_object* v_hyp_1628_, lean_object* v___x_1629_, lean_object* v_args_1630_, lean_object* v_fst_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0(v___x_1626_, v_snd_1627_, v_hyp_1628_, v___x_1629_, v_args_1630_, v_fst_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec_ref(v_args_1630_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize(lean_object* v_x_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
v___x_1659_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1660_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2));
lean_inc(v_x_1649_);
v___x_1661_ = l_Lean_Syntax_isOfKind(v_x_1649_, v___x_1660_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; 
lean_dec(v_x_1649_);
v___x_1662_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_1662_;
}
else
{
lean_object* v___x_1663_; lean_object* v_hyp_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v_args_1667_; lean_object* v___x_1668_; 
v___x_1663_ = lean_unsigned_to_nat(1u);
v_hyp_1664_ = l_Lean_Syntax_getArg(v_x_1649_, v___x_1663_);
v___x_1665_ = lean_unsigned_to_nat(2u);
v___x_1666_ = l_Lean_Syntax_getArg(v_x_1649_, v___x_1665_);
lean_dec(v_x_1649_);
v_args_1667_ = l_Lean_Syntax_getArgs(v___x_1666_);
lean_dec(v___x_1666_);
v___x_1668_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1651_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v_fst_1670_; lean_object* v_snd_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___y_1674_; lean_object* v___x_1675_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1668_, 1);
v_fst_1670_ = lean_ctor_get(v_a_1669_, 0);
lean_inc_n(v_fst_1670_, 2);
v_snd_1671_ = lean_ctor_get(v_a_1669_, 1);
lean_inc_n(v_snd_1671_, 2);
lean_dec(v_a_1669_);
v___x_1672_ = l_Lean_TSyntax_getId(v_hyp_1664_);
v___x_1673_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_snd_1671_, v___x_1672_);
lean_dec(v___x_1672_);
v___y_1674_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___boxed), 15, 6);
lean_closure_set(v___y_1674_, 0, v___x_1673_);
lean_closure_set(v___y_1674_, 1, v_snd_1671_);
lean_closure_set(v___y_1674_, 2, v_hyp_1664_);
lean_closure_set(v___y_1674_, 3, v___x_1659_);
lean_closure_set(v___y_1674_, 4, v_args_1667_);
lean_closure_set(v___y_1674_, 5, v_fst_1670_);
v___x_1675_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_fst_1670_, v___y_1674_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
return v___x_1675_;
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_dec_ref(v_args_1667_);
lean_dec(v_hyp_1664_);
v_a_1676_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1668_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1668_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___boxed(lean_object* v_x_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize(v_x_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
lean_dec(v_a_1692_);
lean_dec_ref(v_a_1691_);
lean_dec(v_a_1690_);
lean_dec_ref(v_a_1689_);
lean_dec(v_a_1688_);
lean_dec_ref(v_a_1687_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2(lean_object* v_mvarId_1695_, lean_object* v_val_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_mvarId_1695_, v_val_1696_, v___y_1702_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___boxed(lean_object* v_mvarId_1707_, lean_object* v_val_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2(v_mvarId_1707_, v_val_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2(lean_object* v_00_u03b2_1719_, lean_object* v_x_1720_, lean_object* v_x_1721_, lean_object* v_x_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2___redArg(v_x_1720_, v_x_1721_, v_x_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_1724_, lean_object* v_x_1725_, size_t v_x_1726_, size_t v_x_1727_, lean_object* v_x_1728_, lean_object* v_x_1729_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_x_1725_, v_x_1726_, v_x_1727_, v_x_1728_, v_x_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1731_, lean_object* v_x_1732_, lean_object* v_x_1733_, lean_object* v_x_1734_, lean_object* v_x_1735_, lean_object* v_x_1736_){
_start:
{
size_t v_x_7931__boxed_1737_; size_t v_x_7932__boxed_1738_; lean_object* v_res_1739_; 
v_x_7931__boxed_1737_ = lean_unbox_usize(v_x_1733_);
lean_dec(v_x_1733_);
v_x_7932__boxed_1738_ = lean_unbox_usize(v_x_1734_);
lean_dec(v_x_1734_);
v_res_1739_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5(v_00_u03b2_1731_, v_x_1732_, v_x_7931__boxed_1737_, v_x_7932__boxed_1738_, v_x_1735_, v_x_1736_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_1740_, lean_object* v_n_1741_, lean_object* v_k_1742_, lean_object* v_v_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6___redArg(v_n_1741_, v_k_1742_, v_v_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7(lean_object* v_00_u03b2_1745_, size_t v_depth_1746_, lean_object* v_keys_1747_, lean_object* v_vals_1748_, lean_object* v_heq_1749_, lean_object* v_i_1750_, lean_object* v_entries_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(v_depth_1746_, v_keys_1747_, v_vals_1748_, v_i_1750_, v_entries_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b2_1753_, lean_object* v_depth_1754_, lean_object* v_keys_1755_, lean_object* v_vals_1756_, lean_object* v_heq_1757_, lean_object* v_i_1758_, lean_object* v_entries_1759_){
_start:
{
size_t v_depth_boxed_1760_; lean_object* v_res_1761_; 
v_depth_boxed_1760_ = lean_unbox_usize(v_depth_1754_);
lean_dec(v_depth_1754_);
v_res_1761_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7(v_00_u03b2_1753_, v_depth_boxed_1760_, v_keys_1755_, v_vals_1756_, v_heq_1757_, v_i_1758_, v_entries_1759_);
lean_dec_ref(v_vals_1756_);
lean_dec_ref(v_keys_1755_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_1762_, lean_object* v_x_1763_, lean_object* v_x_1764_, lean_object* v_x_1765_, lean_object* v_x_1766_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7___redArg(v_x_1763_, v_x_1764_, v_x_1765_, v_x_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1(){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1777_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1778_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2));
v___x_1779_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1));
v___x_1780_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___boxed), 10, 0);
v___x_1781_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1777_, v___x_1778_, v___x_1779_, v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___boxed(lean_object* v_a_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1();
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(lean_object* v___y_1784_){
_start:
{
lean_object* v___x_1786_; lean_object* v_ngen_1787_; lean_object* v_namePrefix_1788_; lean_object* v_idx_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1819_; 
v___x_1786_ = lean_st_ref_get(v___y_1784_);
v_ngen_1787_ = lean_ctor_get(v___x_1786_, 2);
lean_inc_ref(v_ngen_1787_);
lean_dec(v___x_1786_);
v_namePrefix_1788_ = lean_ctor_get(v_ngen_1787_, 0);
v_idx_1789_ = lean_ctor_get(v_ngen_1787_, 1);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_ngen_1787_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1791_ = v_ngen_1787_;
v_isShared_1792_ = v_isSharedCheck_1819_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_idx_1789_);
lean_inc(v_namePrefix_1788_);
lean_dec(v_ngen_1787_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1819_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v_r_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1797_; 
lean_inc(v_idx_1789_);
lean_inc(v_namePrefix_1788_);
v_r_1793_ = l_Lean_Name_num___override(v_namePrefix_1788_, v_idx_1789_);
v___x_1794_ = lean_unsigned_to_nat(1u);
v___x_1795_ = lean_nat_add(v_idx_1789_, v___x_1794_);
lean_dec(v_idx_1789_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 1, v___x_1795_);
v___x_1797_ = v___x_1791_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_namePrefix_1788_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1798_; lean_object* v_env_1799_; lean_object* v_nextMacroScope_1800_; lean_object* v_auxDeclNGen_1801_; lean_object* v_traceState_1802_; lean_object* v_cache_1803_; lean_object* v_recordedDeps_1804_; lean_object* v_messages_1805_; lean_object* v_infoState_1806_; lean_object* v_snapshotTasks_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1816_; 
v___x_1798_ = lean_st_ref_take(v___y_1784_);
v_env_1799_ = lean_ctor_get(v___x_1798_, 0);
v_nextMacroScope_1800_ = lean_ctor_get(v___x_1798_, 1);
v_auxDeclNGen_1801_ = lean_ctor_get(v___x_1798_, 3);
v_traceState_1802_ = lean_ctor_get(v___x_1798_, 4);
v_cache_1803_ = lean_ctor_get(v___x_1798_, 5);
v_recordedDeps_1804_ = lean_ctor_get(v___x_1798_, 6);
v_messages_1805_ = lean_ctor_get(v___x_1798_, 7);
v_infoState_1806_ = lean_ctor_get(v___x_1798_, 8);
v_snapshotTasks_1807_ = lean_ctor_get(v___x_1798_, 9);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1816_ == 0)
{
lean_object* v_unused_1817_; 
v_unused_1817_ = lean_ctor_get(v___x_1798_, 2);
lean_dec(v_unused_1817_);
v___x_1809_ = v___x_1798_;
v_isShared_1810_ = v_isSharedCheck_1816_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_snapshotTasks_1807_);
lean_inc(v_infoState_1806_);
lean_inc(v_messages_1805_);
lean_inc(v_recordedDeps_1804_);
lean_inc(v_cache_1803_);
lean_inc(v_traceState_1802_);
lean_inc(v_auxDeclNGen_1801_);
lean_inc(v_nextMacroScope_1800_);
lean_inc(v_env_1799_);
lean_dec(v___x_1798_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1816_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 2, v___x_1797_);
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_env_1799_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v_nextMacroScope_1800_);
lean_ctor_set(v_reuseFailAlloc_1815_, 2, v___x_1797_);
lean_ctor_set(v_reuseFailAlloc_1815_, 3, v_auxDeclNGen_1801_);
lean_ctor_set(v_reuseFailAlloc_1815_, 4, v_traceState_1802_);
lean_ctor_set(v_reuseFailAlloc_1815_, 5, v_cache_1803_);
lean_ctor_set(v_reuseFailAlloc_1815_, 6, v_recordedDeps_1804_);
lean_ctor_set(v_reuseFailAlloc_1815_, 7, v_messages_1805_);
lean_ctor_set(v_reuseFailAlloc_1815_, 8, v_infoState_1806_);
lean_ctor_set(v_reuseFailAlloc_1815_, 9, v_snapshotTasks_1807_);
v___x_1812_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = lean_st_ref_put(v___y_1784_, v___x_1812_);
v___x_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1814_, 0, v_r_1793_);
return v___x_1814_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg___boxed(lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(v___y_1820_);
lean_dec(v___y_1820_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0(lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(v___y_1830_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___boxed(lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0(v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(lean_object* v_e_1843_, lean_object* v___y_1844_){
_start:
{
uint8_t v___x_1846_; 
v___x_1846_ = l_Lean_Expr_hasMVar(v_e_1843_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_e_1843_);
return v___x_1847_;
}
else
{
lean_object* v___x_1848_; lean_object* v_mctx_1849_; lean_object* v___x_1850_; lean_object* v_fst_1851_; lean_object* v_snd_1852_; lean_object* v___x_1853_; lean_object* v_cache_1854_; lean_object* v_zetaDeltaFVarIds_1855_; lean_object* v_postponed_1856_; lean_object* v_diag_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1866_; 
v___x_1848_ = lean_st_ref_get(v___y_1844_);
v_mctx_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc_ref(v_mctx_1849_);
lean_dec(v___x_1848_);
v___x_1850_ = l_Lean_instantiateMVarsCore(v_mctx_1849_, v_e_1843_);
v_fst_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_fst_1851_);
v_snd_1852_ = lean_ctor_get(v___x_1850_, 1);
lean_inc(v_snd_1852_);
lean_dec_ref(v___x_1850_);
v___x_1853_ = lean_st_ref_take(v___y_1844_);
v_cache_1854_ = lean_ctor_get(v___x_1853_, 1);
v_zetaDeltaFVarIds_1855_ = lean_ctor_get(v___x_1853_, 2);
v_postponed_1856_ = lean_ctor_get(v___x_1853_, 3);
v_diag_1857_ = lean_ctor_get(v___x_1853_, 4);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1866_ == 0)
{
lean_object* v_unused_1867_; 
v_unused_1867_ = lean_ctor_get(v___x_1853_, 0);
lean_dec(v_unused_1867_);
v___x_1859_ = v___x_1853_;
v_isShared_1860_ = v_isSharedCheck_1866_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_diag_1857_);
lean_inc(v_postponed_1856_);
lean_inc(v_zetaDeltaFVarIds_1855_);
lean_inc(v_cache_1854_);
lean_dec(v___x_1853_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1866_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v_snd_1852_);
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_snd_1852_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v_cache_1854_);
lean_ctor_set(v_reuseFailAlloc_1865_, 2, v_zetaDeltaFVarIds_1855_);
lean_ctor_set(v_reuseFailAlloc_1865_, 3, v_postponed_1856_);
lean_ctor_set(v_reuseFailAlloc_1865_, 4, v_diag_1857_);
v___x_1862_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = lean_st_ref_put(v___y_1844_, v___x_1862_);
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v_fst_1851_);
return v___x_1864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg___boxed(lean_object* v_e_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(v_e_1868_, v___y_1869_);
lean_dec(v___y_1869_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1(lean_object* v_e_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(v_e_1872_, v___y_1878_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___boxed(lean_object* v_e_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1(v_e_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2(lean_object* v___x_1894_, lean_object* v___x_1895_, lean_object* v___x_1896_, lean_object* v___x_1897_, lean_object* v___x_1898_, lean_object* v_as_1899_, size_t v_sz_1900_, size_t v_i_1901_, lean_object* v_b_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v_a_1913_; uint8_t v___x_1917_; 
v___x_1917_ = lean_usize_dec_lt(v_i_1901_, v_sz_1900_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; 
lean_dec_ref(v___x_1898_);
lean_dec_ref(v___x_1897_);
lean_dec_ref(v___x_1896_);
lean_dec(v___x_1895_);
lean_dec(v___x_1894_);
v___x_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1918_, 0, v_b_1902_);
return v___x_1918_;
}
else
{
lean_object* v_fst_1919_; lean_object* v_snd_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1974_; 
v_fst_1919_ = lean_ctor_get(v_b_1902_, 0);
v_snd_1920_ = lean_ctor_get(v_b_1902_, 1);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_b_1902_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1922_ = v_b_1902_;
v_isShared_1923_ = v_isSharedCheck_1974_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_snd_1920_);
lean_inc(v_fst_1919_);
lean_dec(v_b_1902_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1974_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v_a_1927_; lean_object* v___y_1929_; lean_object* v___x_1969_; 
v___x_1924_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_1925_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1926_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v_a_1927_ = lean_array_uget_borrowed(v_as_1899_, v_i_1901_);
lean_inc(v_a_1927_);
lean_inc(v_fst_1919_);
lean_inc_ref(v___x_1897_);
v___x_1969_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(v___x_1897_, v_fst_1919_, v_a_1927_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
if (lean_obj_tag(v_a_1970_) == 0)
{
lean_object* v___x_1971_; 
lean_dec_ref_known(v___x_1969_, 1);
lean_inc(v_a_1927_);
lean_inc(v_fst_1919_);
lean_inc_ref(v___x_1897_);
v___x_1971_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(v___x_1897_, v_fst_1919_, v_a_1927_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
if (lean_obj_tag(v_a_1972_) == 0)
{
lean_object* v___x_1973_; 
lean_dec_ref_known(v___x_1971_, 1);
lean_inc(v_a_1927_);
lean_inc(v_fst_1919_);
lean_inc_ref(v___x_1897_);
v___x_1973_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(v___x_1897_, v_fst_1919_, v_a_1927_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
v___y_1929_ = v___x_1973_;
goto v___jp_1928_;
}
else
{
v___y_1929_ = v___x_1971_;
goto v___jp_1928_;
}
}
else
{
v___y_1929_ = v___x_1971_;
goto v___jp_1928_;
}
}
else
{
v___y_1929_ = v___x_1969_;
goto v___jp_1928_;
}
}
else
{
v___y_1929_ = v___x_1969_;
goto v___jp_1928_;
}
v___jp_1928_:
{
if (lean_obj_tag(v___y_1929_) == 0)
{
lean_object* v_a_1930_; 
v_a_1930_ = lean_ctor_get(v___y_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___y_1929_, 1);
if (lean_obj_tag(v_a_1930_) == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1931_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1);
lean_inc(v_fst_1919_);
v___x_1932_ = l_Lean_MessageData_ofExpr(v_fst_1919_);
v___x_1933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_1935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1933_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
lean_inc(v_a_1927_);
v___x_1936_ = l_Lean_MessageData_ofSyntax(v_a_1927_);
v___x_1937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1935_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_1937_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v___x_1940_; 
lean_dec_ref_known(v___x_1938_, 1);
if (v_isShared_1923_ == 0)
{
v___x_1940_ = v___x_1922_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_fst_1919_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_snd_1920_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
v_a_1913_ = v___x_1940_;
goto v___jp_1912_;
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_del_object(v___x_1922_);
lean_dec(v_snd_1920_);
lean_dec(v_fst_1919_);
lean_dec_ref(v___x_1898_);
lean_dec_ref(v___x_1897_);
lean_dec_ref(v___x_1896_);
lean_dec(v___x_1895_);
lean_dec(v___x_1894_);
v_a_1942_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1938_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1938_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_object* v_val_1950_; lean_object* v_fst_1951_; lean_object* v_snd_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1960_; 
lean_del_object(v___x_1922_);
v_val_1950_ = lean_ctor_get(v_a_1930_, 0);
lean_inc(v_val_1950_);
lean_dec_ref_known(v_a_1930_, 1);
v_fst_1951_ = lean_ctor_get(v_val_1950_, 0);
v_snd_1952_ = lean_ctor_get(v_val_1950_, 1);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_val_1950_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1954_ = v_val_1950_;
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_snd_1952_);
lean_inc(v_fst_1951_);
lean_dec(v_val_1950_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___f_1956_; lean_object* v___x_1958_; 
lean_inc_ref(v___x_1898_);
lean_inc(v_fst_1951_);
lean_inc_ref(v___x_1897_);
lean_inc_ref(v___x_1896_);
lean_inc(v___x_1895_);
lean_inc(v___x_1894_);
v___f_1956_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0), 13, 12);
lean_closure_set(v___f_1956_, 0, v___x_1924_);
lean_closure_set(v___f_1956_, 1, v___x_1925_);
lean_closure_set(v___f_1956_, 2, v___x_1926_);
lean_closure_set(v___f_1956_, 3, v___x_1894_);
lean_closure_set(v___f_1956_, 4, v___x_1895_);
lean_closure_set(v___f_1956_, 5, v___x_1896_);
lean_closure_set(v___f_1956_, 6, v___x_1897_);
lean_closure_set(v___f_1956_, 7, v_fst_1919_);
lean_closure_set(v___f_1956_, 8, v_fst_1951_);
lean_closure_set(v___f_1956_, 9, v___x_1898_);
lean_closure_set(v___f_1956_, 10, v_snd_1952_);
lean_closure_set(v___f_1956_, 11, v_snd_1920_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 1, v___f_1956_);
v___x_1958_ = v___x_1954_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_fst_1951_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v___f_1956_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
v_a_1913_ = v___x_1958_;
goto v___jp_1912_;
}
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_del_object(v___x_1922_);
lean_dec(v_snd_1920_);
lean_dec(v_fst_1919_);
lean_dec_ref(v___x_1898_);
lean_dec_ref(v___x_1897_);
lean_dec_ref(v___x_1896_);
lean_dec(v___x_1895_);
lean_dec(v___x_1894_);
v_a_1961_ = lean_ctor_get(v___y_1929_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___y_1929_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___y_1929_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___y_1929_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
}
}
v___jp_1912_:
{
size_t v___x_1914_; size_t v___x_1915_; 
v___x_1914_ = ((size_t)1ULL);
v___x_1915_ = lean_usize_add(v_i_1901_, v___x_1914_);
v_i_1901_ = v___x_1915_;
v_b_1902_ = v_a_1913_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2___boxed(lean_object** _args){
lean_object* v___x_1975_ = _args[0];
lean_object* v___x_1976_ = _args[1];
lean_object* v___x_1977_ = _args[2];
lean_object* v___x_1978_ = _args[3];
lean_object* v___x_1979_ = _args[4];
lean_object* v_as_1980_ = _args[5];
lean_object* v_sz_1981_ = _args[6];
lean_object* v_i_1982_ = _args[7];
lean_object* v_b_1983_ = _args[8];
lean_object* v___y_1984_ = _args[9];
lean_object* v___y_1985_ = _args[10];
lean_object* v___y_1986_ = _args[11];
lean_object* v___y_1987_ = _args[12];
lean_object* v___y_1988_ = _args[13];
lean_object* v___y_1989_ = _args[14];
lean_object* v___y_1990_ = _args[15];
lean_object* v___y_1991_ = _args[16];
lean_object* v___y_1992_ = _args[17];
_start:
{
size_t v_sz_boxed_1993_; size_t v_i_boxed_1994_; lean_object* v_res_1995_; 
v_sz_boxed_1993_ = lean_unbox_usize(v_sz_1981_);
lean_dec(v_sz_1981_);
v_i_boxed_1994_ = lean_unbox_usize(v_i_1982_);
lean_dec(v_i_1982_);
v_res_1995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2(v___x_1975_, v___x_1976_, v___x_1977_, v___x_1978_, v___x_1979_, v_as_1980_, v_sz_boxed_1993_, v_i_boxed_1994_, v_b_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec_ref(v_as_1980_);
return v_res_1995_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2003_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__3));
v___x_2004_ = lean_unsigned_to_nat(33u);
v___x_2005_ = lean_unsigned_to_nat(175u);
v___x_2006_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__2));
v___x_2007_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15));
v___x_2008_ = l_mkPanicMessageWithDecl(v___x_2007_, v___x_2006_, v___x_2005_, v___x_2004_, v___x_2003_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0(lean_object* v___x_2009_, lean_object* v___x_2010_, uint8_t v___x_2011_, lean_object* v_u_2012_, lean_object* v_00_u03c3s_2013_, lean_object* v___x_2014_, lean_object* v_hyp_2015_, lean_object* v_hyps_2016_, lean_object* v_target_2017_, lean_object* v_args_2018_, lean_object* v_fst_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_Elab_Tactic_elabTerm(v___x_2009_, v___x_2010_, v___x_2011_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2031_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc_n(v_a_2030_, 2);
lean_dec_ref_known(v___x_2029_, 1);
lean_inc(v___y_2027_);
lean_inc_ref(v___y_2026_);
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2024_);
v___x_2031_ = lean_infer_type(v_a_2030_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2031_, 1);
v___x_2033_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_2034_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_2035_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_2036_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0));
v___x_2037_ = lean_box(0);
lean_inc(v_u_2012_);
v___x_2038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2038_, 0, v_u_2012_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
lean_inc_ref(v___x_2038_);
v___x_2039_ = l_Lean_mkConst(v___x_2036_, v___x_2038_);
lean_inc_ref(v_00_u03c3s_2013_);
v___x_2040_ = l_Lean_Expr_app___override(v___x_2039_, v_00_u03c3s_2013_);
v___x_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
v___x_2042_ = 0;
v___x_2043_ = lean_box(0);
v___x_2044_ = l_Lean_Meta_mkFreshExprMVar(v___x_2041_, v___x_2042_, v___x_2043_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc_n(v_a_2045_, 2);
lean_dec_ref_known(v___x_2044_, 1);
v___x_2046_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__5));
lean_inc_ref(v___x_2014_);
v___x_2047_ = l_Lean_Name_mkStr5(v___x_2033_, v___x_2034_, v___x_2035_, v___x_2014_, v___x_2046_);
lean_inc_ref(v___x_2038_);
v___x_2048_ = l_Lean_mkConst(v___x_2047_, v___x_2038_);
lean_inc_ref(v_00_u03c3s_2013_);
lean_inc(v_a_2032_);
v___x_2049_ = l_Lean_mkApp3(v___x_2048_, v_a_2032_, v_00_u03c3s_2013_, v_a_2045_);
v___x_2050_ = lean_box(0);
v___x_2051_ = l_Lean_Meta_synthInstance(v___x_2049_, v___x_2050_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2053_; lean_object* v_a_2054_; lean_object* v___x_2055_; lean_object* v_a_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; size_t v_sz_2066_; size_t v___x_2067_; lean_object* v___x_2068_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2051_, 1);
v___x_2053_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(v___y_2027_);
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref(v___x_2053_);
v___x_2055_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(v_a_2045_, v___y_2025_);
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref(v___x_2055_);
v___x_2057_ = l_Lean_TSyntax_getId(v_hyp_2015_);
v___x_2058_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
lean_ctor_set(v___x_2058_, 1, v_a_2054_);
lean_ctor_set(v___x_2058_, 2, v_a_2056_);
v___x_2059_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_2058_);
v___x_2060_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_2061_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__1));
v___x_2062_ = l_Lean_Name_mkStr6(v___x_2033_, v___x_2034_, v___x_2035_, v___x_2014_, v___x_2060_, v___x_2061_);
lean_inc_ref(v___x_2038_);
v___x_2063_ = l_Lean_mkConst(v___x_2062_, v___x_2038_);
lean_inc_ref_n(v_target_2017_, 2);
lean_inc_ref_n(v_hyps_2016_, 2);
lean_inc_ref(v___x_2059_);
lean_inc_ref_n(v_00_u03c3s_2013_, 2);
v___x_2064_ = lean_alloc_closure((void*)(l_Lean_mkApp8), 9, 8);
lean_closure_set(v___x_2064_, 0, v___x_2063_);
lean_closure_set(v___x_2064_, 1, v_00_u03c3s_2013_);
lean_closure_set(v___x_2064_, 2, v_a_2032_);
lean_closure_set(v___x_2064_, 3, v___x_2059_);
lean_closure_set(v___x_2064_, 4, v_hyps_2016_);
lean_closure_set(v___x_2064_, 5, v_target_2017_);
lean_closure_set(v___x_2064_, 6, v_a_2052_);
lean_closure_set(v___x_2064_, 7, v_a_2030_);
v___x_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2059_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v_sz_2066_ = lean_array_size(v_args_2018_);
v___x_2067_ = ((size_t)0ULL);
lean_inc(v_u_2012_);
v___x_2068_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2(v___x_2038_, v_u_2012_, v_00_u03c3s_2013_, v_hyps_2016_, v_target_2017_, v_args_2018_, v_sz_2066_, v___x_2067_, v___x_2065_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; lean_object* v_fst_2070_; lean_object* v_snd_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2100_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_a_2069_);
lean_dec_ref_known(v___x_2068_, 1);
v_fst_2070_ = lean_ctor_get(v_a_2069_, 0);
v_snd_2071_ = lean_ctor_get(v_a_2069_, 1);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_a_2069_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2073_ = v_a_2069_;
v_isShared_2074_ = v_isSharedCheck_2100_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_snd_2071_);
lean_inc(v_fst_2070_);
lean_dec(v_a_2069_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2100_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; 
lean_inc(v_fst_2070_);
v___x_2075_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_fst_2070_);
if (lean_obj_tag(v___x_2075_) == 1)
{
lean_object* v_val_2076_; lean_object* v___x_2077_; 
v_val_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_val_2076_);
lean_dec_ref_known(v___x_2075_, 1);
lean_inc_ref(v_00_u03c3s_2013_);
v___x_2077_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_hyp_2015_, v_00_u03c3s_2013_, v_val_2076_, v___x_2011_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
lean_dec_ref_known(v___x_2077_, 1);
lean_inc_ref(v_00_u03c3s_2013_);
lean_inc(v_u_2012_);
v___x_2078_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_2012_, v_00_u03c3s_2013_, v_hyps_2016_, v_fst_2070_);
v___x_2079_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2079_, 0, v_u_2012_);
lean_ctor_set(v___x_2079_, 1, v_00_u03c3s_2013_);
lean_ctor_set(v___x_2079_, 2, v___x_2078_);
lean_ctor_set(v___x_2079_, 3, v_target_2017_);
v___x_2080_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_2079_);
v___x_2081_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2080_, v___x_2043_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2087_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc_n(v_a_2082_, 2);
lean_dec_ref_known(v___x_2081_, 1);
v___x_2083_ = lean_apply_1(v_snd_2071_, v_a_2082_);
v___x_2084_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_fst_2019_, v___x_2083_, v___y_2025_);
lean_dec_ref(v___x_2084_);
v___x_2085_ = l_Lean_Expr_mvarId_x21(v_a_2082_);
lean_dec(v_a_2082_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set_tag(v___x_2073_, 1);
lean_ctor_set(v___x_2073_, 1, v___x_2037_);
lean_ctor_set(v___x_2073_, 0, v___x_2085_);
v___x_2087_ = v___x_2073_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2085_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v___x_2037_);
v___x_2087_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2087_, v___y_2021_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
return v___x_2088_;
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_del_object(v___x_2073_);
lean_dec(v_snd_2071_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v_fst_2019_);
v_a_2090_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2081_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2081_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
else
{
lean_del_object(v___x_2073_);
lean_dec(v_snd_2071_);
lean_dec(v_fst_2070_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v_fst_2019_);
lean_dec_ref(v_target_2017_);
lean_dec_ref(v_hyps_2016_);
lean_dec_ref(v_00_u03c3s_2013_);
lean_dec(v_u_2012_);
return v___x_2077_;
}
}
else
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
lean_dec(v___x_2075_);
lean_del_object(v___x_2073_);
lean_dec(v_snd_2071_);
lean_dec(v_fst_2070_);
lean_dec(v_fst_2019_);
lean_dec_ref(v_target_2017_);
lean_dec_ref(v_hyps_2016_);
lean_dec(v_hyp_2015_);
lean_dec_ref(v_00_u03c3s_2013_);
lean_dec(v_u_2012_);
v___x_2098_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4, &l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4);
v___x_2099_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(v___x_2098_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
return v___x_2099_;
}
}
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v_fst_2019_);
lean_dec_ref(v_target_2017_);
lean_dec_ref(v_hyps_2016_);
lean_dec(v_hyp_2015_);
lean_dec_ref(v_00_u03c3s_2013_);
lean_dec(v_u_2012_);
v_a_2101_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_2068_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2068_);
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
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec(v_a_2045_);
lean_dec_ref_known(v___x_2038_, 2);
lean_dec(v_a_2032_);
lean_dec(v_a_2030_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v_fst_2019_);
lean_dec_ref(v_target_2017_);
lean_dec_ref(v_hyps_2016_);
lean_dec(v_hyp_2015_);
lean_dec_ref(v___x_2014_);
lean_dec_ref(v_00_u03c3s_2013_);
lean_dec(v_u_2012_);
v_a_2109_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2051_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2051_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec_ref_known(v___x_2038_, 2);
lean_dec(v_a_2032_);
lean_dec(v_a_2030_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v_fst_2019_);
lean_dec_ref(v_target_2017_);
lean_dec_ref(v_hyps_2016_);
lean_dec(v_hyp_2015_);
lean_dec_ref(v___x_2014_);
lean_dec_ref(v_00_u03c3s_2013_);
lean_dec(v_u_2012_);
v_a_2117_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2044_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2044_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec(v_a_2030_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v_fst_2019_);
lean_dec_ref(v_target_2017_);
lean_dec_ref(v_hyps_2016_);
lean_dec(v_hyp_2015_);
lean_dec_ref(v___x_2014_);
lean_dec_ref(v_00_u03c3s_2013_);
lean_dec(v_u_2012_);
v_a_2125_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2031_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2031_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v_fst_2019_);
lean_dec_ref(v_target_2017_);
lean_dec_ref(v_hyps_2016_);
lean_dec(v_hyp_2015_);
lean_dec_ref(v___x_2014_);
lean_dec_ref(v_00_u03c3s_2013_);
lean_dec(v_u_2012_);
v_a_2133_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2029_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2029_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___boxed(lean_object** _args){
lean_object* v___x_2141_ = _args[0];
lean_object* v___x_2142_ = _args[1];
lean_object* v___x_2143_ = _args[2];
lean_object* v_u_2144_ = _args[3];
lean_object* v_00_u03c3s_2145_ = _args[4];
lean_object* v___x_2146_ = _args[5];
lean_object* v_hyp_2147_ = _args[6];
lean_object* v_hyps_2148_ = _args[7];
lean_object* v_target_2149_ = _args[8];
lean_object* v_args_2150_ = _args[9];
lean_object* v_fst_2151_ = _args[10];
lean_object* v___y_2152_ = _args[11];
lean_object* v___y_2153_ = _args[12];
lean_object* v___y_2154_ = _args[13];
lean_object* v___y_2155_ = _args[14];
lean_object* v___y_2156_ = _args[15];
lean_object* v___y_2157_ = _args[16];
lean_object* v___y_2158_ = _args[17];
lean_object* v___y_2159_ = _args[18];
lean_object* v___y_2160_ = _args[19];
_start:
{
uint8_t v___x_8366__boxed_2161_; lean_object* v_res_2162_; 
v___x_8366__boxed_2161_ = lean_unbox(v___x_2143_);
v_res_2162_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0(v___x_2141_, v___x_2142_, v___x_8366__boxed_2161_, v_u_2144_, v_00_u03c3s_2145_, v___x_2146_, v_hyp_2147_, v_hyps_2148_, v_target_2149_, v_args_2150_, v_fst_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec_ref(v_args_2150_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure(lean_object* v_x_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; 
v___x_2186_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_2187_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1));
lean_inc(v_x_2176_);
v___x_2188_ = l_Lean_Syntax_isOfKind(v_x_2176_, v___x_2187_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2189_; 
lean_dec(v_x_2176_);
v___x_2189_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_2189_;
}
else
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2190_ = lean_unsigned_to_nat(1u);
v___x_2191_ = l_Lean_Syntax_getArg(v_x_2176_, v___x_2190_);
v___x_2192_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4));
lean_inc(v___x_2191_);
v___x_2193_ = l_Lean_Syntax_isOfKind(v___x_2191_, v___x_2192_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; 
lean_dec(v___x_2191_);
lean_dec(v_x_2176_);
v___x_2194_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_2194_;
}
else
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; uint8_t v___x_2198_; 
v___x_2195_ = lean_unsigned_to_nat(0u);
v___x_2196_ = lean_unsigned_to_nat(2u);
v___x_2197_ = l_Lean_Syntax_getArg(v_x_2176_, v___x_2196_);
v___x_2198_ = l_Lean_Syntax_matchesNull(v___x_2197_, v___x_2195_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; 
lean_dec(v___x_2191_);
lean_dec(v_x_2176_);
v___x_2199_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_2199_;
}
else
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v_hyp_2203_; lean_object* v_args_2204_; lean_object* v___x_2205_; 
v___x_2200_ = l_Lean_Syntax_getArg(v___x_2191_, v___x_2195_);
v___x_2201_ = l_Lean_Syntax_getArg(v___x_2191_, v___x_2190_);
lean_dec(v___x_2191_);
v___x_2202_ = lean_unsigned_to_nat(4u);
v_hyp_2203_ = l_Lean_Syntax_getArg(v_x_2176_, v___x_2202_);
lean_dec(v_x_2176_);
v_args_2204_ = l_Lean_Syntax_getArgs(v___x_2201_);
lean_dec(v___x_2201_);
v___x_2205_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_2178_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v_snd_2207_; lean_object* v_fst_2208_; lean_object* v_u_2209_; lean_object* v_00_u03c3s_2210_; lean_object* v_hyps_2211_; lean_object* v_target_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; lean_object* v___x_2215_; lean_object* v___f_2216_; lean_object* v___x_2217_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2206_);
lean_dec_ref_known(v___x_2205_, 1);
v_snd_2207_ = lean_ctor_get(v_a_2206_, 1);
lean_inc(v_snd_2207_);
v_fst_2208_ = lean_ctor_get(v_a_2206_, 0);
lean_inc_n(v_fst_2208_, 2);
lean_dec(v_a_2206_);
v_u_2209_ = lean_ctor_get(v_snd_2207_, 0);
lean_inc(v_u_2209_);
v_00_u03c3s_2210_ = lean_ctor_get(v_snd_2207_, 1);
lean_inc_ref(v_00_u03c3s_2210_);
v_hyps_2211_ = lean_ctor_get(v_snd_2207_, 2);
lean_inc_ref(v_hyps_2211_);
v_target_2212_ = lean_ctor_get(v_snd_2207_, 3);
lean_inc_ref(v_target_2212_);
lean_dec(v_snd_2207_);
v___x_2213_ = lean_box(0);
v___x_2214_ = 0;
v___x_2215_ = lean_box(v___x_2214_);
v___f_2216_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___boxed), 20, 11);
lean_closure_set(v___f_2216_, 0, v___x_2200_);
lean_closure_set(v___f_2216_, 1, v___x_2213_);
lean_closure_set(v___f_2216_, 2, v___x_2215_);
lean_closure_set(v___f_2216_, 3, v_u_2209_);
lean_closure_set(v___f_2216_, 4, v_00_u03c3s_2210_);
lean_closure_set(v___f_2216_, 5, v___x_2186_);
lean_closure_set(v___f_2216_, 6, v_hyp_2203_);
lean_closure_set(v___f_2216_, 7, v_hyps_2211_);
lean_closure_set(v___f_2216_, 8, v_target_2212_);
lean_closure_set(v___f_2216_, 9, v_args_2204_);
lean_closure_set(v___f_2216_, 10, v_fst_2208_);
v___x_2217_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_fst_2208_, v___f_2216_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_);
return v___x_2217_;
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v_args_2204_);
lean_dec(v_hyp_2203_);
lean_dec(v___x_2200_);
v_a_2218_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2205_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2205_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___boxed(lean_object* v_x_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure(v_x_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
lean_dec(v_a_2228_);
lean_dec_ref(v_a_2227_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1(){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2246_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2247_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1));
v___x_2248_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1));
v___x_2249_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___boxed), 10, 0);
v___x_2250_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2246_, v___x_2247_, v___x_2248_, v___x_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___boxed(lean_object* v_a_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1();
return v_res_2252_;
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
