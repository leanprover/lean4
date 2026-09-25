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
lean_object* v___x_107_; lean_object* v_env_108_; lean_object* v___x_109_; lean_object* v_toCold_110_; lean_object* v_mctx_111_; lean_object* v_lctx_112_; lean_object* v_options_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_107_ = lean_st_ref_get(v___y_105_);
v_env_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc_ref(v_env_108_);
lean_dec(v___x_107_);
v___x_109_ = lean_st_ref_get(v___y_103_);
v_toCold_110_ = lean_ctor_get(v___y_104_, 0);
v_mctx_111_ = lean_ctor_get(v___x_109_, 0);
lean_inc_ref(v_mctx_111_);
lean_dec(v___x_109_);
v_lctx_112_ = lean_ctor_get(v___y_102_, 2);
v_options_113_ = lean_ctor_get(v_toCold_110_, 2);
lean_inc_ref(v_options_113_);
lean_inc_ref(v_lctx_112_);
v___x_114_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_114_, 0, v_env_108_);
lean_ctor_set(v___x_114_, 1, v_mctx_111_);
lean_ctor_set(v___x_114_, 2, v_lctx_112_);
lean_ctor_set(v___x_114_, 3, v_options_113_);
v___x_115_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v_msgData_101_);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0___boxed(lean_object* v_msgData_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(v_msgData_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
return v_res_123_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_124_; double v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_float_of_nat(v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(lean_object* v_cls_129_, lean_object* v_msg_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_ref_136_; lean_object* v___x_137_; lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_183_; 
v_ref_136_ = lean_ctor_get(v___y_133_, 2);
v___x_137_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(v_msg_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
v_a_138_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_183_ == 0)
{
v___x_140_ = v___x_137_;
v_isShared_141_ = v_isSharedCheck_183_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_137_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_183_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v_traceState_143_; lean_object* v_env_144_; lean_object* v_nextMacroScope_145_; lean_object* v_ngen_146_; lean_object* v_auxDeclNGen_147_; lean_object* v_cache_148_; lean_object* v_recordedDeps_149_; lean_object* v_messages_150_; lean_object* v_infoState_151_; lean_object* v_snapshotTasks_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_182_; 
v___x_142_ = lean_st_ref_take(v___y_134_);
v_traceState_143_ = lean_ctor_get(v___x_142_, 4);
v_env_144_ = lean_ctor_get(v___x_142_, 0);
v_nextMacroScope_145_ = lean_ctor_get(v___x_142_, 1);
v_ngen_146_ = lean_ctor_get(v___x_142_, 2);
v_auxDeclNGen_147_ = lean_ctor_get(v___x_142_, 3);
v_cache_148_ = lean_ctor_get(v___x_142_, 5);
v_recordedDeps_149_ = lean_ctor_get(v___x_142_, 6);
v_messages_150_ = lean_ctor_get(v___x_142_, 7);
v_infoState_151_ = lean_ctor_get(v___x_142_, 8);
v_snapshotTasks_152_ = lean_ctor_get(v___x_142_, 9);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_182_ == 0)
{
v___x_154_ = v___x_142_;
v_isShared_155_ = v_isSharedCheck_182_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_snapshotTasks_152_);
lean_inc(v_infoState_151_);
lean_inc(v_messages_150_);
lean_inc(v_recordedDeps_149_);
lean_inc(v_cache_148_);
lean_inc(v_traceState_143_);
lean_inc(v_auxDeclNGen_147_);
lean_inc(v_ngen_146_);
lean_inc(v_nextMacroScope_145_);
lean_inc(v_env_144_);
lean_dec(v___x_142_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_182_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
uint64_t v_tid_156_; lean_object* v_traces_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_181_; 
v_tid_156_ = lean_ctor_get_uint64(v_traceState_143_, sizeof(void*)*1);
v_traces_157_ = lean_ctor_get(v_traceState_143_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v_traceState_143_);
if (v_isSharedCheck_181_ == 0)
{
v___x_159_ = v_traceState_143_;
v_isShared_160_ = v_isSharedCheck_181_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_traces_157_);
lean_dec(v_traceState_143_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_181_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; lean_object* v___x_162_; double v___x_163_; uint8_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_161_ = lean_box(0);
v___x_162_ = lean_box(0);
v___x_163_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0);
v___x_164_ = 0;
v___x_165_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__1));
v___x_166_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_166_, 0, v_cls_129_);
lean_ctor_set(v___x_166_, 1, v___x_162_);
lean_ctor_set(v___x_166_, 2, v___x_165_);
lean_ctor_set_float(v___x_166_, sizeof(void*)*3, v___x_163_);
lean_ctor_set_float(v___x_166_, sizeof(void*)*3 + 8, v___x_163_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*3 + 16, v___x_164_);
v___x_167_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__2));
v___x_168_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set(v___x_168_, 1, v_a_138_);
lean_ctor_set(v___x_168_, 2, v___x_167_);
lean_inc(v_ref_136_);
v___x_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_169_, 0, v_ref_136_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
v___x_170_ = l_Lean_PersistentArray_push___redArg(v_traces_157_, v___x_169_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_170_);
v___x_172_ = v___x_159_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_170_);
lean_ctor_set_uint64(v_reuseFailAlloc_180_, sizeof(void*)*1, v_tid_156_);
v___x_172_ = v_reuseFailAlloc_180_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_174_; 
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 4, v___x_172_);
v___x_174_ = v___x_154_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_env_144_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_nextMacroScope_145_);
lean_ctor_set(v_reuseFailAlloc_179_, 2, v_ngen_146_);
lean_ctor_set(v_reuseFailAlloc_179_, 3, v_auxDeclNGen_147_);
lean_ctor_set(v_reuseFailAlloc_179_, 4, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_179_, 5, v_cache_148_);
lean_ctor_set(v_reuseFailAlloc_179_, 6, v_recordedDeps_149_);
lean_ctor_set(v_reuseFailAlloc_179_, 7, v_messages_150_);
lean_ctor_set(v_reuseFailAlloc_179_, 8, v_infoState_151_);
lean_ctor_set(v_reuseFailAlloc_179_, 9, v_snapshotTasks_152_);
v___x_174_ = v_reuseFailAlloc_179_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_175_ = lean_st_ref_put(v___y_134_, v___x_174_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_161_);
v___x_177_ = v___x_140_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_161_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___boxed(lean_object* v_cls_184_, lean_object* v_msg_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v_cls_184_, v_msg_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(lean_object* v_msg_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_ref_198_; lean_object* v___x_199_; lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_208_; 
v_ref_198_ = lean_ctor_get(v___y_195_, 2);
v___x_199_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(v_msg_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
v_a_200_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_208_ == 0)
{
v___x_202_ = v___x_199_;
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_199_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_206_; 
lean_inc(v_ref_198_);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v_ref_198_);
lean_ctor_set(v___x_204_, 1, v_a_200_);
if (v_isShared_203_ == 0)
{
lean_ctor_set_tag(v___x_202_, 1);
lean_ctor_set(v___x_202_, 0, v___x_204_);
v___x_206_ = v___x_202_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_204_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg___boxed(lean_object* v_msg_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v_msg_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
return v_res_215_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__5));
v___x_229_ = l_Lean_stringToMessageData(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__7));
v___x_232_ = l_Lean_stringToMessageData(v___x_231_);
return v___x_232_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_236_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_237_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__10));
v___x_238_ = l_Lean_Name_append(v___x_237_, v___x_236_);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__12));
v___x_241_ = l_Lean_stringToMessageData(v___x_240_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__14));
v___x_244_ = l_Lean_stringToMessageData(v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(lean_object* v_P_245_, lean_object* v_QR_246_, lean_object* v_arg_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
uint8_t v___x_260_; 
v___x_260_ = l_Lean_Syntax_isIdent(v_arg_247_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec(v_arg_247_);
lean_dec_ref(v_QR_246_);
lean_dec_ref(v_P_245_);
v___x_261_ = lean_box(0);
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
else
{
lean_object* v___x_263_; 
lean_inc_ref(v_QR_246_);
v___x_263_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_QR_246_);
if (lean_obj_tag(v___x_263_) == 1)
{
lean_object* v_val_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_421_; 
v_val_264_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_421_ == 0)
{
v___x_266_ = v___x_263_;
v_isShared_267_ = v_isSharedCheck_421_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_val_264_);
lean_dec(v___x_263_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_421_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v_p_268_; 
v_p_268_ = lean_ctor_get(v_val_264_, 2);
lean_inc_ref(v_p_268_);
if (lean_obj_tag(v_p_268_) == 5)
{
lean_object* v_fn_269_; 
v_fn_269_ = lean_ctor_get(v_p_268_, 0);
if (lean_obj_tag(v_fn_269_) == 5)
{
lean_object* v_fn_270_; 
v_fn_270_ = lean_ctor_get(v_fn_269_, 0);
if (lean_obj_tag(v_fn_270_) == 5)
{
lean_object* v_fn_271_; 
v_fn_271_ = lean_ctor_get(v_fn_270_, 0);
if (lean_obj_tag(v_fn_271_) == 4)
{
lean_object* v_declName_272_; 
v_declName_272_ = lean_ctor_get(v_fn_271_, 0);
if (lean_obj_tag(v_declName_272_) == 1)
{
lean_object* v_pre_273_; 
v_pre_273_ = lean_ctor_get(v_declName_272_, 0);
if (lean_obj_tag(v_pre_273_) == 1)
{
lean_object* v_pre_274_; 
v_pre_274_ = lean_ctor_get(v_pre_273_, 0);
if (lean_obj_tag(v_pre_274_) == 1)
{
lean_object* v_pre_275_; 
v_pre_275_ = lean_ctor_get(v_pre_274_, 0);
if (lean_obj_tag(v_pre_275_) == 1)
{
lean_object* v_pre_276_; 
v_pre_276_ = lean_ctor_get(v_pre_275_, 0);
if (lean_obj_tag(v_pre_276_) == 0)
{
lean_object* v_name_277_; lean_object* v_uniq_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_419_; 
v_name_277_ = lean_ctor_get(v_val_264_, 0);
v_uniq_278_ = lean_ctor_get(v_val_264_, 1);
v_isSharedCheck_419_ = !lean_is_exclusive(v_val_264_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; 
v_unused_420_ = lean_ctor_get(v_val_264_, 2);
lean_dec(v_unused_420_);
v___x_280_ = v_val_264_;
v_isShared_281_ = v_isSharedCheck_419_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_uniq_278_);
lean_inc(v_name_277_);
lean_dec(v_val_264_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_419_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v_arg_282_; lean_object* v_arg_283_; lean_object* v_arg_284_; lean_object* v_us_285_; lean_object* v_str_286_; lean_object* v_str_287_; lean_object* v_str_288_; lean_object* v_str_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_arg_282_ = lean_ctor_get(v_p_268_, 1);
v_arg_283_ = lean_ctor_get(v_fn_269_, 1);
v_arg_284_ = lean_ctor_get(v_fn_270_, 1);
v_us_285_ = lean_ctor_get(v_fn_271_, 1);
v_str_286_ = lean_ctor_get(v_declName_272_, 1);
v_str_287_ = lean_ctor_get(v_pre_273_, 1);
v_str_288_ = lean_ctor_get(v_pre_274_, 1);
v_str_289_ = lean_ctor_get(v_pre_275_, 1);
v___x_290_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_291_ = lean_string_dec_eq(v_str_289_, v___x_290_);
if (v___x_291_ == 0)
{
lean_del_object(v___x_280_);
lean_dec(v_uniq_278_);
lean_dec(v_name_277_);
lean_dec_ref_known(v_p_268_, 2);
lean_del_object(v___x_266_);
lean_dec(v_arg_247_);
lean_dec_ref(v_QR_246_);
lean_dec_ref(v_P_245_);
goto v___jp_257_;
}
else
{
lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_293_ = lean_string_dec_eq(v_str_288_, v___x_292_);
if (v___x_293_ == 0)
{
lean_del_object(v___x_280_);
lean_dec(v_uniq_278_);
lean_dec(v_name_277_);
lean_dec_ref_known(v_p_268_, 2);
lean_del_object(v___x_266_);
lean_dec(v_arg_247_);
lean_dec_ref(v_QR_246_);
lean_dec_ref(v_P_245_);
goto v___jp_257_;
}
else
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_295_ = lean_string_dec_eq(v_str_287_, v___x_294_);
if (v___x_295_ == 0)
{
lean_del_object(v___x_280_);
lean_dec(v_uniq_278_);
lean_dec(v_name_277_);
lean_dec_ref_known(v_p_268_, 2);
lean_del_object(v___x_266_);
lean_dec(v_arg_247_);
lean_dec_ref(v_QR_246_);
lean_dec_ref(v_P_245_);
goto v___jp_257_;
}
else
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__2));
v___x_297_ = lean_string_dec_eq(v_str_286_, v___x_296_);
if (v___x_297_ == 0)
{
lean_del_object(v___x_280_);
lean_dec(v_uniq_278_);
lean_dec(v_name_277_);
lean_dec_ref_known(v_p_268_, 2);
lean_del_object(v___x_266_);
lean_dec(v_arg_247_);
lean_dec_ref(v_QR_246_);
lean_dec_ref(v_P_245_);
goto v___jp_257_;
}
else
{
if (lean_obj_tag(v_us_285_) == 1)
{
lean_object* v_tail_298_; 
v_tail_298_ = lean_ctor_get(v_us_285_, 1);
if (lean_obj_tag(v_tail_298_) == 0)
{
lean_object* v_head_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_head_299_ = lean_ctor_get(v_us_285_, 0);
lean_inc_ref(v_P_245_);
lean_inc_ref_n(v_arg_284_, 2);
lean_inc_n(v_head_299_, 2);
v___x_300_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_head_299_, v_arg_284_, v_P_245_, v_QR_246_);
v___x_301_ = l_Lean_Syntax_getId(v_arg_247_);
v___x_302_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(v_head_299_, v_arg_284_, v___x_300_, v___x_301_);
lean_dec(v___x_301_);
if (lean_obj_tag(v___x_302_) == 1)
{
lean_object* v_val_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_414_; 
lean_del_object(v___x_266_);
v_val_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_414_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_414_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_val_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_414_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v_focusHyp_307_; lean_object* v_restHyps_308_; lean_object* v_proof_309_; lean_object* v___x_310_; 
v_focusHyp_307_ = lean_ctor_get(v_val_303_, 0);
lean_inc_ref_n(v_focusHyp_307_, 2);
v_restHyps_308_ = lean_ctor_get(v_val_303_, 1);
lean_inc_ref(v_restHyps_308_);
v_proof_309_ = lean_ctor_get(v_val_303_, 2);
lean_inc_ref(v_proof_309_);
lean_dec(v_val_303_);
v___x_310_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_307_);
if (lean_obj_tag(v___x_310_) == 1)
{
lean_object* v_val_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_409_; 
lean_del_object(v___x_305_);
v_val_311_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_409_ == 0)
{
v___x_313_ = v___x_310_;
v_isShared_314_ = v_isSharedCheck_409_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_val_311_);
lean_dec(v___x_310_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_409_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
uint8_t v___x_315_; lean_object* v___x_316_; 
v___x_315_ = 0;
lean_inc_ref(v_arg_284_);
v___x_316_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_arg_247_, v_arg_284_, v_val_311_, v___x_315_, v_a_252_, v_a_253_, v_a_254_, v_a_255_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_399_; 
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; 
v_unused_400_ = lean_ctor_get(v___x_316_, 0);
lean_dec(v_unused_400_);
v___x_318_ = v___x_316_;
v_isShared_319_ = v_isSharedCheck_399_;
goto v_resetjp_317_;
}
else
{
lean_dec(v___x_316_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_399_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v_toCold_320_; lean_object* v_options_321_; lean_object* v_inheritedTraceOptions_322_; uint8_t v_hasTrace_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; 
v_toCold_320_ = lean_ctor_get(v_a_254_, 0);
v_options_321_ = lean_ctor_get(v_toCold_320_, 2);
v_inheritedTraceOptions_322_ = lean_ctor_get(v_toCold_320_, 11);
v_hasTrace_323_ = lean_ctor_get_uint8(v_options_321_, sizeof(void*)*1);
v___x_324_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4));
lean_inc_ref(v_us_285_);
v___x_325_ = l_Lean_mkConst(v___x_324_, v_us_285_);
lean_inc_ref(v_arg_282_);
lean_inc_ref(v_focusHyp_307_);
lean_inc_ref(v_P_245_);
lean_inc_ref(v_arg_284_);
v___x_326_ = l_Lean_mkApp6(v___x_325_, v_arg_284_, v_P_245_, v_restHyps_308_, v_focusHyp_307_, v_arg_282_, v_proof_309_);
if (v_hasTrace_323_ == 0)
{
lean_dec_ref(v_P_245_);
v___y_340_ = v_a_248_;
v___y_341_ = v_a_249_;
v___y_342_ = v_a_250_;
v___y_343_ = v_a_251_;
v___y_344_ = v_a_252_;
v___y_345_ = v_a_253_;
v___y_346_ = v_a_254_;
v___y_347_ = v_a_255_;
goto v___jp_339_;
}
else
{
lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_375_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_376_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11);
v___x_377_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_322_, v_options_321_, v___x_376_);
if (v___x_377_ == 0)
{
lean_dec_ref(v_P_245_);
v___y_340_ = v_a_248_;
v___y_341_ = v_a_249_;
v___y_342_ = v_a_250_;
v___y_343_ = v_a_251_;
v___y_344_ = v_a_252_;
v___y_345_ = v_a_253_;
v___y_346_ = v_a_254_;
v___y_347_ = v_a_255_;
goto v___jp_339_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_378_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13);
lean_inc_ref(v_p_268_);
v___x_379_ = l_Lean_MessageData_ofExpr(v_p_268_);
v___x_380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
lean_inc_ref(v_focusHyp_307_);
v___x_383_ = l_Lean_MessageData_ofExpr(v_focusHyp_307_);
v___x_384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15);
v___x_386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
lean_inc_ref(v_arg_282_);
lean_inc_ref(v_arg_284_);
lean_inc(v_head_299_);
v___x_387_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_head_299_, v_arg_284_, v_P_245_, v_arg_282_);
v___x_388_ = l_Lean_MessageData_ofExpr(v___x_387_);
v___x_389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_386_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v___x_375_, v___x_389_, v_a_252_, v_a_253_, v_a_254_, v_a_255_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_dec_ref_known(v___x_390_, 1);
v___y_340_ = v_a_248_;
v___y_341_ = v_a_249_;
v___y_342_ = v_a_250_;
v___y_343_ = v_a_251_;
v___y_344_ = v_a_252_;
v___y_345_ = v_a_253_;
v___y_346_ = v_a_254_;
v___y_347_ = v_a_255_;
goto v___jp_339_;
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec_ref(v___x_326_);
lean_del_object(v___x_318_);
lean_del_object(v___x_313_);
lean_dec_ref(v_focusHyp_307_);
lean_del_object(v___x_280_);
lean_dec(v_uniq_278_);
lean_dec(v_name_277_);
lean_dec_ref_known(v_p_268_, 2);
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
v___jp_327_:
{
lean_object* v___x_329_; 
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 2, v_arg_282_);
v___x_329_ = v___x_280_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_name_277_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_uniq_278_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v_arg_282_);
v___x_329_ = v_reuseFailAlloc_338_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_330_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_329_);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v___x_326_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_331_);
v___x_333_ = v___x_313_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_331_);
v___x_333_ = v_reuseFailAlloc_337_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_335_; 
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_333_);
v___x_335_ = v___x_318_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
v___jp_339_:
{
lean_object* v___x_348_; 
lean_inc_ref(v_arg_283_);
lean_inc_ref(v_focusHyp_307_);
v___x_348_ = l_Lean_Meta_isExprDefEq(v_focusHyp_307_, v_arg_283_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; uint8_t v___x_350_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_a_349_);
lean_dec_ref_known(v___x_348_, 1);
v___x_350_ = lean_unbox(v_a_349_);
lean_dec(v_a_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec_ref(v___x_326_);
lean_del_object(v___x_318_);
lean_del_object(v___x_313_);
lean_del_object(v___x_280_);
lean_dec(v_uniq_278_);
lean_dec(v_name_277_);
v___x_351_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6);
v___x_352_ = l_Lean_MessageData_ofExpr(v_p_268_);
v___x_353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_351_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_353_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
v___x_356_ = l_Lean_MessageData_ofExpr(v_focusHyp_307_);
v___x_357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_355_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
v___x_358_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_357_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
v_a_359_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_358_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
else
{
lean_inc_ref(v_arg_282_);
lean_dec_ref(v_focusHyp_307_);
lean_dec_ref_known(v_p_268_, 2);
goto v___jp_327_;
}
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
lean_dec_ref(v___x_326_);
lean_del_object(v___x_318_);
lean_del_object(v___x_313_);
lean_dec_ref(v_focusHyp_307_);
lean_del_object(v___x_280_);
lean_dec(v_uniq_278_);
lean_dec(v_name_277_);
lean_dec_ref_known(v_p_268_, 2);
v_a_367_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_348_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_348_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_del_object(v___x_313_);
lean_dec_ref(v_proof_309_);
lean_dec_ref(v_restHyps_308_);
lean_dec_ref(v_focusHyp_307_);
lean_del_object(v___x_280_);
lean_dec(v_uniq_278_);
lean_dec(v_name_277_);
lean_dec_ref_known(v_p_268_, 2);
lean_dec_ref(v_P_245_);
v_a_401_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_316_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_316_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
else
{
lean_object* v___x_410_; lean_object* v___x_412_; 
lean_dec(v___x_310_);
lean_dec_ref(v_proof_309_);
lean_dec_ref(v_restHyps_308_);
lean_dec_ref(v_focusHyp_307_);
lean_del_object(v___x_280_);
lean_dec(v_uniq_278_);
lean_dec(v_name_277_);
lean_dec_ref_known(v_p_268_, 2);
lean_dec(v_arg_247_);
lean_dec_ref(v_P_245_);
v___x_410_ = lean_box(0);
if (v_isShared_306_ == 0)
{
lean_ctor_set_tag(v___x_305_, 0);
lean_ctor_set(v___x_305_, 0, v___x_410_);
v___x_412_ = v___x_305_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
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
else
{
lean_object* v___x_415_; lean_object* v___x_417_; 
lean_dec(v___x_302_);
lean_del_object(v___x_280_);
lean_dec(v_uniq_278_);
lean_dec(v_name_277_);
lean_dec_ref_known(v_p_268_, 2);
lean_dec(v_arg_247_);
lean_dec_ref(v_P_245_);
v___x_415_ = lean_box(0);
if (v_isShared_267_ == 0)
{
lean_ctor_set_tag(v___x_266_, 0);
lean_ctor_set(v___x_266_, 0, v___x_415_);
v___x_417_ = v___x_266_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
else
{
lean_del_object(v___x_280_);
lean_dec(v_uniq_278_);
lean_dec(v_name_277_);
lean_dec_ref_known(v_p_268_, 2);
lean_del_object(v___x_266_);
lean_dec(v_arg_247_);
lean_dec_ref(v_QR_246_);
lean_dec_ref(v_P_245_);
goto v___jp_257_;
}
}
else
{
lean_del_object(v___x_280_);
lean_dec(v_uniq_278_);
lean_dec(v_name_277_);
lean_dec_ref_known(v_p_268_, 2);
lean_del_object(v___x_266_);
lean_dec(v_arg_247_);
lean_dec_ref(v_QR_246_);
lean_dec_ref(v_P_245_);
goto v___jp_257_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_p_268_, 2);
lean_del_object(v___x_266_);
lean_dec(v_val_264_);
lean_dec(v_arg_247_);
lean_dec_ref(v_QR_246_);
lean_dec_ref(v_P_245_);
goto v___jp_257_;
}
}
else
{
lean_dec_ref_known(v_p_268_, 2);
lean_del_object(v___x_266_);
lean_dec(v_val_264_);
lean_dec(v_arg_247_);
lean_dec_ref(v_QR_246_);
lean_dec_ref(v_P_245_);
goto v___jp_257_;
}
}
else
{
lean_dec_ref_known(v_p_268_, 2);
lean_del_object(v___x_266_);
lean_dec(v_val_264_);
lean_dec(v_arg_247_);
lean_dec_ref(v_QR_246_);
lean_dec_ref(v_P_245_);
goto v___jp_257_;
}
}
else
{
lean_dec_ref_known(v_p_268_, 2);
lean_del_object(v___x_266_);
lean_dec(v_val_264_);
lean_dec(v_arg_247_);
lean_dec_ref(v_QR_246_);
lean_dec_ref(v_P_245_);
goto v___jp_257_;
}
}
else
{
lean_dec_ref_known(v_p_268_, 2);
lean_del_object(v___x_266_);
lean_dec(v_val_264_);
lean_dec(v_arg_247_);
lean_dec_ref(v_QR_246_);
lean_dec_ref(v_P_245_);
goto v___jp_257_;
}
}
else
{
lean_dec_ref_known(v_p_268_, 2);
lean_del_object(v___x_266_);
lean_dec(v_val_264_);
lean_dec(v_arg_247_);
lean_dec_ref(v_QR_246_);
lean_dec_ref(v_P_245_);
goto v___jp_257_;
}
}
else
{
lean_dec_ref_known(v_p_268_, 2);
lean_del_object(v___x_266_);
lean_dec(v_val_264_);
lean_dec(v_arg_247_);
lean_dec_ref(v_QR_246_);
lean_dec_ref(v_P_245_);
goto v___jp_257_;
}
}
else
{
lean_dec_ref_known(v_p_268_, 2);
lean_del_object(v___x_266_);
lean_dec(v_val_264_);
lean_dec(v_arg_247_);
lean_dec_ref(v_QR_246_);
lean_dec_ref(v_P_245_);
goto v___jp_257_;
}
}
else
{
lean_dec_ref(v_p_268_);
lean_del_object(v___x_266_);
lean_dec(v_val_264_);
lean_dec(v_arg_247_);
lean_dec_ref(v_QR_246_);
lean_dec_ref(v_P_245_);
goto v___jp_257_;
}
}
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec(v___x_263_);
lean_dec(v_arg_247_);
lean_dec_ref(v_QR_246_);
lean_dec_ref(v_P_245_);
v___x_422_ = lean_box(0);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
}
v___jp_257_:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_box(0);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___boxed(lean_object* v_P_424_, lean_object* v_QR_425_, lean_object* v_arg_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(v_P_424_, v_QR_425_, v_arg_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0(lean_object* v_00_u03b1_437_, lean_object* v_msg_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v_msg_438_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___boxed(lean_object* v_00_u03b1_449_, lean_object* v_msg_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0(v_00_u03b1_449_, v_msg_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1(lean_object* v_cls_461_, lean_object* v_msg_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v_cls_461_, v_msg_462_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___boxed(lean_object* v_cls_473_, lean_object* v_msg_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1(v_cls_473_, v_msg_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
return v_res_484_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0(void){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_instMonadEIO___redArg();
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(lean_object* v_msg_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v_toApplicative_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_596_; 
v___x_502_ = lean_obj_once(&l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0, &l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0);
v___x_503_ = l_StateRefT_x27_instMonad___redArg(v___x_502_);
v_toApplicative_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; 
v_unused_597_ = lean_ctor_get(v___x_503_, 1);
lean_dec(v_unused_597_);
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_596_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_toApplicative_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_596_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v_toFunctor_508_; lean_object* v_toSeq_509_; lean_object* v_toSeqLeft_510_; lean_object* v_toSeqRight_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_594_; 
v_toFunctor_508_ = lean_ctor_get(v_toApplicative_504_, 0);
v_toSeq_509_ = lean_ctor_get(v_toApplicative_504_, 2);
v_toSeqLeft_510_ = lean_ctor_get(v_toApplicative_504_, 3);
v_toSeqRight_511_ = lean_ctor_get(v_toApplicative_504_, 4);
v_isSharedCheck_594_ = !lean_is_exclusive(v_toApplicative_504_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; 
v_unused_595_ = lean_ctor_get(v_toApplicative_504_, 1);
lean_dec(v_unused_595_);
v___x_513_ = v_toApplicative_504_;
v_isShared_514_ = v_isSharedCheck_594_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_toSeqRight_511_);
lean_inc(v_toSeqLeft_510_);
lean_inc(v_toSeq_509_);
lean_inc(v_toFunctor_508_);
lean_dec(v_toApplicative_504_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_594_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___f_515_; lean_object* v___f_516_; lean_object* v___f_517_; lean_object* v___f_518_; lean_object* v___x_519_; lean_object* v___f_520_; lean_object* v___f_521_; lean_object* v___f_522_; lean_object* v___x_524_; 
v___f_515_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__1));
v___f_516_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__2));
lean_inc_ref(v_toFunctor_508_);
v___f_517_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_517_, 0, v_toFunctor_508_);
v___f_518_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_518_, 0, v_toFunctor_508_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v___f_517_);
lean_ctor_set(v___x_519_, 1, v___f_518_);
v___f_520_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_520_, 0, v_toSeqRight_511_);
v___f_521_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_521_, 0, v_toSeqLeft_510_);
v___f_522_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_522_, 0, v_toSeq_509_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 4, v___f_520_);
lean_ctor_set(v___x_513_, 3, v___f_521_);
lean_ctor_set(v___x_513_, 2, v___f_522_);
lean_ctor_set(v___x_513_, 1, v___f_515_);
lean_ctor_set(v___x_513_, 0, v___x_519_);
v___x_524_ = v___x_513_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v___f_515_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v___f_522_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v___f_521_);
lean_ctor_set(v_reuseFailAlloc_593_, 4, v___f_520_);
v___x_524_ = v_reuseFailAlloc_593_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_526_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 1, v___f_516_);
lean_ctor_set(v___x_506_, 0, v___x_524_);
v___x_526_ = v___x_506_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v___f_516_);
v___x_526_ = v_reuseFailAlloc_592_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; lean_object* v_toApplicative_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_590_; 
v___x_527_ = l_StateRefT_x27_instMonad___redArg(v___x_526_);
v_toApplicative_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; 
v_unused_591_ = lean_ctor_get(v___x_527_, 1);
lean_dec(v_unused_591_);
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_590_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_toApplicative_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_590_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v_toFunctor_532_; lean_object* v_toSeq_533_; lean_object* v_toSeqLeft_534_; lean_object* v_toSeqRight_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_588_; 
v_toFunctor_532_ = lean_ctor_get(v_toApplicative_528_, 0);
v_toSeq_533_ = lean_ctor_get(v_toApplicative_528_, 2);
v_toSeqLeft_534_ = lean_ctor_get(v_toApplicative_528_, 3);
v_toSeqRight_535_ = lean_ctor_get(v_toApplicative_528_, 4);
v_isSharedCheck_588_ = !lean_is_exclusive(v_toApplicative_528_);
if (v_isSharedCheck_588_ == 0)
{
lean_object* v_unused_589_; 
v_unused_589_ = lean_ctor_get(v_toApplicative_528_, 1);
lean_dec(v_unused_589_);
v___x_537_ = v_toApplicative_528_;
v_isShared_538_ = v_isSharedCheck_588_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_toSeqRight_535_);
lean_inc(v_toSeqLeft_534_);
lean_inc(v_toSeq_533_);
lean_inc(v_toFunctor_532_);
lean_dec(v_toApplicative_528_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_588_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___f_539_; lean_object* v___f_540_; lean_object* v___f_541_; lean_object* v___f_542_; lean_object* v___x_543_; lean_object* v___f_544_; lean_object* v___f_545_; lean_object* v___f_546_; lean_object* v___x_548_; 
v___f_539_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__3));
v___f_540_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__4));
lean_inc_ref(v_toFunctor_532_);
v___f_541_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_541_, 0, v_toFunctor_532_);
v___f_542_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_542_, 0, v_toFunctor_532_);
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v___f_541_);
lean_ctor_set(v___x_543_, 1, v___f_542_);
v___f_544_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_544_, 0, v_toSeqRight_535_);
v___f_545_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_545_, 0, v_toSeqLeft_534_);
v___f_546_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_546_, 0, v_toSeq_533_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 4, v___f_544_);
lean_ctor_set(v___x_537_, 3, v___f_545_);
lean_ctor_set(v___x_537_, 2, v___f_546_);
lean_ctor_set(v___x_537_, 1, v___f_539_);
lean_ctor_set(v___x_537_, 0, v___x_543_);
v___x_548_ = v___x_537_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v___f_539_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v___f_546_);
lean_ctor_set(v_reuseFailAlloc_587_, 3, v___f_545_);
lean_ctor_set(v_reuseFailAlloc_587_, 4, v___f_544_);
v___x_548_ = v_reuseFailAlloc_587_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_550_; 
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 1, v___f_540_);
lean_ctor_set(v___x_530_, 0, v___x_548_);
v___x_550_ = v___x_530_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v___f_540_);
v___x_550_ = v_reuseFailAlloc_586_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_551_; lean_object* v_toApplicative_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_584_; 
v___x_551_ = l_StateRefT_x27_instMonad___redArg(v___x_550_);
v_toApplicative_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; 
v_unused_585_ = lean_ctor_get(v___x_551_, 1);
lean_dec(v_unused_585_);
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_584_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_toApplicative_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_584_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v_toFunctor_556_; lean_object* v_toSeq_557_; lean_object* v_toSeqLeft_558_; lean_object* v_toSeqRight_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_582_; 
v_toFunctor_556_ = lean_ctor_get(v_toApplicative_552_, 0);
v_toSeq_557_ = lean_ctor_get(v_toApplicative_552_, 2);
v_toSeqLeft_558_ = lean_ctor_get(v_toApplicative_552_, 3);
v_toSeqRight_559_ = lean_ctor_get(v_toApplicative_552_, 4);
v_isSharedCheck_582_ = !lean_is_exclusive(v_toApplicative_552_);
if (v_isSharedCheck_582_ == 0)
{
lean_object* v_unused_583_; 
v_unused_583_ = lean_ctor_get(v_toApplicative_552_, 1);
lean_dec(v_unused_583_);
v___x_561_ = v_toApplicative_552_;
v_isShared_562_ = v_isSharedCheck_582_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_toSeqRight_559_);
lean_inc(v_toSeqLeft_558_);
lean_inc(v_toSeq_557_);
lean_inc(v_toFunctor_556_);
lean_dec(v_toApplicative_552_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_582_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___f_563_; lean_object* v___f_564_; lean_object* v___f_565_; lean_object* v___f_566_; lean_object* v___x_567_; lean_object* v___f_568_; lean_object* v___f_569_; lean_object* v___f_570_; lean_object* v___x_572_; 
v___f_563_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__5));
v___f_564_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__6));
lean_inc_ref(v_toFunctor_556_);
v___f_565_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_565_, 0, v_toFunctor_556_);
v___f_566_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_566_, 0, v_toFunctor_556_);
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v___f_565_);
lean_ctor_set(v___x_567_, 1, v___f_566_);
v___f_568_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_568_, 0, v_toSeqRight_559_);
v___f_569_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_569_, 0, v_toSeqLeft_558_);
v___f_570_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_570_, 0, v_toSeq_557_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 4, v___f_568_);
lean_ctor_set(v___x_561_, 3, v___f_569_);
lean_ctor_set(v___x_561_, 2, v___f_570_);
lean_ctor_set(v___x_561_, 1, v___f_563_);
lean_ctor_set(v___x_561_, 0, v___x_567_);
v___x_572_ = v___x_561_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v___f_563_);
lean_ctor_set(v_reuseFailAlloc_581_, 2, v___f_570_);
lean_ctor_set(v_reuseFailAlloc_581_, 3, v___f_569_);
lean_ctor_set(v_reuseFailAlloc_581_, 4, v___f_568_);
v___x_572_ = v_reuseFailAlloc_581_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_574_; 
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v___f_564_);
lean_ctor_set(v___x_554_, 0, v___x_572_);
v___x_574_ = v___x_554_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v___f_564_);
v___x_574_ = v_reuseFailAlloc_580_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_10568__overap_578_; lean_object* v___x_579_; 
v___x_575_ = l_StateRefT_x27_instMonad___redArg(v___x_574_);
v___x_576_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_576_, 0, lean_box(0));
lean_closure_set(v___x_576_, 1, lean_box(0));
lean_closure_set(v___x_576_, 2, v___x_575_);
v___x_577_ = l_OptionT_instInhabitedOfPure___redArg(v___x_576_);
v___x_10568__overap_578_ = lean_panic_fn_borrowed(v___x_577_, v_msg_492_);
lean_dec(v___x_577_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc(v___y_498_);
lean_inc_ref(v___y_497_);
lean_inc(v___y_496_);
lean_inc_ref(v___y_495_);
lean_inc(v___y_494_);
lean_inc_ref(v___y_493_);
v___x_579_ = lean_apply_9(v___x_10568__overap_578_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, lean_box(0));
return v___x_579_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___boxed(lean_object* v_msg_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(v_msg_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
return v_res_608_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_box(0);
v___x_610_ = l_Lean_mkSort(v___x_609_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0);
v___x_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__9));
v___x_639_ = l_Lean_stringToMessageData(v___x_638_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_658_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__17));
v___x_659_ = lean_unsigned_to_nat(37u);
v___x_660_ = lean_unsigned_to_nat(45u);
v___x_661_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__16));
v___x_662_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15));
v___x_663_ = l_mkPanicMessageWithDecl(v___x_662_, v___x_661_, v___x_660_, v___x_659_, v___x_658_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(lean_object* v_P_664_, lean_object* v_QR_665_, lean_object* v_arg_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_QR_665_);
if (lean_obj_tag(v___x_679_) == 1)
{
lean_object* v_val_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_858_; 
v_val_680_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_858_ == 0)
{
v___x_682_ = v___x_679_;
v_isShared_683_ = v_isSharedCheck_858_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_val_680_);
lean_dec(v___x_679_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_858_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_p_684_; 
v_p_684_ = lean_ctor_get(v_val_680_, 2);
lean_inc_ref(v_p_684_);
if (lean_obj_tag(v_p_684_) == 5)
{
lean_object* v_name_685_; lean_object* v_uniq_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_856_; 
v_name_685_ = lean_ctor_get(v_val_680_, 0);
v_uniq_686_ = lean_ctor_get(v_val_680_, 1);
v_isSharedCheck_856_ = !lean_is_exclusive(v_val_680_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; 
v_unused_857_ = lean_ctor_get(v_val_680_, 2);
lean_dec(v_unused_857_);
v___x_688_ = v_val_680_;
v_isShared_689_ = v_isSharedCheck_856_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_uniq_686_);
lean_inc(v_name_685_);
lean_dec(v_val_680_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_856_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_fn_690_; lean_object* v_arg_691_; lean_object* v___y_693_; 
v_fn_690_ = lean_ctor_get(v_p_684_, 0);
v_arg_691_ = lean_ctor_get(v_p_684_, 1);
lean_inc_ref(v_arg_691_);
if (lean_obj_tag(v_fn_690_) == 5)
{
lean_object* v_fn_703_; 
v_fn_703_ = lean_ctor_get(v_fn_690_, 0);
if (lean_obj_tag(v_fn_703_) == 5)
{
lean_object* v_fn_704_; 
v_fn_704_ = lean_ctor_get(v_fn_703_, 0);
if (lean_obj_tag(v_fn_704_) == 4)
{
lean_object* v_declName_705_; 
v_declName_705_ = lean_ctor_get(v_fn_704_, 0);
if (lean_obj_tag(v_declName_705_) == 1)
{
lean_object* v_pre_706_; 
v_pre_706_ = lean_ctor_get(v_declName_705_, 0);
if (lean_obj_tag(v_pre_706_) == 1)
{
lean_object* v_pre_707_; 
v_pre_707_ = lean_ctor_get(v_pre_706_, 0);
if (lean_obj_tag(v_pre_707_) == 1)
{
lean_object* v_pre_708_; 
v_pre_708_ = lean_ctor_get(v_pre_707_, 0);
if (lean_obj_tag(v_pre_708_) == 1)
{
lean_object* v_pre_709_; 
v_pre_709_ = lean_ctor_get(v_pre_708_, 0);
if (lean_obj_tag(v_pre_709_) == 0)
{
lean_object* v_arg_710_; lean_object* v_arg_711_; lean_object* v_us_712_; lean_object* v_str_713_; lean_object* v_str_714_; lean_object* v_str_715_; lean_object* v_str_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v_arg_710_ = lean_ctor_get(v_fn_690_, 1);
lean_inc_ref(v_arg_710_);
v_arg_711_ = lean_ctor_get(v_fn_703_, 1);
lean_inc_ref(v_arg_711_);
v_us_712_ = lean_ctor_get(v_fn_704_, 1);
v_str_713_ = lean_ctor_get(v_declName_705_, 1);
v_str_714_ = lean_ctor_get(v_pre_706_, 1);
v_str_715_ = lean_ctor_get(v_pre_707_, 1);
v_str_716_ = lean_ctor_get(v_pre_708_, 1);
v___x_717_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_718_ = lean_string_dec_eq(v_str_716_, v___x_717_);
if (v___x_718_ == 0)
{
lean_dec_ref(v_arg_711_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec(v_name_685_);
lean_dec_ref_known(v_p_684_, 2);
lean_del_object(v___x_682_);
lean_dec(v_arg_666_);
lean_dec_ref(v_P_664_);
goto v___jp_676_;
}
else
{
lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_719_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_720_ = lean_string_dec_eq(v_str_715_, v___x_719_);
if (v___x_720_ == 0)
{
lean_dec_ref(v_arg_711_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec(v_name_685_);
lean_dec_ref_known(v_p_684_, 2);
lean_del_object(v___x_682_);
lean_dec(v_arg_666_);
lean_dec_ref(v_P_664_);
goto v___jp_676_;
}
else
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_722_ = lean_string_dec_eq(v_str_714_, v___x_721_);
if (v___x_722_ == 0)
{
lean_dec_ref(v_arg_711_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec(v_name_685_);
lean_dec_ref_known(v_p_684_, 2);
lean_del_object(v___x_682_);
lean_dec(v_arg_666_);
lean_dec_ref(v_P_664_);
goto v___jp_676_;
}
else
{
lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_723_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__2));
v___x_724_ = lean_string_dec_eq(v_str_713_, v___x_723_);
if (v___x_724_ == 0)
{
lean_dec_ref(v_arg_711_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec(v_name_685_);
lean_dec_ref_known(v_p_684_, 2);
lean_del_object(v___x_682_);
lean_dec(v_arg_666_);
lean_dec_ref(v_P_664_);
goto v___jp_676_;
}
else
{
if (lean_obj_tag(v_us_712_) == 1)
{
lean_object* v_tail_725_; 
v_tail_725_ = lean_ctor_get(v_us_712_, 1);
if (lean_obj_tag(v_tail_725_) == 0)
{
lean_object* v_head_726_; lean_object* v___x_727_; uint8_t v___x_728_; lean_object* v___x_729_; 
v_head_726_ = lean_ctor_get(v_us_712_, 0);
lean_inc(v_head_726_);
v___x_727_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1);
v___x_728_ = 0;
v___x_729_ = l_Lean_Meta_mkFreshExprMVar(v___x_727_, v___x_728_, v_pre_709_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc_n(v_a_730_, 2);
lean_dec_ref_known(v___x_729_, 1);
v___x_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_731_, 0, v_a_730_);
v___x_732_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2));
v___x_733_ = lean_box(0);
v___x_734_ = l_Lean_Elab_Tactic_elabTermWithHoles(v_arg_666_, v___x_731_, v___x_732_, v___x_724_, v___x_733_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v_fst_736_; lean_object* v_snd_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_832_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
v_fst_736_ = lean_ctor_get(v_a_735_, 0);
v_snd_737_ = lean_ctor_get(v_a_735_, 1);
v_isSharedCheck_832_ = !lean_is_exclusive(v_a_735_);
if (v_isSharedCheck_832_ == 0)
{
v___x_739_ = v_a_735_;
v_isShared_740_ = v_isSharedCheck_832_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_snd_737_);
lean_inc(v_fst_736_);
lean_dec(v_a_735_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_832_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v_00_u03c6_745_; lean_object* v_h_u03c6_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___x_815_; 
v___x_741_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4));
lean_inc_ref(v_us_712_);
v___x_742_ = l_Lean_mkConst(v___x_741_, v_us_712_);
lean_inc(v_a_730_);
lean_inc_ref(v_arg_710_);
lean_inc_ref(v_arg_711_);
v___x_743_ = l_Lean_mkApp3(v___x_742_, v_arg_711_, v_arg_710_, v_a_730_);
v___x_815_ = l_Lean_Meta_synthInstance_x3f(v___x_743_, v___x_733_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_a_816_);
lean_dec_ref_known(v___x_815_, 1);
if (lean_obj_tag(v_a_816_) == 1)
{
lean_object* v_val_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v_val_817_ = lean_ctor_get(v_a_816_, 0);
lean_inc(v_val_817_);
lean_dec_ref_known(v_a_816_, 1);
v___x_818_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12));
lean_inc_ref_n(v_us_712_, 2);
v___x_819_ = l_Lean_mkConst(v___x_818_, v_us_712_);
lean_inc_ref_n(v_arg_710_, 2);
lean_inc_ref_n(v_arg_711_, 2);
v___x_820_ = l_Lean_mkApp5(v___x_819_, v_arg_711_, v_a_730_, v_arg_710_, v_val_817_, v_fst_736_);
v___x_821_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14));
v___x_822_ = l_Lean_mkConst(v___x_821_, v_us_712_);
v___x_823_ = l_Lean_mkAppB(v___x_822_, v_arg_711_, v_arg_710_);
v_00_u03c6_745_ = v___x_823_;
v_h_u03c6_746_ = v___x_820_;
v___y_747_ = v_a_668_;
v___y_748_ = v_a_671_;
v___y_749_ = v_a_672_;
v___y_750_ = v_a_673_;
v___y_751_ = v_a_674_;
goto v___jp_744_;
}
else
{
lean_dec(v_a_816_);
v_00_u03c6_745_ = v_a_730_;
v_h_u03c6_746_ = v_fst_736_;
v___y_747_ = v_a_668_;
v___y_748_ = v_a_671_;
v___y_749_ = v_a_672_;
v___y_750_ = v_a_673_;
v___y_751_ = v_a_674_;
goto v___jp_744_;
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_del_object(v___x_739_);
lean_dec(v_snd_737_);
lean_dec(v_fst_736_);
lean_dec(v_a_730_);
lean_dec(v_head_726_);
lean_dec_ref(v_arg_711_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec_ref_known(v_p_684_, 2);
lean_dec(v_name_685_);
lean_del_object(v___x_682_);
lean_dec_ref(v_P_664_);
v_a_824_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_815_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_815_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
v___jp_744_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_752_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6));
lean_inc_ref(v_us_712_);
v___x_753_ = l_Lean_mkConst(v___x_752_, v_us_712_);
lean_inc_ref(v_arg_710_);
lean_inc_ref(v_arg_711_);
lean_inc_ref(v_00_u03c6_745_);
v___x_754_ = l_Lean_mkApp3(v___x_753_, v_00_u03c6_745_, v_arg_711_, v_arg_710_);
v___x_755_ = l_Lean_Meta_synthInstance_x3f(v___x_754_, v___x_733_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_806_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_806_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_806_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_806_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
if (lean_obj_tag(v_a_756_) == 1)
{
lean_object* v_val_760_; lean_object* v___x_761_; 
lean_del_object(v___x_758_);
v_val_760_ = lean_ctor_get(v_a_756_, 0);
lean_inc(v_val_760_);
lean_dec_ref_known(v_a_756_, 1);
v___x_761_ = l_Lean_Elab_Tactic_pushGoals___redArg(v_snd_737_, v___y_747_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_toCold_762_; lean_object* v_options_763_; lean_object* v_inheritedTraceOptions_764_; uint8_t v_hasTrace_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec_ref_known(v___x_761_, 1);
v_toCold_762_ = lean_ctor_get(v___y_750_, 0);
v_options_763_ = lean_ctor_get(v_toCold_762_, 2);
v_inheritedTraceOptions_764_ = lean_ctor_get(v_toCold_762_, 11);
v_hasTrace_765_ = lean_ctor_get_uint8(v_options_763_, sizeof(void*)*1);
v___x_766_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8));
lean_inc_ref(v_us_712_);
v___x_767_ = l_Lean_mkConst(v___x_766_, v_us_712_);
lean_inc_ref(v_arg_691_);
lean_inc_ref(v_arg_710_);
lean_inc_ref(v_P_664_);
lean_inc_ref(v_arg_711_);
v___x_768_ = l_Lean_mkApp7(v___x_767_, v_arg_711_, v_00_u03c6_745_, v_P_664_, v_arg_710_, v_arg_691_, v_val_760_, v_h_u03c6_746_);
if (v_hasTrace_765_ == 0)
{
lean_del_object(v___x_739_);
lean_dec(v_head_726_);
lean_dec_ref(v_arg_711_);
lean_dec_ref(v_arg_710_);
lean_dec_ref_known(v_p_684_, 2);
lean_dec_ref(v_P_664_);
v___y_693_ = v___x_768_;
goto v___jp_692_;
}
else
{
lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_769_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_770_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11);
v___x_771_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_764_, v_options_763_, v___x_770_);
if (v___x_771_ == 0)
{
lean_del_object(v___x_739_);
lean_dec(v_head_726_);
lean_dec_ref(v_arg_711_);
lean_dec_ref(v_arg_710_);
lean_dec_ref_known(v_p_684_, 2);
lean_dec_ref(v_P_664_);
v___y_693_ = v___x_768_;
goto v___jp_692_;
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_772_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10);
v___x_773_ = l_Lean_MessageData_ofExpr(v_p_684_);
if (v_isShared_740_ == 0)
{
lean_ctor_set_tag(v___x_739_, 7);
lean_ctor_set(v___x_739_, 1, v___x_773_);
lean_ctor_set(v___x_739_, 0, v___x_772_);
v___x_775_ = v___x_739_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v___x_773_);
v___x_775_ = v_reuseFailAlloc_794_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_776_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_775_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = l_Lean_MessageData_ofExpr(v_arg_710_);
v___x_779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_777_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15);
v___x_781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
lean_inc_ref(v_arg_691_);
v___x_782_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_head_726_, v_arg_711_, v_P_664_, v_arg_691_);
v___x_783_ = l_Lean_MessageData_ofExpr(v___x_782_);
v___x_784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_781_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v___x_769_, v___x_784_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_dec_ref_known(v___x_785_, 1);
v___y_693_ = v___x_768_;
goto v___jp_692_;
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec_ref(v___x_768_);
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec(v_name_685_);
lean_del_object(v___x_682_);
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec(v_val_760_);
lean_dec_ref(v_h_u03c6_746_);
lean_dec_ref(v_00_u03c6_745_);
lean_del_object(v___x_739_);
lean_dec(v_head_726_);
lean_dec_ref(v_arg_711_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec_ref_known(v_p_684_, 2);
lean_dec(v_name_685_);
lean_del_object(v___x_682_);
lean_dec_ref(v_P_664_);
v_a_795_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_761_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_761_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
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
lean_object* v___x_804_; 
lean_dec(v_a_756_);
lean_dec_ref(v_h_u03c6_746_);
lean_dec_ref(v_00_u03c6_745_);
lean_del_object(v___x_739_);
lean_dec(v_snd_737_);
lean_dec(v_head_726_);
lean_dec_ref(v_arg_711_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec_ref_known(v_p_684_, 2);
lean_dec(v_name_685_);
lean_del_object(v___x_682_);
lean_dec_ref(v_P_664_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_733_);
v___x_804_ = v___x_758_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_733_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec_ref(v_h_u03c6_746_);
lean_dec_ref(v_00_u03c6_745_);
lean_del_object(v___x_739_);
lean_dec(v_snd_737_);
lean_dec(v_head_726_);
lean_dec_ref(v_arg_711_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec_ref_known(v_p_684_, 2);
lean_dec(v_name_685_);
lean_del_object(v___x_682_);
lean_dec_ref(v_P_664_);
v_a_807_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_755_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_755_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_847_; 
lean_dec(v_a_730_);
lean_dec(v_head_726_);
lean_dec_ref(v_arg_711_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec_ref_known(v_p_684_, 2);
lean_dec(v_name_685_);
lean_del_object(v___x_682_);
lean_dec_ref(v_P_664_);
v_a_833_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_847_ == 0)
{
v___x_835_ = v___x_734_;
v_isShared_836_ = v_isSharedCheck_847_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_734_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_847_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
uint8_t v___y_838_; uint8_t v___x_845_; 
v___x_845_ = l_Lean_Exception_isInterrupt(v_a_833_);
if (v___x_845_ == 0)
{
uint8_t v___x_846_; 
lean_inc(v_a_833_);
v___x_846_ = l_Lean_Exception_isRuntime(v_a_833_);
v___y_838_ = v___x_846_;
goto v___jp_837_;
}
else
{
v___y_838_ = v___x_845_;
goto v___jp_837_;
}
v___jp_837_:
{
if (v___y_838_ == 0)
{
lean_object* v___x_840_; 
lean_dec(v_a_833_);
if (v_isShared_836_ == 0)
{
lean_ctor_set_tag(v___x_835_, 0);
lean_ctor_set(v___x_835_, 0, v___x_733_);
v___x_840_ = v___x_835_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_733_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
else
{
lean_object* v___x_843_; 
if (v_isShared_836_ == 0)
{
v___x_843_ = v___x_835_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_833_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec(v_head_726_);
lean_dec_ref(v_arg_711_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec(v_name_685_);
lean_dec_ref_known(v_p_684_, 2);
lean_del_object(v___x_682_);
lean_dec(v_arg_666_);
lean_dec_ref(v_P_664_);
v_a_848_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_729_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_729_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
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
else
{
lean_dec_ref(v_arg_711_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec(v_name_685_);
lean_dec_ref_known(v_p_684_, 2);
lean_del_object(v___x_682_);
lean_dec(v_arg_666_);
lean_dec_ref(v_P_664_);
goto v___jp_676_;
}
}
else
{
lean_dec_ref(v_arg_711_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec(v_name_685_);
lean_dec_ref_known(v_p_684_, 2);
lean_del_object(v___x_682_);
lean_dec(v_arg_666_);
lean_dec_ref(v_P_664_);
goto v___jp_676_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec(v_name_685_);
lean_dec_ref_known(v_p_684_, 2);
lean_del_object(v___x_682_);
lean_dec(v_arg_666_);
lean_dec_ref(v_P_664_);
goto v___jp_676_;
}
}
else
{
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec(v_name_685_);
lean_dec_ref_known(v_p_684_, 2);
lean_del_object(v___x_682_);
lean_dec(v_arg_666_);
lean_dec_ref(v_P_664_);
goto v___jp_676_;
}
}
else
{
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec(v_name_685_);
lean_dec_ref_known(v_p_684_, 2);
lean_del_object(v___x_682_);
lean_dec(v_arg_666_);
lean_dec_ref(v_P_664_);
goto v___jp_676_;
}
}
else
{
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec(v_name_685_);
lean_dec_ref_known(v_p_684_, 2);
lean_del_object(v___x_682_);
lean_dec(v_arg_666_);
lean_dec_ref(v_P_664_);
goto v___jp_676_;
}
}
else
{
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec(v_name_685_);
lean_dec_ref_known(v_p_684_, 2);
lean_del_object(v___x_682_);
lean_dec(v_arg_666_);
lean_dec_ref(v_P_664_);
goto v___jp_676_;
}
}
else
{
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec(v_name_685_);
lean_dec_ref_known(v_p_684_, 2);
lean_del_object(v___x_682_);
lean_dec(v_arg_666_);
lean_dec_ref(v_P_664_);
goto v___jp_676_;
}
}
else
{
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec(v_name_685_);
lean_dec_ref_known(v_p_684_, 2);
lean_del_object(v___x_682_);
lean_dec(v_arg_666_);
lean_dec_ref(v_P_664_);
goto v___jp_676_;
}
}
else
{
lean_dec_ref(v_arg_691_);
lean_del_object(v___x_688_);
lean_dec(v_uniq_686_);
lean_dec(v_name_685_);
lean_dec_ref_known(v_p_684_, 2);
lean_del_object(v___x_682_);
lean_dec(v_arg_666_);
lean_dec_ref(v_P_664_);
goto v___jp_676_;
}
v___jp_692_:
{
lean_object* v___x_695_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 2, v_arg_691_);
v___x_695_ = v___x_688_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_name_685_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_uniq_686_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_arg_691_);
v___x_695_ = v_reuseFailAlloc_702_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_696_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_695_);
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v___y_693_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v___x_697_);
v___x_699_ = v___x_682_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_701_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; 
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_684_);
lean_del_object(v___x_682_);
lean_dec(v_val_680_);
lean_dec(v_arg_666_);
lean_dec_ref(v_P_664_);
goto v___jp_676_;
}
}
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; 
lean_dec(v___x_679_);
lean_dec(v_arg_666_);
lean_dec_ref(v_P_664_);
v___x_859_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18);
v___x_860_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(v___x_859_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
return v___x_860_;
}
v___jp_676_:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_box(0);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___boxed(lean_object* v_P_861_, lean_object* v_QR_862_, lean_object* v_arg_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(v_P_861_, v_QR_862_, v_arg_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
return v_res_873_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__2));
v___x_884_ = l_Lean_stringToMessageData(v___x_883_);
return v___x_884_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_887_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__5));
v___x_888_ = lean_unsigned_to_nat(36u);
v___x_889_ = lean_unsigned_to_nat(73u);
v___x_890_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__4));
v___x_891_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15));
v___x_892_ = l_mkPanicMessageWithDecl(v___x_891_, v___x_890_, v___x_889_, v___x_888_, v___x_887_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(lean_object* v_P_893_, lean_object* v_00_u03a8_894_, lean_object* v_arg_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_00_u03a8_894_);
if (lean_obj_tag(v___x_908_) == 1)
{
lean_object* v_val_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_1044_; 
v_val_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_1044_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_val_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_1044_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_p_913_; 
v_p_913_ = lean_ctor_get(v_val_909_, 2);
lean_inc_ref(v_p_913_);
if (lean_obj_tag(v_p_913_) == 5)
{
lean_object* v_fn_914_; 
v_fn_914_ = lean_ctor_get(v_p_913_, 0);
if (lean_obj_tag(v_fn_914_) == 5)
{
lean_object* v_fn_915_; 
v_fn_915_ = lean_ctor_get(v_fn_914_, 0);
if (lean_obj_tag(v_fn_915_) == 5)
{
lean_object* v_fn_916_; 
v_fn_916_ = lean_ctor_get(v_fn_915_, 0);
if (lean_obj_tag(v_fn_916_) == 4)
{
lean_object* v_declName_917_; 
v_declName_917_ = lean_ctor_get(v_fn_916_, 0);
if (lean_obj_tag(v_declName_917_) == 1)
{
lean_object* v_pre_918_; 
v_pre_918_ = lean_ctor_get(v_declName_917_, 0);
if (lean_obj_tag(v_pre_918_) == 1)
{
lean_object* v_pre_919_; 
v_pre_919_ = lean_ctor_get(v_pre_918_, 0);
if (lean_obj_tag(v_pre_919_) == 1)
{
lean_object* v_pre_920_; 
v_pre_920_ = lean_ctor_get(v_pre_919_, 0);
if (lean_obj_tag(v_pre_920_) == 1)
{
lean_object* v_pre_921_; 
v_pre_921_ = lean_ctor_get(v_pre_920_, 0);
if (lean_obj_tag(v_pre_921_) == 0)
{
lean_object* v_name_922_; lean_object* v_uniq_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_1042_; 
v_name_922_ = lean_ctor_get(v_val_909_, 0);
v_uniq_923_ = lean_ctor_get(v_val_909_, 1);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_val_909_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; 
v_unused_1043_ = lean_ctor_get(v_val_909_, 2);
lean_dec(v_unused_1043_);
v___x_925_ = v_val_909_;
v_isShared_926_ = v_isSharedCheck_1042_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_uniq_923_);
lean_inc(v_name_922_);
lean_dec(v_val_909_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_1042_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v_arg_927_; lean_object* v_arg_928_; lean_object* v_arg_929_; lean_object* v_us_930_; lean_object* v_str_931_; lean_object* v_str_932_; lean_object* v_str_933_; lean_object* v_str_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
v_arg_927_ = lean_ctor_get(v_p_913_, 1);
v_arg_928_ = lean_ctor_get(v_fn_914_, 1);
lean_inc_ref(v_arg_928_);
v_arg_929_ = lean_ctor_get(v_fn_915_, 1);
v_us_930_ = lean_ctor_get(v_fn_916_, 1);
v_str_931_ = lean_ctor_get(v_declName_917_, 1);
v_str_932_ = lean_ctor_get(v_pre_918_, 1);
v_str_933_ = lean_ctor_get(v_pre_919_, 1);
v_str_934_ = lean_ctor_get(v_pre_920_, 1);
v___x_935_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_936_ = lean_string_dec_eq(v_str_934_, v___x_935_);
if (v___x_936_ == 0)
{
lean_dec_ref(v_arg_928_);
lean_del_object(v___x_925_);
lean_dec(v_uniq_923_);
lean_dec(v_name_922_);
lean_dec_ref_known(v_p_913_, 2);
lean_del_object(v___x_911_);
lean_dec(v_arg_895_);
lean_dec_ref(v_P_893_);
goto v___jp_905_;
}
else
{
lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_937_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_938_ = lean_string_dec_eq(v_str_933_, v___x_937_);
if (v___x_938_ == 0)
{
lean_dec_ref(v_arg_928_);
lean_del_object(v___x_925_);
lean_dec(v_uniq_923_);
lean_dec(v_name_922_);
lean_dec_ref_known(v_p_913_, 2);
lean_del_object(v___x_911_);
lean_dec(v_arg_895_);
lean_dec_ref(v_P_893_);
goto v___jp_905_;
}
else
{
lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_939_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_940_ = lean_string_dec_eq(v_str_932_, v___x_939_);
if (v___x_940_ == 0)
{
lean_dec_ref(v_arg_928_);
lean_del_object(v___x_925_);
lean_dec(v_uniq_923_);
lean_dec(v_name_922_);
lean_dec_ref_known(v_p_913_, 2);
lean_del_object(v___x_911_);
lean_dec(v_arg_895_);
lean_dec_ref(v_P_893_);
goto v___jp_905_;
}
else
{
lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_941_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__0));
v___x_942_ = lean_string_dec_eq(v_str_931_, v___x_941_);
if (v___x_942_ == 0)
{
lean_dec_ref(v_arg_928_);
lean_del_object(v___x_925_);
lean_dec(v_uniq_923_);
lean_dec(v_name_922_);
lean_dec_ref_known(v_p_913_, 2);
lean_del_object(v___x_911_);
lean_dec(v_arg_895_);
lean_dec_ref(v_P_893_);
goto v___jp_905_;
}
else
{
if (lean_obj_tag(v_us_930_) == 1)
{
lean_object* v_tail_943_; 
v_tail_943_ = lean_ctor_get(v_us_930_, 1);
lean_inc(v_tail_943_);
if (lean_obj_tag(v_tail_943_) == 1)
{
lean_object* v_tail_944_; 
v_tail_944_ = lean_ctor_get(v_tail_943_, 1);
if (lean_obj_tag(v_tail_944_) == 0)
{
lean_object* v_head_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_1040_; 
v_head_945_ = lean_ctor_get(v_tail_943_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_tail_943_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; 
v_unused_1041_ = lean_ctor_get(v_tail_943_, 1);
lean_dec(v_unused_1041_);
v___x_947_ = v_tail_943_;
v_isShared_948_ = v_isSharedCheck_1040_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_head_945_);
lean_dec(v_tail_943_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_1040_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
lean_inc_ref(v_arg_929_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v_arg_929_);
v___x_950_ = v___x_911_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_arg_929_);
v___x_950_ = v_reuseFailAlloc_1039_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_951_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2));
v___x_952_ = lean_box(0);
v___x_953_ = l_Lean_Elab_Tactic_elabTermWithHoles(v_arg_895_, v___x_950_, v___x_951_, v___x_942_, v___x_952_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v_fst_955_; lean_object* v_snd_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_1023_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
v_fst_955_ = lean_ctor_get(v_a_954_, 0);
v_snd_956_ = lean_ctor_get(v_a_954_, 1);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_a_954_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_958_ = v_a_954_;
v_isShared_959_ = v_isSharedCheck_1023_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_snd_956_);
lean_inc(v_fst_955_);
lean_dec(v_a_954_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_1023_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_Elab_Tactic_pushGoals___redArg(v_snd_956_, v_a_897_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_1013_; 
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_1013_ == 0)
{
lean_object* v_unused_1014_; 
v_unused_1014_ = lean_ctor_get(v___x_960_, 0);
lean_dec(v_unused_1014_);
v___x_962_ = v___x_960_;
v_isShared_963_ = v_isSharedCheck_1013_;
goto v_resetjp_961_;
}
else
{
lean_dec(v___x_960_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_1013_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v_toCold_964_; lean_object* v_options_965_; lean_object* v_inheritedTraceOptions_966_; uint8_t v_hasTrace_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_toCold_964_ = lean_ctor_get(v_a_902_, 0);
v_options_965_ = lean_ctor_get(v_toCold_964_, 2);
v_inheritedTraceOptions_966_ = lean_ctor_get(v_toCold_964_, 11);
v_hasTrace_967_ = lean_ctor_get_uint8(v_options_965_, sizeof(void*)*1);
v___x_968_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1));
lean_inc_ref(v_us_930_);
v___x_969_ = l_Lean_mkConst(v___x_968_, v_us_930_);
lean_inc_n(v_fst_955_, 2);
lean_inc_ref(v_P_893_);
lean_inc_ref_n(v_arg_927_, 2);
lean_inc_ref(v_arg_928_);
lean_inc_ref(v_arg_929_);
v___x_970_ = l_Lean_mkApp5(v___x_969_, v_arg_929_, v_arg_928_, v_arg_927_, v_P_893_, v_fst_955_);
v___x_971_ = lean_unsigned_to_nat(1u);
v___x_972_ = lean_mk_empty_array_with_capacity(v___x_971_);
v___x_973_ = lean_array_push(v___x_972_, v_fst_955_);
v___x_974_ = l_Lean_Expr_beta(v_arg_927_, v___x_973_);
if (v_hasTrace_967_ == 0)
{
lean_dec(v_fst_955_);
lean_del_object(v___x_947_);
lean_dec(v_head_945_);
lean_dec_ref(v_arg_928_);
lean_dec_ref_known(v_p_913_, 2);
lean_dec_ref(v_P_893_);
goto v___jp_975_;
}
else
{
lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_987_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_988_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11);
v___x_989_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_966_, v_options_965_, v___x_988_);
if (v___x_989_ == 0)
{
lean_dec(v_fst_955_);
lean_del_object(v___x_947_);
lean_dec(v_head_945_);
lean_dec_ref(v_arg_928_);
lean_dec_ref_known(v_p_913_, 2);
lean_dec_ref(v_P_893_);
goto v___jp_975_;
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_990_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3);
v___x_991_ = l_Lean_MessageData_ofExpr(v_p_913_);
if (v_isShared_948_ == 0)
{
lean_ctor_set_tag(v___x_947_, 7);
lean_ctor_set(v___x_947_, 1, v___x_991_);
lean_ctor_set(v___x_947_, 0, v___x_990_);
v___x_993_ = v___x_947_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_990_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v___x_991_);
v___x_993_ = v_reuseFailAlloc_1012_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_994_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = l_Lean_MessageData_ofExpr(v_fst_955_);
v___x_997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
lean_inc_ref(v___x_974_);
v___x_1000_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_head_945_, v_arg_928_, v_P_893_, v___x_974_);
v___x_1001_ = l_Lean_MessageData_ofExpr(v___x_1000_);
v___x_1002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_999_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v___x_987_, v___x_1002_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_dec_ref_known(v___x_1003_, 1);
goto v___jp_975_;
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v___x_974_);
lean_dec_ref(v___x_970_);
lean_del_object(v___x_962_);
lean_del_object(v___x_958_);
lean_del_object(v___x_925_);
lean_dec(v_uniq_923_);
lean_dec(v_name_922_);
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
}
v___jp_975_:
{
lean_object* v___x_977_; 
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 2, v___x_974_);
v___x_977_ = v___x_925_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_name_922_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_uniq_923_);
lean_ctor_set(v_reuseFailAlloc_986_, 2, v___x_974_);
v___x_977_ = v_reuseFailAlloc_986_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_977_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 1, v___x_970_);
lean_ctor_set(v___x_958_, 0, v___x_978_);
v___x_980_ = v___x_958_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___x_970_);
v___x_980_ = v_reuseFailAlloc_985_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 0, v___x_981_);
v___x_983_ = v___x_962_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_del_object(v___x_958_);
lean_dec(v_fst_955_);
lean_del_object(v___x_947_);
lean_dec(v_head_945_);
lean_dec_ref(v_arg_928_);
lean_del_object(v___x_925_);
lean_dec(v_uniq_923_);
lean_dec(v_name_922_);
lean_dec_ref_known(v_p_913_, 2);
lean_dec_ref(v_P_893_);
v_a_1015_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_960_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_960_);
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
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1038_; 
lean_del_object(v___x_947_);
lean_dec(v_head_945_);
lean_dec_ref(v_arg_928_);
lean_del_object(v___x_925_);
lean_dec(v_uniq_923_);
lean_dec(v_name_922_);
lean_dec_ref_known(v_p_913_, 2);
lean_dec_ref(v_P_893_);
v_a_1024_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1026_ = v___x_953_;
v_isShared_1027_ = v_isSharedCheck_1038_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_953_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1038_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
uint8_t v___y_1029_; uint8_t v___x_1036_; 
v___x_1036_ = l_Lean_Exception_isInterrupt(v_a_1024_);
if (v___x_1036_ == 0)
{
uint8_t v___x_1037_; 
lean_inc(v_a_1024_);
v___x_1037_ = l_Lean_Exception_isRuntime(v_a_1024_);
v___y_1029_ = v___x_1037_;
goto v___jp_1028_;
}
else
{
v___y_1029_ = v___x_1036_;
goto v___jp_1028_;
}
v___jp_1028_:
{
if (v___y_1029_ == 0)
{
lean_object* v___x_1031_; 
lean_dec(v_a_1024_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set_tag(v___x_1026_, 0);
lean_ctor_set(v___x_1026_, 0, v___x_952_);
v___x_1031_ = v___x_1026_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_952_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
else
{
lean_object* v___x_1034_; 
if (v_isShared_1027_ == 0)
{
v___x_1034_ = v___x_1026_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1024_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
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
lean_dec_ref_known(v_tail_943_, 2);
lean_dec_ref(v_arg_928_);
lean_del_object(v___x_925_);
lean_dec(v_uniq_923_);
lean_dec(v_name_922_);
lean_dec_ref_known(v_p_913_, 2);
lean_del_object(v___x_911_);
lean_dec(v_arg_895_);
lean_dec_ref(v_P_893_);
goto v___jp_905_;
}
}
else
{
lean_dec(v_tail_943_);
lean_dec_ref(v_arg_928_);
lean_del_object(v___x_925_);
lean_dec(v_uniq_923_);
lean_dec(v_name_922_);
lean_dec_ref_known(v_p_913_, 2);
lean_del_object(v___x_911_);
lean_dec(v_arg_895_);
lean_dec_ref(v_P_893_);
goto v___jp_905_;
}
}
else
{
lean_dec_ref(v_arg_928_);
lean_del_object(v___x_925_);
lean_dec(v_uniq_923_);
lean_dec(v_name_922_);
lean_dec_ref_known(v_p_913_, 2);
lean_del_object(v___x_911_);
lean_dec(v_arg_895_);
lean_dec_ref(v_P_893_);
goto v___jp_905_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_p_913_, 2);
lean_del_object(v___x_911_);
lean_dec(v_val_909_);
lean_dec(v_arg_895_);
lean_dec_ref(v_P_893_);
goto v___jp_905_;
}
}
else
{
lean_dec_ref_known(v_p_913_, 2);
lean_del_object(v___x_911_);
lean_dec(v_val_909_);
lean_dec(v_arg_895_);
lean_dec_ref(v_P_893_);
goto v___jp_905_;
}
}
else
{
lean_dec_ref_known(v_p_913_, 2);
lean_del_object(v___x_911_);
lean_dec(v_val_909_);
lean_dec(v_arg_895_);
lean_dec_ref(v_P_893_);
goto v___jp_905_;
}
}
else
{
lean_dec_ref_known(v_p_913_, 2);
lean_del_object(v___x_911_);
lean_dec(v_val_909_);
lean_dec(v_arg_895_);
lean_dec_ref(v_P_893_);
goto v___jp_905_;
}
}
else
{
lean_dec_ref_known(v_p_913_, 2);
lean_del_object(v___x_911_);
lean_dec(v_val_909_);
lean_dec(v_arg_895_);
lean_dec_ref(v_P_893_);
goto v___jp_905_;
}
}
else
{
lean_dec_ref_known(v_p_913_, 2);
lean_del_object(v___x_911_);
lean_dec(v_val_909_);
lean_dec(v_arg_895_);
lean_dec_ref(v_P_893_);
goto v___jp_905_;
}
}
else
{
lean_dec_ref_known(v_p_913_, 2);
lean_del_object(v___x_911_);
lean_dec(v_val_909_);
lean_dec(v_arg_895_);
lean_dec_ref(v_P_893_);
goto v___jp_905_;
}
}
else
{
lean_dec_ref_known(v_p_913_, 2);
lean_del_object(v___x_911_);
lean_dec(v_val_909_);
lean_dec(v_arg_895_);
lean_dec_ref(v_P_893_);
goto v___jp_905_;
}
}
else
{
lean_dec_ref(v_p_913_);
lean_del_object(v___x_911_);
lean_dec(v_val_909_);
lean_dec(v_arg_895_);
lean_dec_ref(v_P_893_);
goto v___jp_905_;
}
}
}
else
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_dec(v___x_908_);
lean_dec(v_arg_895_);
lean_dec_ref(v_P_893_);
v___x_1045_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6);
v___x_1046_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(v___x_1045_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
return v___x_1046_;
}
v___jp_905_:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = lean_box(0);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
return v___x_907_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___boxed(lean_object* v_P_1047_, lean_object* v_00_u03a8_1048_, lean_object* v_arg_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(v_P_1047_, v_00_u03a8_1048_, v_arg_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
return v_res_1059_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1060_ = lean_box(0);
v___x_1061_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v___x_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg(){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0);
v___x_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___boxed(lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0(lean_object* v_00_u03b1_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___boxed(lean_object* v_00_u03b1_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0(v_00_u03b1_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(lean_object* v_msg_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v___f_1101_; lean_object* v___x_5040__overap_1102_; lean_object* v___x_1103_; 
v___f_1101_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3___closed__0));
v___x_5040__overap_1102_ = lean_panic_fn_borrowed(v___f_1101_, v_msg_1091_);
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1096_);
lean_inc(v___y_1095_);
lean_inc_ref(v___y_1094_);
lean_inc(v___y_1093_);
lean_inc_ref(v___y_1092_);
v___x_1103_ = lean_apply_9(v___x_5040__overap_1102_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, lean_box(0));
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3___boxed(lean_object* v_msg_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(v_msg_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0(lean_object* v_x_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; 
lean_inc(v___y_1119_);
lean_inc_ref(v___y_1118_);
lean_inc(v___y_1117_);
lean_inc_ref(v___y_1116_);
v___x_1125_ = lean_apply_9(v_x_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, lean_box(0));
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0___boxed(lean_object* v_x_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0(v_x_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(lean_object* v_mvarId_1137_, lean_object* v_x_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v___f_1148_; lean_object* v___x_1149_; 
lean_inc(v___y_1142_);
lean_inc_ref(v___y_1141_);
lean_inc(v___y_1140_);
lean_inc_ref(v___y_1139_);
v___f_1148_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1148_, 0, v_x_1138_);
lean_closure_set(v___f_1148_, 1, v___y_1139_);
lean_closure_set(v___f_1148_, 2, v___y_1140_);
lean_closure_set(v___f_1148_, 3, v___y_1141_);
lean_closure_set(v___f_1148_, 4, v___y_1142_);
v___x_1149_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1137_, v___f_1148_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1149_) == 0)
{
return v___x_1149_;
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___boxed(lean_object* v_mvarId_1158_, lean_object* v_x_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_mvarId_1158_, v_x_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4(lean_object* v_00_u03b1_1170_, lean_object* v_mvarId_1171_, lean_object* v_x_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_mvarId_1171_, v_x_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___boxed(lean_object* v_00_u03b1_1183_, lean_object* v_mvarId_1184_, lean_object* v_x_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4(v_00_u03b1_1183_, v_mvarId_1184_, v_x_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0(lean_object* v___x_1198_, lean_object* v___x_1199_, lean_object* v___x_1200_, lean_object* v___x_1201_, lean_object* v___x_1202_, lean_object* v___x_1203_, lean_object* v___x_1204_, lean_object* v_fst_1205_, lean_object* v_fst_1206_, lean_object* v___x_1207_, lean_object* v_snd_1208_, lean_object* v_snd_1209_, lean_object* v_hgoal_1210_){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1211_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__0));
v___x_1212_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__1));
v___x_1213_ = l_Lean_Name_mkStr5(v___x_1198_, v___x_1199_, v___x_1200_, v___x_1211_, v___x_1212_);
v___x_1214_ = l_Lean_mkConst(v___x_1213_, v___x_1201_);
lean_inc_ref(v___x_1204_);
lean_inc_ref_n(v___x_1203_, 2);
lean_inc(v___x_1202_);
v___x_1215_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v___x_1202_, v___x_1203_, v___x_1204_, v_fst_1205_);
v___x_1216_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v___x_1202_, v___x_1203_, v___x_1204_, v_fst_1206_);
v___x_1217_ = l_Lean_mkApp6(v___x_1214_, v___x_1203_, v___x_1215_, v___x_1216_, v___x_1207_, v_snd_1208_, v_hgoal_1210_);
v___x_1218_ = lean_apply_1(v_snd_1209_, v___x_1217_);
return v___x_1218_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__0));
v___x_1221_ = l_Lean_stringToMessageData(v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1(lean_object* v___x_1222_, lean_object* v___x_1223_, lean_object* v___x_1224_, lean_object* v___x_1225_, lean_object* v___x_1226_, lean_object* v_as_1227_, size_t v_sz_1228_, size_t v_i_1229_, lean_object* v_b_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_a_1241_; uint8_t v___x_1245_; 
v___x_1245_ = lean_usize_dec_lt(v_i_1229_, v_sz_1228_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; 
lean_dec_ref(v___x_1226_);
lean_dec_ref(v___x_1225_);
lean_dec_ref(v___x_1224_);
lean_dec(v___x_1223_);
lean_dec(v___x_1222_);
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v_b_1230_);
return v___x_1246_;
}
else
{
lean_object* v_fst_1247_; lean_object* v_snd_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1302_; 
v_fst_1247_ = lean_ctor_get(v_b_1230_, 0);
v_snd_1248_ = lean_ctor_get(v_b_1230_, 1);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_b_1230_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1250_ = v_b_1230_;
v_isShared_1251_ = v_isSharedCheck_1302_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_snd_1248_);
lean_inc(v_fst_1247_);
lean_dec(v_b_1230_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1302_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v_a_1255_; lean_object* v___y_1257_; lean_object* v___x_1297_; 
v___x_1252_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_1253_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1254_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v_a_1255_ = lean_array_uget_borrowed(v_as_1227_, v_i_1229_);
lean_inc(v_a_1255_);
lean_inc(v_fst_1247_);
lean_inc_ref(v___x_1225_);
v___x_1297_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(v___x_1225_, v_fst_1247_, v_a_1255_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
if (lean_obj_tag(v_a_1298_) == 0)
{
lean_object* v___x_1299_; 
lean_dec_ref_known(v___x_1297_, 1);
lean_inc(v_a_1255_);
lean_inc(v_fst_1247_);
lean_inc_ref(v___x_1225_);
v___x_1299_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(v___x_1225_, v_fst_1247_, v_a_1255_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
if (lean_obj_tag(v_a_1300_) == 0)
{
lean_object* v___x_1301_; 
lean_dec_ref_known(v___x_1299_, 1);
lean_inc(v_a_1255_);
lean_inc(v_fst_1247_);
lean_inc_ref(v___x_1225_);
v___x_1301_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(v___x_1225_, v_fst_1247_, v_a_1255_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
v___y_1257_ = v___x_1301_;
goto v___jp_1256_;
}
else
{
lean_dec_ref_known(v_a_1300_, 1);
v___y_1257_ = v___x_1299_;
goto v___jp_1256_;
}
}
else
{
v___y_1257_ = v___x_1299_;
goto v___jp_1256_;
}
}
else
{
lean_dec_ref_known(v_a_1298_, 1);
v___y_1257_ = v___x_1297_;
goto v___jp_1256_;
}
}
else
{
v___y_1257_ = v___x_1297_;
goto v___jp_1256_;
}
v___jp_1256_:
{
if (lean_obj_tag(v___y_1257_) == 0)
{
lean_object* v_a_1258_; 
v_a_1258_ = lean_ctor_get(v___y_1257_, 0);
lean_inc(v_a_1258_);
lean_dec_ref_known(v___y_1257_, 1);
if (lean_obj_tag(v_a_1258_) == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1259_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1);
lean_inc(v_fst_1247_);
v___x_1260_ = l_Lean_MessageData_ofExpr(v_fst_1247_);
v___x_1261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1259_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_1263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1261_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
lean_inc(v_a_1255_);
v___x_1264_ = l_Lean_MessageData_ofSyntax(v_a_1255_);
v___x_1265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1263_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_1265_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v___x_1268_; 
lean_dec_ref_known(v___x_1266_, 1);
if (v_isShared_1251_ == 0)
{
v___x_1268_ = v___x_1250_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_fst_1247_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_snd_1248_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
v_a_1241_ = v___x_1268_;
goto v___jp_1240_;
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_del_object(v___x_1250_);
lean_dec(v_snd_1248_);
lean_dec(v_fst_1247_);
lean_dec_ref(v___x_1226_);
lean_dec_ref(v___x_1225_);
lean_dec_ref(v___x_1224_);
lean_dec(v___x_1223_);
lean_dec(v___x_1222_);
v_a_1270_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1266_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1266_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
else
{
lean_object* v_val_1278_; lean_object* v_fst_1279_; lean_object* v_snd_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1288_; 
lean_del_object(v___x_1250_);
v_val_1278_ = lean_ctor_get(v_a_1258_, 0);
lean_inc(v_val_1278_);
lean_dec_ref_known(v_a_1258_, 1);
v_fst_1279_ = lean_ctor_get(v_val_1278_, 0);
v_snd_1280_ = lean_ctor_get(v_val_1278_, 1);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_val_1278_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1282_ = v_val_1278_;
v_isShared_1283_ = v_isSharedCheck_1288_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_snd_1280_);
lean_inc(v_fst_1279_);
lean_dec(v_val_1278_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1288_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___f_1284_; lean_object* v___x_1286_; 
lean_inc_ref(v___x_1226_);
lean_inc(v_fst_1279_);
lean_inc_ref(v___x_1225_);
lean_inc_ref(v___x_1224_);
lean_inc(v___x_1223_);
lean_inc(v___x_1222_);
v___f_1284_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0), 13, 12);
lean_closure_set(v___f_1284_, 0, v___x_1252_);
lean_closure_set(v___f_1284_, 1, v___x_1253_);
lean_closure_set(v___f_1284_, 2, v___x_1254_);
lean_closure_set(v___f_1284_, 3, v___x_1222_);
lean_closure_set(v___f_1284_, 4, v___x_1223_);
lean_closure_set(v___f_1284_, 5, v___x_1224_);
lean_closure_set(v___f_1284_, 6, v___x_1225_);
lean_closure_set(v___f_1284_, 7, v_fst_1247_);
lean_closure_set(v___f_1284_, 8, v_fst_1279_);
lean_closure_set(v___f_1284_, 9, v___x_1226_);
lean_closure_set(v___f_1284_, 10, v_snd_1280_);
lean_closure_set(v___f_1284_, 11, v_snd_1248_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 1, v___f_1284_);
v___x_1286_ = v___x_1282_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_fst_1279_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v___f_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
v_a_1241_ = v___x_1286_;
goto v___jp_1240_;
}
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_del_object(v___x_1250_);
lean_dec(v_snd_1248_);
lean_dec(v_fst_1247_);
lean_dec_ref(v___x_1226_);
lean_dec_ref(v___x_1225_);
lean_dec_ref(v___x_1224_);
lean_dec(v___x_1223_);
lean_dec(v___x_1222_);
v_a_1289_ = lean_ctor_get(v___y_1257_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___y_1257_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___y_1257_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___y_1257_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
}
v___jp_1240_:
{
size_t v___x_1242_; size_t v___x_1243_; 
v___x_1242_ = ((size_t)1ULL);
v___x_1243_ = lean_usize_add(v_i_1229_, v___x_1242_);
v_i_1229_ = v___x_1243_;
v_b_1230_ = v_a_1241_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___boxed(lean_object** _args){
lean_object* v___x_1303_ = _args[0];
lean_object* v___x_1304_ = _args[1];
lean_object* v___x_1305_ = _args[2];
lean_object* v___x_1306_ = _args[3];
lean_object* v___x_1307_ = _args[4];
lean_object* v_as_1308_ = _args[5];
lean_object* v_sz_1309_ = _args[6];
lean_object* v_i_1310_ = _args[7];
lean_object* v_b_1311_ = _args[8];
lean_object* v___y_1312_ = _args[9];
lean_object* v___y_1313_ = _args[10];
lean_object* v___y_1314_ = _args[11];
lean_object* v___y_1315_ = _args[12];
lean_object* v___y_1316_ = _args[13];
lean_object* v___y_1317_ = _args[14];
lean_object* v___y_1318_ = _args[15];
lean_object* v___y_1319_ = _args[16];
lean_object* v___y_1320_ = _args[17];
_start:
{
size_t v_sz_boxed_1321_; size_t v_i_boxed_1322_; lean_object* v_res_1323_; 
v_sz_boxed_1321_ = lean_unbox_usize(v_sz_1309_);
lean_dec(v_sz_1309_);
v_i_boxed_1322_ = lean_unbox_usize(v_i_1310_);
lean_dec(v_i_1310_);
v_res_1323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1(v___x_1303_, v___x_1304_, v___x_1305_, v___x_1306_, v___x_1307_, v_as_1308_, v_sz_boxed_1321_, v_i_boxed_1322_, v_b_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec_ref(v_as_1308_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7___redArg(lean_object* v_x_1324_, lean_object* v_x_1325_, lean_object* v_x_1326_, lean_object* v_x_1327_){
_start:
{
lean_object* v_ks_1328_; lean_object* v_vs_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1353_; 
v_ks_1328_ = lean_ctor_get(v_x_1324_, 0);
v_vs_1329_ = lean_ctor_get(v_x_1324_, 1);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_x_1324_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1331_ = v_x_1324_;
v_isShared_1332_ = v_isSharedCheck_1353_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_vs_1329_);
lean_inc(v_ks_1328_);
lean_dec(v_x_1324_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1353_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1333_ = lean_array_get_size(v_ks_1328_);
v___x_1334_ = lean_nat_dec_lt(v_x_1325_, v___x_1333_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1338_; 
lean_dec(v_x_1325_);
v___x_1335_ = lean_array_push(v_ks_1328_, v_x_1326_);
v___x_1336_ = lean_array_push(v_vs_1329_, v_x_1327_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 1, v___x_1336_);
lean_ctor_set(v___x_1331_, 0, v___x_1335_);
v___x_1338_ = v___x_1331_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
else
{
lean_object* v_k_x27_1340_; uint8_t v___x_1341_; 
v_k_x27_1340_ = lean_array_fget_borrowed(v_ks_1328_, v_x_1325_);
v___x_1341_ = l_Lean_instBEqMVarId_beq(v_x_1326_, v_k_x27_1340_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1343_; 
if (v_isShared_1332_ == 0)
{
v___x_1343_ = v___x_1331_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_ks_1328_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_vs_1329_);
v___x_1343_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = lean_unsigned_to_nat(1u);
v___x_1345_ = lean_nat_add(v_x_1325_, v___x_1344_);
lean_dec(v_x_1325_);
v_x_1324_ = v___x_1343_;
v_x_1325_ = v___x_1345_;
goto _start;
}
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1348_ = lean_array_fset(v_ks_1328_, v_x_1325_, v_x_1326_);
v___x_1349_ = lean_array_fset(v_vs_1329_, v_x_1325_, v_x_1327_);
lean_dec(v_x_1325_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 1, v___x_1349_);
lean_ctor_set(v___x_1331_, 0, v___x_1348_);
v___x_1351_ = v___x_1331_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6___redArg(lean_object* v_n_1354_, lean_object* v_k_1355_, lean_object* v_v_1356_){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7___redArg(v_n_1354_, v___x_1357_, v_k_1355_, v_v_1356_);
return v___x_1358_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(lean_object* v_x_1360_, size_t v_x_1361_, size_t v_x_1362_, lean_object* v_x_1363_, lean_object* v_x_1364_){
_start:
{
if (lean_obj_tag(v_x_1360_) == 0)
{
lean_object* v_es_1365_; size_t v___x_1366_; size_t v___x_1367_; lean_object* v_j_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v_es_1365_ = lean_ctor_get(v_x_1360_, 0);
v___x_1366_ = ((size_t)31ULL);
v___x_1367_ = lean_usize_land(v_x_1361_, v___x_1366_);
v_j_1368_ = lean_usize_to_nat(v___x_1367_);
v___x_1369_ = lean_array_get_size(v_es_1365_);
v___x_1370_ = lean_nat_dec_lt(v_j_1368_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_dec(v_j_1368_);
lean_dec(v_x_1364_);
lean_dec(v_x_1363_);
return v_x_1360_;
}
else
{
lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1409_; 
lean_inc_ref(v_es_1365_);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_x_1360_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; 
v_unused_1410_ = lean_ctor_get(v_x_1360_, 0);
lean_dec(v_unused_1410_);
v___x_1372_ = v_x_1360_;
v_isShared_1373_ = v_isSharedCheck_1409_;
goto v_resetjp_1371_;
}
else
{
lean_dec(v_x_1360_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1409_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v_v_1374_; lean_object* v___x_1375_; lean_object* v_xs_x27_1376_; lean_object* v___y_1378_; 
v_v_1374_ = lean_array_fget(v_es_1365_, v_j_1368_);
v___x_1375_ = lean_box(0);
v_xs_x27_1376_ = lean_array_fset(v_es_1365_, v_j_1368_, v___x_1375_);
switch(lean_obj_tag(v_v_1374_))
{
case 0:
{
lean_object* v_key_1383_; lean_object* v_val_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1394_; 
v_key_1383_ = lean_ctor_get(v_v_1374_, 0);
v_val_1384_ = lean_ctor_get(v_v_1374_, 1);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_v_1374_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1386_ = v_v_1374_;
v_isShared_1387_ = v_isSharedCheck_1394_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_val_1384_);
lean_inc(v_key_1383_);
lean_dec(v_v_1374_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1394_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
uint8_t v___x_1388_; 
v___x_1388_ = l_Lean_instBEqMVarId_beq(v_x_1363_, v_key_1383_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_del_object(v___x_1386_);
v___x_1389_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1383_, v_val_1384_, v_x_1363_, v_x_1364_);
v___x_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
v___y_1378_ = v___x_1390_;
goto v___jp_1377_;
}
else
{
lean_object* v___x_1392_; 
lean_dec(v_val_1384_);
lean_dec(v_key_1383_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 1, v_x_1364_);
lean_ctor_set(v___x_1386_, 0, v_x_1363_);
v___x_1392_ = v___x_1386_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_x_1363_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_x_1364_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
v___y_1378_ = v___x_1392_;
goto v___jp_1377_;
}
}
}
}
case 1:
{
lean_object* v_node_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1407_; 
v_node_1395_ = lean_ctor_get(v_v_1374_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_v_1374_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1397_ = v_v_1374_;
v_isShared_1398_ = v_isSharedCheck_1407_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_node_1395_);
lean_dec(v_v_1374_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1407_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
size_t v___x_1399_; size_t v___x_1400_; size_t v___x_1401_; size_t v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1399_ = ((size_t)5ULL);
v___x_1400_ = lean_usize_shift_right(v_x_1361_, v___x_1399_);
v___x_1401_ = ((size_t)1ULL);
v___x_1402_ = lean_usize_add(v_x_1362_, v___x_1401_);
v___x_1403_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_node_1395_, v___x_1400_, v___x_1402_, v_x_1363_, v_x_1364_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1403_);
v___x_1405_ = v___x_1397_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
v___y_1378_ = v___x_1405_;
goto v___jp_1377_;
}
}
}
default: 
{
lean_object* v___x_1408_; 
v___x_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1408_, 0, v_x_1363_);
lean_ctor_set(v___x_1408_, 1, v_x_1364_);
v___y_1378_ = v___x_1408_;
goto v___jp_1377_;
}
}
v___jp_1377_:
{
lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1379_ = lean_array_fset(v_xs_x27_1376_, v_j_1368_, v___y_1378_);
lean_dec(v_j_1368_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1379_);
v___x_1381_ = v___x_1372_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
else
{
lean_object* v_ks_1411_; lean_object* v_vs_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1430_; 
v_ks_1411_ = lean_ctor_get(v_x_1360_, 0);
v_vs_1412_ = lean_ctor_get(v_x_1360_, 1);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_x_1360_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1414_ = v_x_1360_;
v_isShared_1415_ = v_isSharedCheck_1430_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_vs_1412_);
lean_inc(v_ks_1411_);
lean_dec(v_x_1360_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1430_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_ks_1411_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_vs_1412_);
v___x_1417_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v_newNode_1418_; size_t v___x_1419_; uint8_t v___x_1420_; 
v_newNode_1418_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6___redArg(v___x_1417_, v_x_1363_, v_x_1364_);
v___x_1419_ = ((size_t)7ULL);
v___x_1420_ = lean_usize_dec_le(v___x_1419_, v_x_1362_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___x_1421_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1418_);
v___x_1422_ = lean_unsigned_to_nat(4u);
v___x_1423_ = lean_nat_dec_lt(v___x_1421_, v___x_1422_);
lean_dec(v___x_1421_);
if (v___x_1423_ == 0)
{
lean_object* v_ks_1424_; lean_object* v_vs_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_ks_1424_ = lean_ctor_get(v_newNode_1418_, 0);
lean_inc_ref(v_ks_1424_);
v_vs_1425_ = lean_ctor_get(v_newNode_1418_, 1);
lean_inc_ref(v_vs_1425_);
lean_dec_ref(v_newNode_1418_);
v___x_1426_ = lean_unsigned_to_nat(0u);
v___x_1427_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0);
v___x_1428_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(v_x_1362_, v_ks_1424_, v_vs_1425_, v___x_1426_, v___x_1427_);
lean_dec_ref(v_vs_1425_);
lean_dec_ref(v_ks_1424_);
return v___x_1428_;
}
else
{
return v_newNode_1418_;
}
}
else
{
return v_newNode_1418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(size_t v_depth_1431_, lean_object* v_keys_1432_, lean_object* v_vals_1433_, lean_object* v_i_1434_, lean_object* v_entries_1435_){
_start:
{
lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1436_ = lean_array_get_size(v_keys_1432_);
v___x_1437_ = lean_nat_dec_lt(v_i_1434_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_dec(v_i_1434_);
return v_entries_1435_;
}
else
{
lean_object* v_k_1438_; lean_object* v_v_1439_; uint64_t v___x_1440_; size_t v_h_1441_; size_t v___x_1442_; lean_object* v___x_1443_; size_t v___x_1444_; size_t v___x_1445_; size_t v___x_1446_; size_t v_h_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_k_1438_ = lean_array_fget_borrowed(v_keys_1432_, v_i_1434_);
v_v_1439_ = lean_array_fget_borrowed(v_vals_1433_, v_i_1434_);
v___x_1440_ = l_Lean_instHashableMVarId_hash(v_k_1438_);
v_h_1441_ = lean_uint64_to_usize(v___x_1440_);
v___x_1442_ = ((size_t)5ULL);
v___x_1443_ = lean_unsigned_to_nat(1u);
v___x_1444_ = ((size_t)1ULL);
v___x_1445_ = lean_usize_sub(v_depth_1431_, v___x_1444_);
v___x_1446_ = lean_usize_mul(v___x_1442_, v___x_1445_);
v_h_1447_ = lean_usize_shift_right(v_h_1441_, v___x_1446_);
v___x_1448_ = lean_nat_add(v_i_1434_, v___x_1443_);
lean_dec(v_i_1434_);
lean_inc(v_v_1439_);
lean_inc(v_k_1438_);
v___x_1449_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_entries_1435_, v_h_1447_, v_depth_1431_, v_k_1438_, v_v_1439_);
v_i_1434_ = v___x_1448_;
v_entries_1435_ = v___x_1449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_depth_1451_, lean_object* v_keys_1452_, lean_object* v_vals_1453_, lean_object* v_i_1454_, lean_object* v_entries_1455_){
_start:
{
size_t v_depth_boxed_1456_; lean_object* v_res_1457_; 
v_depth_boxed_1456_ = lean_unbox_usize(v_depth_1451_);
lean_dec(v_depth_1451_);
v_res_1457_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(v_depth_boxed_1456_, v_keys_1452_, v_vals_1453_, v_i_1454_, v_entries_1455_);
lean_dec_ref(v_vals_1453_);
lean_dec_ref(v_keys_1452_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_x_1458_, lean_object* v_x_1459_, lean_object* v_x_1460_, lean_object* v_x_1461_, lean_object* v_x_1462_){
_start:
{
size_t v_x_7379__boxed_1463_; size_t v_x_7380__boxed_1464_; lean_object* v_res_1465_; 
v_x_7379__boxed_1463_ = lean_unbox_usize(v_x_1459_);
lean_dec(v_x_1459_);
v_x_7380__boxed_1464_ = lean_unbox_usize(v_x_1460_);
lean_dec(v_x_1460_);
v_res_1465_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_x_1458_, v_x_7379__boxed_1463_, v_x_7380__boxed_1464_, v_x_1461_, v_x_1462_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2___redArg(lean_object* v_x_1466_, lean_object* v_x_1467_, lean_object* v_x_1468_){
_start:
{
uint64_t v___x_1469_; size_t v___x_1470_; size_t v___x_1471_; lean_object* v___x_1472_; 
v___x_1469_ = l_Lean_instHashableMVarId_hash(v_x_1467_);
v___x_1470_ = lean_uint64_to_usize(v___x_1469_);
v___x_1471_ = ((size_t)1ULL);
v___x_1472_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_x_1466_, v___x_1470_, v___x_1471_, v_x_1467_, v_x_1468_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(lean_object* v_mvarId_1473_, lean_object* v_val_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v___x_1477_; lean_object* v_mctx_1478_; lean_object* v_cache_1479_; lean_object* v_zetaDeltaFVarIds_1480_; lean_object* v_postponed_1481_; lean_object* v_diag_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1511_; 
v___x_1477_ = lean_st_ref_take(v___y_1475_);
v_mctx_1478_ = lean_ctor_get(v___x_1477_, 0);
v_cache_1479_ = lean_ctor_get(v___x_1477_, 1);
v_zetaDeltaFVarIds_1480_ = lean_ctor_get(v___x_1477_, 2);
v_postponed_1481_ = lean_ctor_get(v___x_1477_, 3);
v_diag_1482_ = lean_ctor_get(v___x_1477_, 4);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1484_ = v___x_1477_;
v_isShared_1485_ = v_isSharedCheck_1511_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_diag_1482_);
lean_inc(v_postponed_1481_);
lean_inc(v_zetaDeltaFVarIds_1480_);
lean_inc(v_cache_1479_);
lean_inc(v_mctx_1478_);
lean_dec(v___x_1477_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1511_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v_depth_1486_; lean_object* v_levelAssignDepth_1487_; lean_object* v_lmvarCounter_1488_; lean_object* v_mvarCounter_1489_; lean_object* v_lDecls_1490_; lean_object* v_decls_1491_; lean_object* v_userNames_1492_; lean_object* v_lAssignment_1493_; lean_object* v_eAssignment_1494_; lean_object* v_dAssignment_1495_; lean_object* v_instanceTypedMVars_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1510_; 
v_depth_1486_ = lean_ctor_get(v_mctx_1478_, 0);
v_levelAssignDepth_1487_ = lean_ctor_get(v_mctx_1478_, 1);
v_lmvarCounter_1488_ = lean_ctor_get(v_mctx_1478_, 2);
v_mvarCounter_1489_ = lean_ctor_get(v_mctx_1478_, 3);
v_lDecls_1490_ = lean_ctor_get(v_mctx_1478_, 4);
v_decls_1491_ = lean_ctor_get(v_mctx_1478_, 5);
v_userNames_1492_ = lean_ctor_get(v_mctx_1478_, 6);
v_lAssignment_1493_ = lean_ctor_get(v_mctx_1478_, 7);
v_eAssignment_1494_ = lean_ctor_get(v_mctx_1478_, 8);
v_dAssignment_1495_ = lean_ctor_get(v_mctx_1478_, 9);
v_instanceTypedMVars_1496_ = lean_ctor_get(v_mctx_1478_, 10);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_mctx_1478_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1498_ = v_mctx_1478_;
v_isShared_1499_ = v_isSharedCheck_1510_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_instanceTypedMVars_1496_);
lean_inc(v_dAssignment_1495_);
lean_inc(v_eAssignment_1494_);
lean_inc(v_lAssignment_1493_);
lean_inc(v_userNames_1492_);
lean_inc(v_decls_1491_);
lean_inc(v_lDecls_1490_);
lean_inc(v_mvarCounter_1489_);
lean_inc(v_lmvarCounter_1488_);
lean_inc(v_levelAssignDepth_1487_);
lean_inc(v_depth_1486_);
lean_dec(v_mctx_1478_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1510_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1500_ = lean_box(0);
v___x_1501_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2___redArg(v_eAssignment_1494_, v_mvarId_1473_, v_val_1474_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 8, v___x_1501_);
v___x_1503_ = v___x_1498_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_depth_1486_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_levelAssignDepth_1487_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_lmvarCounter_1488_);
lean_ctor_set(v_reuseFailAlloc_1509_, 3, v_mvarCounter_1489_);
lean_ctor_set(v_reuseFailAlloc_1509_, 4, v_lDecls_1490_);
lean_ctor_set(v_reuseFailAlloc_1509_, 5, v_decls_1491_);
lean_ctor_set(v_reuseFailAlloc_1509_, 6, v_userNames_1492_);
lean_ctor_set(v_reuseFailAlloc_1509_, 7, v_lAssignment_1493_);
lean_ctor_set(v_reuseFailAlloc_1509_, 8, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1509_, 9, v_dAssignment_1495_);
lean_ctor_set(v_reuseFailAlloc_1509_, 10, v_instanceTypedMVars_1496_);
v___x_1503_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1505_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v___x_1503_);
v___x_1505_ = v___x_1484_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_cache_1479_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_zetaDeltaFVarIds_1480_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_postponed_1481_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v_diag_1482_);
v___x_1505_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = lean_st_ref_put(v___y_1475_, v___x_1505_);
v___x_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1500_);
return v___x_1507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg___boxed(lean_object* v_mvarId_1512_, lean_object* v_val_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_mvarId_1512_, v_val_1513_, v___y_1514_);
lean_dec(v___y_1514_);
return v_res_1516_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1520_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__2));
v___x_1521_ = lean_unsigned_to_nat(33u);
v___x_1522_ = lean_unsigned_to_nat(105u);
v___x_1523_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__1));
v___x_1524_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15));
v___x_1525_ = l_mkPanicMessageWithDecl(v___x_1524_, v___x_1523_, v___x_1522_, v___x_1521_, v___x_1520_);
return v___x_1525_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__4));
v___x_1528_ = l_Lean_stringToMessageData(v___x_1527_);
return v___x_1528_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__6));
v___x_1531_ = l_Lean_stringToMessageData(v___x_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0(lean_object* v___x_1532_, lean_object* v_snd_1533_, lean_object* v_hyp_1534_, lean_object* v___x_1535_, lean_object* v_args_1536_, lean_object* v_fst_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
if (lean_obj_tag(v___x_1532_) == 1)
{
lean_object* v_val_1547_; lean_object* v_focusHyp_1548_; lean_object* v_restHyps_1549_; lean_object* v_proof_1550_; lean_object* v___x_1551_; 
v_val_1547_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_val_1547_);
lean_dec_ref_known(v___x_1532_, 1);
v_focusHyp_1548_ = lean_ctor_get(v_val_1547_, 0);
lean_inc_ref_n(v_focusHyp_1548_, 2);
v_restHyps_1549_ = lean_ctor_get(v_val_1547_, 1);
lean_inc_ref(v_restHyps_1549_);
v_proof_1550_ = lean_ctor_get(v_val_1547_, 2);
lean_inc_ref(v_proof_1550_);
lean_dec(v_val_1547_);
v___x_1551_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_1548_);
if (lean_obj_tag(v___x_1551_) == 1)
{
lean_object* v_val_1552_; lean_object* v_u_1553_; lean_object* v_00_u03c3s_1554_; lean_object* v_hyps_1555_; lean_object* v_target_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1614_; 
v_val_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_val_1552_);
lean_dec_ref_known(v___x_1551_, 1);
v_u_1553_ = lean_ctor_get(v_snd_1533_, 0);
v_00_u03c3s_1554_ = lean_ctor_get(v_snd_1533_, 1);
v_hyps_1555_ = lean_ctor_get(v_snd_1533_, 2);
v_target_1556_ = lean_ctor_get(v_snd_1533_, 3);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_snd_1533_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1558_ = v_snd_1533_;
v_isShared_1559_ = v_isSharedCheck_1614_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_target_1556_);
lean_inc(v_hyps_1555_);
lean_inc(v_00_u03c3s_1554_);
lean_inc(v_u_1553_);
lean_dec(v_snd_1533_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1614_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
uint8_t v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = 0;
lean_inc_ref(v_00_u03c3s_1554_);
v___x_1561_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_hyp_1534_, v_00_u03c3s_1554_, v_val_1552_, v___x_1560_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; size_t v_sz_1573_; size_t v___x_1574_; lean_object* v___x_1575_; 
lean_dec_ref_known(v___x_1561_, 1);
v___x_1562_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_1563_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1564_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_1565_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1566_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__0));
v___x_1567_ = l_Lean_Name_mkStr6(v___x_1562_, v___x_1563_, v___x_1564_, v___x_1535_, v___x_1565_, v___x_1566_);
v___x_1568_ = lean_box(0);
lean_inc_n(v_u_1553_, 2);
v___x_1569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1569_, 0, v_u_1553_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
lean_inc_ref(v___x_1569_);
v___x_1570_ = l_Lean_mkConst(v___x_1567_, v___x_1569_);
lean_inc_ref_n(v_target_1556_, 2);
lean_inc_ref(v_focusHyp_1548_);
lean_inc_ref_n(v_restHyps_1549_, 2);
lean_inc_ref_n(v_00_u03c3s_1554_, 2);
v___x_1571_ = lean_alloc_closure((void*)(l_Lean_mkApp7), 8, 7);
lean_closure_set(v___x_1571_, 0, v___x_1570_);
lean_closure_set(v___x_1571_, 1, v_00_u03c3s_1554_);
lean_closure_set(v___x_1571_, 2, v_hyps_1555_);
lean_closure_set(v___x_1571_, 3, v_restHyps_1549_);
lean_closure_set(v___x_1571_, 4, v_focusHyp_1548_);
lean_closure_set(v___x_1571_, 5, v_target_1556_);
lean_closure_set(v___x_1571_, 6, v_proof_1550_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v_focusHyp_1548_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v_sz_1573_ = lean_array_size(v_args_1536_);
v___x_1574_ = ((size_t)0ULL);
v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1(v___x_1569_, v_u_1553_, v_00_u03c3s_1554_, v_restHyps_1549_, v_target_1556_, v_args_1536_, v_sz_1573_, v___x_1574_, v___x_1572_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v_fst_1577_; lean_object* v_snd_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1605_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1575_, 1);
v_fst_1577_ = lean_ctor_get(v_a_1576_, 0);
v_snd_1578_ = lean_ctor_get(v_a_1576_, 1);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_a_1576_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1580_ = v_a_1576_;
v_isShared_1581_ = v_isSharedCheck_1605_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_snd_1578_);
lean_inc(v_fst_1577_);
lean_dec(v_a_1576_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1605_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v___x_1584_; 
lean_inc_ref(v_00_u03c3s_1554_);
lean_inc(v_u_1553_);
v___x_1582_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1553_, v_00_u03c3s_1554_, v_restHyps_1549_, v_fst_1577_);
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 2, v___x_1582_);
v___x_1584_ = v___x_1558_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_u_1553_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_00_u03c3s_1554_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1604_, 3, v_target_1556_);
v___x_1584_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1585_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1584_);
v___x_1586_ = lean_box(0);
v___x_1587_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1585_, v___x_1586_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc_n(v_a_1588_, 2);
lean_dec_ref_known(v___x_1587_, 1);
v___x_1589_ = lean_apply_1(v_snd_1578_, v_a_1588_);
v___x_1590_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_fst_1537_, v___x_1589_, v___y_1543_);
lean_dec_ref(v___x_1590_);
v___x_1591_ = l_Lean_Expr_mvarId_x21(v_a_1588_);
lean_dec(v_a_1588_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set_tag(v___x_1580_, 1);
lean_ctor_set(v___x_1580_, 1, v___x_1568_);
lean_ctor_set(v___x_1580_, 0, v___x_1591_);
v___x_1593_ = v___x_1580_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v___x_1568_);
v___x_1593_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1593_, v___y_1539_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
return v___x_1594_;
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_del_object(v___x_1580_);
lean_dec(v_snd_1578_);
lean_dec(v_fst_1537_);
v_a_1596_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1587_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1587_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_del_object(v___x_1558_);
lean_dec_ref(v_target_1556_);
lean_dec_ref(v_00_u03c3s_1554_);
lean_dec(v_u_1553_);
lean_dec_ref(v_restHyps_1549_);
lean_dec(v_fst_1537_);
v_a_1606_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1575_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1575_);
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
else
{
lean_del_object(v___x_1558_);
lean_dec_ref(v_target_1556_);
lean_dec_ref(v_hyps_1555_);
lean_dec_ref(v_00_u03c3s_1554_);
lean_dec(v_u_1553_);
lean_dec_ref(v_proof_1550_);
lean_dec_ref(v_restHyps_1549_);
lean_dec_ref(v_focusHyp_1548_);
lean_dec(v_fst_1537_);
lean_dec_ref(v___x_1535_);
return v___x_1561_;
}
}
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_dec(v___x_1551_);
lean_dec_ref(v_proof_1550_);
lean_dec_ref(v_restHyps_1549_);
lean_dec_ref(v_focusHyp_1548_);
lean_dec(v_fst_1537_);
lean_dec_ref(v___x_1535_);
lean_dec(v_hyp_1534_);
lean_dec_ref(v_snd_1533_);
v___x_1615_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3);
v___x_1616_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(v___x_1615_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
return v___x_1616_;
}
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec(v_fst_1537_);
lean_dec_ref(v___x_1535_);
lean_dec_ref(v_snd_1533_);
lean_dec(v___x_1532_);
v___x_1617_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5);
v___x_1618_ = l_Lean_MessageData_ofSyntax(v_hyp_1534_);
v___x_1619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1617_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7);
v___x_1621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_1621_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
return v___x_1622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___boxed(lean_object* v___x_1623_, lean_object* v_snd_1624_, lean_object* v_hyp_1625_, lean_object* v___x_1626_, lean_object* v_args_1627_, lean_object* v_fst_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0(v___x_1623_, v_snd_1624_, v_hyp_1625_, v___x_1626_, v_args_1627_, v_fst_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec_ref(v_args_1627_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize(lean_object* v_x_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; 
v___x_1656_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1657_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2));
lean_inc(v_x_1646_);
v___x_1658_ = l_Lean_Syntax_isOfKind(v_x_1646_, v___x_1657_);
if (v___x_1658_ == 0)
{
lean_object* v___x_1659_; 
lean_dec(v_x_1646_);
v___x_1659_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_1659_;
}
else
{
lean_object* v___x_1660_; lean_object* v_hyp_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v_args_1664_; lean_object* v___x_1665_; 
v___x_1660_ = lean_unsigned_to_nat(1u);
v_hyp_1661_ = l_Lean_Syntax_getArg(v_x_1646_, v___x_1660_);
v___x_1662_ = lean_unsigned_to_nat(2u);
v___x_1663_ = l_Lean_Syntax_getArg(v_x_1646_, v___x_1662_);
lean_dec(v_x_1646_);
v_args_1664_ = l_Lean_Syntax_getArgs(v___x_1663_);
lean_dec(v___x_1663_);
v___x_1665_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1648_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v_fst_1667_; lean_object* v_snd_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___y_1671_; lean_object* v___x_1672_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v___x_1665_, 1);
v_fst_1667_ = lean_ctor_get(v_a_1666_, 0);
lean_inc_n(v_fst_1667_, 2);
v_snd_1668_ = lean_ctor_get(v_a_1666_, 1);
lean_inc_n(v_snd_1668_, 2);
lean_dec(v_a_1666_);
v___x_1669_ = l_Lean_TSyntax_getId(v_hyp_1661_);
v___x_1670_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_snd_1668_, v___x_1669_);
lean_dec(v___x_1669_);
v___y_1671_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___boxed), 15, 6);
lean_closure_set(v___y_1671_, 0, v___x_1670_);
lean_closure_set(v___y_1671_, 1, v_snd_1668_);
lean_closure_set(v___y_1671_, 2, v_hyp_1661_);
lean_closure_set(v___y_1671_, 3, v___x_1656_);
lean_closure_set(v___y_1671_, 4, v_args_1664_);
lean_closure_set(v___y_1671_, 5, v_fst_1667_);
v___x_1672_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_fst_1667_, v___y_1671_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
return v___x_1672_;
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec_ref(v_args_1664_);
lean_dec(v_hyp_1661_);
v_a_1673_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1665_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1665_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___boxed(lean_object* v_x_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize(v_x_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2(lean_object* v_mvarId_1692_, lean_object* v_val_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_mvarId_1692_, v_val_1693_, v___y_1699_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___boxed(lean_object* v_mvarId_1704_, lean_object* v_val_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2(v_mvarId_1704_, v_val_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2(lean_object* v_00_u03b2_1716_, lean_object* v_x_1717_, lean_object* v_x_1718_, lean_object* v_x_1719_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2___redArg(v_x_1717_, v_x_1718_, v_x_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_1721_, lean_object* v_x_1722_, size_t v_x_1723_, size_t v_x_1724_, lean_object* v_x_1725_, lean_object* v_x_1726_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_x_1722_, v_x_1723_, v_x_1724_, v_x_1725_, v_x_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1728_, lean_object* v_x_1729_, lean_object* v_x_1730_, lean_object* v_x_1731_, lean_object* v_x_1732_, lean_object* v_x_1733_){
_start:
{
size_t v_x_7926__boxed_1734_; size_t v_x_7927__boxed_1735_; lean_object* v_res_1736_; 
v_x_7926__boxed_1734_ = lean_unbox_usize(v_x_1730_);
lean_dec(v_x_1730_);
v_x_7927__boxed_1735_ = lean_unbox_usize(v_x_1731_);
lean_dec(v_x_1731_);
v_res_1736_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5(v_00_u03b2_1728_, v_x_1729_, v_x_7926__boxed_1734_, v_x_7927__boxed_1735_, v_x_1732_, v_x_1733_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_1737_, lean_object* v_n_1738_, lean_object* v_k_1739_, lean_object* v_v_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6___redArg(v_n_1738_, v_k_1739_, v_v_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7(lean_object* v_00_u03b2_1742_, size_t v_depth_1743_, lean_object* v_keys_1744_, lean_object* v_vals_1745_, lean_object* v_heq_1746_, lean_object* v_i_1747_, lean_object* v_entries_1748_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(v_depth_1743_, v_keys_1744_, v_vals_1745_, v_i_1747_, v_entries_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b2_1750_, lean_object* v_depth_1751_, lean_object* v_keys_1752_, lean_object* v_vals_1753_, lean_object* v_heq_1754_, lean_object* v_i_1755_, lean_object* v_entries_1756_){
_start:
{
size_t v_depth_boxed_1757_; lean_object* v_res_1758_; 
v_depth_boxed_1757_ = lean_unbox_usize(v_depth_1751_);
lean_dec(v_depth_1751_);
v_res_1758_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7(v_00_u03b2_1750_, v_depth_boxed_1757_, v_keys_1752_, v_vals_1753_, v_heq_1754_, v_i_1755_, v_entries_1756_);
lean_dec_ref(v_vals_1753_);
lean_dec_ref(v_keys_1752_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_1759_, lean_object* v_x_1760_, lean_object* v_x_1761_, lean_object* v_x_1762_, lean_object* v_x_1763_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7___redArg(v_x_1760_, v_x_1761_, v_x_1762_, v_x_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1(){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1774_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1775_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2));
v___x_1776_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1));
v___x_1777_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___boxed), 10, 0);
v___x_1778_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1774_, v___x_1775_, v___x_1776_, v___x_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___boxed(lean_object* v_a_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1();
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(lean_object* v___y_1781_){
_start:
{
lean_object* v___x_1783_; lean_object* v_ngen_1784_; lean_object* v_namePrefix_1785_; lean_object* v_idx_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1816_; 
v___x_1783_ = lean_st_ref_get(v___y_1781_);
v_ngen_1784_ = lean_ctor_get(v___x_1783_, 2);
lean_inc_ref(v_ngen_1784_);
lean_dec(v___x_1783_);
v_namePrefix_1785_ = lean_ctor_get(v_ngen_1784_, 0);
v_idx_1786_ = lean_ctor_get(v_ngen_1784_, 1);
v_isSharedCheck_1816_ = !lean_is_exclusive(v_ngen_1784_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1788_ = v_ngen_1784_;
v_isShared_1789_ = v_isSharedCheck_1816_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_idx_1786_);
lean_inc(v_namePrefix_1785_);
lean_dec(v_ngen_1784_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1816_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v_r_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1794_; 
lean_inc(v_idx_1786_);
lean_inc(v_namePrefix_1785_);
v_r_1790_ = l_Lean_Name_num___override(v_namePrefix_1785_, v_idx_1786_);
v___x_1791_ = lean_unsigned_to_nat(1u);
v___x_1792_ = lean_nat_add(v_idx_1786_, v___x_1791_);
lean_dec(v_idx_1786_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 1, v___x_1792_);
v___x_1794_ = v___x_1788_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_namePrefix_1785_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1795_; lean_object* v_env_1796_; lean_object* v_nextMacroScope_1797_; lean_object* v_auxDeclNGen_1798_; lean_object* v_traceState_1799_; lean_object* v_cache_1800_; lean_object* v_recordedDeps_1801_; lean_object* v_messages_1802_; lean_object* v_infoState_1803_; lean_object* v_snapshotTasks_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1813_; 
v___x_1795_ = lean_st_ref_take(v___y_1781_);
v_env_1796_ = lean_ctor_get(v___x_1795_, 0);
v_nextMacroScope_1797_ = lean_ctor_get(v___x_1795_, 1);
v_auxDeclNGen_1798_ = lean_ctor_get(v___x_1795_, 3);
v_traceState_1799_ = lean_ctor_get(v___x_1795_, 4);
v_cache_1800_ = lean_ctor_get(v___x_1795_, 5);
v_recordedDeps_1801_ = lean_ctor_get(v___x_1795_, 6);
v_messages_1802_ = lean_ctor_get(v___x_1795_, 7);
v_infoState_1803_ = lean_ctor_get(v___x_1795_, 8);
v_snapshotTasks_1804_ = lean_ctor_get(v___x_1795_, 9);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1813_ == 0)
{
lean_object* v_unused_1814_; 
v_unused_1814_ = lean_ctor_get(v___x_1795_, 2);
lean_dec(v_unused_1814_);
v___x_1806_ = v___x_1795_;
v_isShared_1807_ = v_isSharedCheck_1813_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_snapshotTasks_1804_);
lean_inc(v_infoState_1803_);
lean_inc(v_messages_1802_);
lean_inc(v_recordedDeps_1801_);
lean_inc(v_cache_1800_);
lean_inc(v_traceState_1799_);
lean_inc(v_auxDeclNGen_1798_);
lean_inc(v_nextMacroScope_1797_);
lean_inc(v_env_1796_);
lean_dec(v___x_1795_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1813_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 2, v___x_1794_);
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_env_1796_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v_nextMacroScope_1797_);
lean_ctor_set(v_reuseFailAlloc_1812_, 2, v___x_1794_);
lean_ctor_set(v_reuseFailAlloc_1812_, 3, v_auxDeclNGen_1798_);
lean_ctor_set(v_reuseFailAlloc_1812_, 4, v_traceState_1799_);
lean_ctor_set(v_reuseFailAlloc_1812_, 5, v_cache_1800_);
lean_ctor_set(v_reuseFailAlloc_1812_, 6, v_recordedDeps_1801_);
lean_ctor_set(v_reuseFailAlloc_1812_, 7, v_messages_1802_);
lean_ctor_set(v_reuseFailAlloc_1812_, 8, v_infoState_1803_);
lean_ctor_set(v_reuseFailAlloc_1812_, 9, v_snapshotTasks_1804_);
v___x_1809_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = lean_st_ref_put(v___y_1781_, v___x_1809_);
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v_r_1790_);
return v___x_1811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg___boxed(lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(v___y_1817_);
lean_dec(v___y_1817_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0(lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(v___y_1827_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___boxed(lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0(v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(lean_object* v_e_1840_, lean_object* v___y_1841_){
_start:
{
uint8_t v___x_1843_; 
v___x_1843_ = l_Lean_Expr_hasMVar(v_e_1840_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; 
v___x_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1844_, 0, v_e_1840_);
return v___x_1844_;
}
else
{
lean_object* v___x_1845_; lean_object* v_mctx_1846_; lean_object* v___x_1847_; lean_object* v_fst_1848_; lean_object* v_snd_1849_; lean_object* v___x_1850_; lean_object* v_cache_1851_; lean_object* v_zetaDeltaFVarIds_1852_; lean_object* v_postponed_1853_; lean_object* v_diag_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1863_; 
v___x_1845_ = lean_st_ref_get(v___y_1841_);
v_mctx_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc_ref(v_mctx_1846_);
lean_dec(v___x_1845_);
v___x_1847_ = l_Lean_instantiateMVarsCore(v_mctx_1846_, v_e_1840_);
v_fst_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_fst_1848_);
v_snd_1849_ = lean_ctor_get(v___x_1847_, 1);
lean_inc(v_snd_1849_);
lean_dec_ref(v___x_1847_);
v___x_1850_ = lean_st_ref_take(v___y_1841_);
v_cache_1851_ = lean_ctor_get(v___x_1850_, 1);
v_zetaDeltaFVarIds_1852_ = lean_ctor_get(v___x_1850_, 2);
v_postponed_1853_ = lean_ctor_get(v___x_1850_, 3);
v_diag_1854_ = lean_ctor_get(v___x_1850_, 4);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1863_ == 0)
{
lean_object* v_unused_1864_; 
v_unused_1864_ = lean_ctor_get(v___x_1850_, 0);
lean_dec(v_unused_1864_);
v___x_1856_ = v___x_1850_;
v_isShared_1857_ = v_isSharedCheck_1863_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_diag_1854_);
lean_inc(v_postponed_1853_);
lean_inc(v_zetaDeltaFVarIds_1852_);
lean_inc(v_cache_1851_);
lean_dec(v___x_1850_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1863_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v_snd_1849_);
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_snd_1849_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_cache_1851_);
lean_ctor_set(v_reuseFailAlloc_1862_, 2, v_zetaDeltaFVarIds_1852_);
lean_ctor_set(v_reuseFailAlloc_1862_, 3, v_postponed_1853_);
lean_ctor_set(v_reuseFailAlloc_1862_, 4, v_diag_1854_);
v___x_1859_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_st_ref_put(v___y_1841_, v___x_1859_);
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v_fst_1848_);
return v___x_1861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg___boxed(lean_object* v_e_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(v_e_1865_, v___y_1866_);
lean_dec(v___y_1866_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1(lean_object* v_e_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(v_e_1869_, v___y_1875_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___boxed(lean_object* v_e_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1(v_e_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2(lean_object* v___x_1891_, lean_object* v___x_1892_, lean_object* v___x_1893_, lean_object* v___x_1894_, lean_object* v___x_1895_, lean_object* v_as_1896_, size_t v_sz_1897_, size_t v_i_1898_, lean_object* v_b_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_a_1910_; uint8_t v___x_1914_; 
v___x_1914_ = lean_usize_dec_lt(v_i_1898_, v_sz_1897_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; 
lean_dec_ref(v___x_1895_);
lean_dec_ref(v___x_1894_);
lean_dec_ref(v___x_1893_);
lean_dec(v___x_1892_);
lean_dec(v___x_1891_);
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v_b_1899_);
return v___x_1915_;
}
else
{
lean_object* v_fst_1916_; lean_object* v_snd_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1971_; 
v_fst_1916_ = lean_ctor_get(v_b_1899_, 0);
v_snd_1917_ = lean_ctor_get(v_b_1899_, 1);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_b_1899_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1919_ = v_b_1899_;
v_isShared_1920_ = v_isSharedCheck_1971_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_snd_1917_);
lean_inc(v_fst_1916_);
lean_dec(v_b_1899_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1971_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v_a_1924_; lean_object* v___y_1926_; lean_object* v___x_1966_; 
v___x_1921_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_1922_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1923_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v_a_1924_ = lean_array_uget_borrowed(v_as_1896_, v_i_1898_);
lean_inc(v_a_1924_);
lean_inc(v_fst_1916_);
lean_inc_ref(v___x_1894_);
v___x_1966_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(v___x_1894_, v_fst_1916_, v_a_1924_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
if (lean_obj_tag(v_a_1967_) == 0)
{
lean_object* v___x_1968_; 
lean_dec_ref_known(v___x_1966_, 1);
lean_inc(v_a_1924_);
lean_inc(v_fst_1916_);
lean_inc_ref(v___x_1894_);
v___x_1968_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(v___x_1894_, v_fst_1916_, v_a_1924_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
if (lean_obj_tag(v_a_1969_) == 0)
{
lean_object* v___x_1970_; 
lean_dec_ref_known(v___x_1968_, 1);
lean_inc(v_a_1924_);
lean_inc(v_fst_1916_);
lean_inc_ref(v___x_1894_);
v___x_1970_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(v___x_1894_, v_fst_1916_, v_a_1924_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
v___y_1926_ = v___x_1970_;
goto v___jp_1925_;
}
else
{
lean_dec_ref_known(v_a_1969_, 1);
v___y_1926_ = v___x_1968_;
goto v___jp_1925_;
}
}
else
{
v___y_1926_ = v___x_1968_;
goto v___jp_1925_;
}
}
else
{
lean_dec_ref_known(v_a_1967_, 1);
v___y_1926_ = v___x_1966_;
goto v___jp_1925_;
}
}
else
{
v___y_1926_ = v___x_1966_;
goto v___jp_1925_;
}
v___jp_1925_:
{
if (lean_obj_tag(v___y_1926_) == 0)
{
lean_object* v_a_1927_; 
v_a_1927_ = lean_ctor_get(v___y_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v___y_1926_, 1);
if (lean_obj_tag(v_a_1927_) == 0)
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1928_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1);
lean_inc(v_fst_1916_);
v___x_1929_ = l_Lean_MessageData_ofExpr(v_fst_1916_);
v___x_1930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1928_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_1932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
lean_inc(v_a_1924_);
v___x_1933_ = l_Lean_MessageData_ofSyntax(v_a_1924_);
v___x_1934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_1934_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v___x_1937_; 
lean_dec_ref_known(v___x_1935_, 1);
if (v_isShared_1920_ == 0)
{
v___x_1937_ = v___x_1919_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_fst_1916_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_snd_1917_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
v_a_1910_ = v___x_1937_;
goto v___jp_1909_;
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_del_object(v___x_1919_);
lean_dec(v_snd_1917_);
lean_dec(v_fst_1916_);
lean_dec_ref(v___x_1895_);
lean_dec_ref(v___x_1894_);
lean_dec_ref(v___x_1893_);
lean_dec(v___x_1892_);
lean_dec(v___x_1891_);
v_a_1939_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1935_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1935_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
else
{
lean_object* v_val_1947_; lean_object* v_fst_1948_; lean_object* v_snd_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1957_; 
lean_del_object(v___x_1919_);
v_val_1947_ = lean_ctor_get(v_a_1927_, 0);
lean_inc(v_val_1947_);
lean_dec_ref_known(v_a_1927_, 1);
v_fst_1948_ = lean_ctor_get(v_val_1947_, 0);
v_snd_1949_ = lean_ctor_get(v_val_1947_, 1);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_val_1947_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1951_ = v_val_1947_;
v_isShared_1952_ = v_isSharedCheck_1957_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_snd_1949_);
lean_inc(v_fst_1948_);
lean_dec(v_val_1947_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1957_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___f_1953_; lean_object* v___x_1955_; 
lean_inc_ref(v___x_1895_);
lean_inc(v_fst_1948_);
lean_inc_ref(v___x_1894_);
lean_inc_ref(v___x_1893_);
lean_inc(v___x_1892_);
lean_inc(v___x_1891_);
v___f_1953_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0), 13, 12);
lean_closure_set(v___f_1953_, 0, v___x_1921_);
lean_closure_set(v___f_1953_, 1, v___x_1922_);
lean_closure_set(v___f_1953_, 2, v___x_1923_);
lean_closure_set(v___f_1953_, 3, v___x_1891_);
lean_closure_set(v___f_1953_, 4, v___x_1892_);
lean_closure_set(v___f_1953_, 5, v___x_1893_);
lean_closure_set(v___f_1953_, 6, v___x_1894_);
lean_closure_set(v___f_1953_, 7, v_fst_1916_);
lean_closure_set(v___f_1953_, 8, v_fst_1948_);
lean_closure_set(v___f_1953_, 9, v___x_1895_);
lean_closure_set(v___f_1953_, 10, v_snd_1949_);
lean_closure_set(v___f_1953_, 11, v_snd_1917_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 1, v___f_1953_);
v___x_1955_ = v___x_1951_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_fst_1948_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v___f_1953_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
v_a_1910_ = v___x_1955_;
goto v___jp_1909_;
}
}
}
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_del_object(v___x_1919_);
lean_dec(v_snd_1917_);
lean_dec(v_fst_1916_);
lean_dec_ref(v___x_1895_);
lean_dec_ref(v___x_1894_);
lean_dec_ref(v___x_1893_);
lean_dec(v___x_1892_);
lean_dec(v___x_1891_);
v_a_1958_ = lean_ctor_get(v___y_1926_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___y_1926_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___y_1926_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___y_1926_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
}
v___jp_1909_:
{
size_t v___x_1911_; size_t v___x_1912_; 
v___x_1911_ = ((size_t)1ULL);
v___x_1912_ = lean_usize_add(v_i_1898_, v___x_1911_);
v_i_1898_ = v___x_1912_;
v_b_1899_ = v_a_1910_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2___boxed(lean_object** _args){
lean_object* v___x_1972_ = _args[0];
lean_object* v___x_1973_ = _args[1];
lean_object* v___x_1974_ = _args[2];
lean_object* v___x_1975_ = _args[3];
lean_object* v___x_1976_ = _args[4];
lean_object* v_as_1977_ = _args[5];
lean_object* v_sz_1978_ = _args[6];
lean_object* v_i_1979_ = _args[7];
lean_object* v_b_1980_ = _args[8];
lean_object* v___y_1981_ = _args[9];
lean_object* v___y_1982_ = _args[10];
lean_object* v___y_1983_ = _args[11];
lean_object* v___y_1984_ = _args[12];
lean_object* v___y_1985_ = _args[13];
lean_object* v___y_1986_ = _args[14];
lean_object* v___y_1987_ = _args[15];
lean_object* v___y_1988_ = _args[16];
lean_object* v___y_1989_ = _args[17];
_start:
{
size_t v_sz_boxed_1990_; size_t v_i_boxed_1991_; lean_object* v_res_1992_; 
v_sz_boxed_1990_ = lean_unbox_usize(v_sz_1978_);
lean_dec(v_sz_1978_);
v_i_boxed_1991_ = lean_unbox_usize(v_i_1979_);
lean_dec(v_i_1979_);
v_res_1992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2(v___x_1972_, v___x_1973_, v___x_1974_, v___x_1975_, v___x_1976_, v_as_1977_, v_sz_boxed_1990_, v_i_boxed_1991_, v_b_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec_ref(v_as_1977_);
return v_res_1992_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2000_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__3));
v___x_2001_ = lean_unsigned_to_nat(33u);
v___x_2002_ = lean_unsigned_to_nat(175u);
v___x_2003_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__2));
v___x_2004_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15));
v___x_2005_ = l_mkPanicMessageWithDecl(v___x_2004_, v___x_2003_, v___x_2002_, v___x_2001_, v___x_2000_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0(lean_object* v___x_2006_, lean_object* v___x_2007_, uint8_t v___x_2008_, lean_object* v_u_2009_, lean_object* v_00_u03c3s_2010_, lean_object* v___x_2011_, lean_object* v_hyp_2012_, lean_object* v_hyps_2013_, lean_object* v_target_2014_, lean_object* v_args_2015_, lean_object* v_fst_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l_Lean_Elab_Tactic_elabTerm(v___x_2006_, v___x_2007_, v___x_2008_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2028_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc_n(v_a_2027_, 2);
lean_dec_ref_known(v___x_2026_, 1);
lean_inc(v___y_2024_);
lean_inc_ref(v___y_2023_);
lean_inc(v___y_2022_);
lean_inc_ref(v___y_2021_);
v___x_2028_ = lean_infer_type(v_a_2027_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_a_2029_);
lean_dec_ref_known(v___x_2028_, 1);
v___x_2030_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_2031_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_2032_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_2033_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0));
v___x_2034_ = lean_box(0);
lean_inc(v_u_2009_);
v___x_2035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2035_, 0, v_u_2009_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
lean_inc_ref(v___x_2035_);
v___x_2036_ = l_Lean_mkConst(v___x_2033_, v___x_2035_);
lean_inc_ref(v_00_u03c3s_2010_);
v___x_2037_ = l_Lean_Expr_app___override(v___x_2036_, v_00_u03c3s_2010_);
v___x_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
v___x_2039_ = 0;
v___x_2040_ = lean_box(0);
v___x_2041_ = l_Lean_Meta_mkFreshExprMVar(v___x_2038_, v___x_2039_, v___x_2040_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc_n(v_a_2042_, 2);
lean_dec_ref_known(v___x_2041_, 1);
v___x_2043_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__5));
lean_inc_ref(v___x_2011_);
v___x_2044_ = l_Lean_Name_mkStr5(v___x_2030_, v___x_2031_, v___x_2032_, v___x_2011_, v___x_2043_);
lean_inc_ref(v___x_2035_);
v___x_2045_ = l_Lean_mkConst(v___x_2044_, v___x_2035_);
lean_inc_ref(v_00_u03c3s_2010_);
lean_inc(v_a_2029_);
v___x_2046_ = l_Lean_mkApp3(v___x_2045_, v_a_2029_, v_00_u03c3s_2010_, v_a_2042_);
v___x_2047_ = lean_box(0);
v___x_2048_ = l_Lean_Meta_synthInstance(v___x_2046_, v___x_2047_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2050_; lean_object* v_a_2051_; lean_object* v___x_2052_; lean_object* v_a_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; size_t v_sz_2063_; size_t v___x_2064_; lean_object* v___x_2065_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2049_);
lean_dec_ref_known(v___x_2048_, 1);
v___x_2050_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(v___y_2024_);
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref(v___x_2050_);
v___x_2052_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(v_a_2042_, v___y_2022_);
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref(v___x_2052_);
v___x_2054_ = l_Lean_TSyntax_getId(v_hyp_2012_);
v___x_2055_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
lean_ctor_set(v___x_2055_, 1, v_a_2051_);
lean_ctor_set(v___x_2055_, 2, v_a_2053_);
v___x_2056_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_2055_);
v___x_2057_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_2058_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__1));
v___x_2059_ = l_Lean_Name_mkStr6(v___x_2030_, v___x_2031_, v___x_2032_, v___x_2011_, v___x_2057_, v___x_2058_);
lean_inc_ref(v___x_2035_);
v___x_2060_ = l_Lean_mkConst(v___x_2059_, v___x_2035_);
lean_inc_ref_n(v_target_2014_, 2);
lean_inc_ref_n(v_hyps_2013_, 2);
lean_inc_ref(v___x_2056_);
lean_inc_ref_n(v_00_u03c3s_2010_, 2);
v___x_2061_ = lean_alloc_closure((void*)(l_Lean_mkApp8), 9, 8);
lean_closure_set(v___x_2061_, 0, v___x_2060_);
lean_closure_set(v___x_2061_, 1, v_00_u03c3s_2010_);
lean_closure_set(v___x_2061_, 2, v_a_2029_);
lean_closure_set(v___x_2061_, 3, v___x_2056_);
lean_closure_set(v___x_2061_, 4, v_hyps_2013_);
lean_closure_set(v___x_2061_, 5, v_target_2014_);
lean_closure_set(v___x_2061_, 6, v_a_2049_);
lean_closure_set(v___x_2061_, 7, v_a_2027_);
v___x_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2056_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
v_sz_2063_ = lean_array_size(v_args_2015_);
v___x_2064_ = ((size_t)0ULL);
lean_inc(v_u_2009_);
v___x_2065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2(v___x_2035_, v_u_2009_, v_00_u03c3s_2010_, v_hyps_2013_, v_target_2014_, v_args_2015_, v_sz_2063_, v___x_2064_, v___x_2062_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v_fst_2067_; lean_object* v_snd_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2097_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref_known(v___x_2065_, 1);
v_fst_2067_ = lean_ctor_get(v_a_2066_, 0);
v_snd_2068_ = lean_ctor_get(v_a_2066_, 1);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_a_2066_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2070_ = v_a_2066_;
v_isShared_2071_ = v_isSharedCheck_2097_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_snd_2068_);
lean_inc(v_fst_2067_);
lean_dec(v_a_2066_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2097_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; 
lean_inc(v_fst_2067_);
v___x_2072_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_fst_2067_);
if (lean_obj_tag(v___x_2072_) == 1)
{
lean_object* v_val_2073_; lean_object* v___x_2074_; 
v_val_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_val_2073_);
lean_dec_ref_known(v___x_2072_, 1);
lean_inc_ref(v_00_u03c3s_2010_);
v___x_2074_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_hyp_2012_, v_00_u03c3s_2010_, v_val_2073_, v___x_2008_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_dec_ref_known(v___x_2074_, 1);
lean_inc_ref(v_00_u03c3s_2010_);
lean_inc(v_u_2009_);
v___x_2075_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_2009_, v_00_u03c3s_2010_, v_hyps_2013_, v_fst_2067_);
v___x_2076_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2076_, 0, v_u_2009_);
lean_ctor_set(v___x_2076_, 1, v_00_u03c3s_2010_);
lean_ctor_set(v___x_2076_, 2, v___x_2075_);
lean_ctor_set(v___x_2076_, 3, v_target_2014_);
v___x_2077_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_2076_);
v___x_2078_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2077_, v___x_2040_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2084_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc_n(v_a_2079_, 2);
lean_dec_ref_known(v___x_2078_, 1);
v___x_2080_ = lean_apply_1(v_snd_2068_, v_a_2079_);
v___x_2081_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_fst_2016_, v___x_2080_, v___y_2022_);
lean_dec_ref(v___x_2081_);
v___x_2082_ = l_Lean_Expr_mvarId_x21(v_a_2079_);
lean_dec(v_a_2079_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set_tag(v___x_2070_, 1);
lean_ctor_set(v___x_2070_, 1, v___x_2034_);
lean_ctor_set(v___x_2070_, 0, v___x_2082_);
v___x_2084_ = v___x_2070_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v___x_2034_);
v___x_2084_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2084_, v___y_2018_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
return v___x_2085_;
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_del_object(v___x_2070_);
lean_dec(v_snd_2068_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v_fst_2016_);
v_a_2087_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2078_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2078_);
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
else
{
lean_del_object(v___x_2070_);
lean_dec(v_snd_2068_);
lean_dec(v_fst_2067_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v_fst_2016_);
lean_dec_ref(v_target_2014_);
lean_dec_ref(v_hyps_2013_);
lean_dec_ref(v_00_u03c3s_2010_);
lean_dec(v_u_2009_);
return v___x_2074_;
}
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
lean_dec(v___x_2072_);
lean_del_object(v___x_2070_);
lean_dec(v_snd_2068_);
lean_dec(v_fst_2067_);
lean_dec(v_fst_2016_);
lean_dec_ref(v_target_2014_);
lean_dec_ref(v_hyps_2013_);
lean_dec(v_hyp_2012_);
lean_dec_ref(v_00_u03c3s_2010_);
lean_dec(v_u_2009_);
v___x_2095_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4, &l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4);
v___x_2096_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(v___x_2095_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
return v___x_2096_;
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v_fst_2016_);
lean_dec_ref(v_target_2014_);
lean_dec_ref(v_hyps_2013_);
lean_dec(v_hyp_2012_);
lean_dec_ref(v_00_u03c3s_2010_);
lean_dec(v_u_2009_);
v_a_2098_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2065_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2065_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec(v_a_2042_);
lean_dec_ref_known(v___x_2035_, 2);
lean_dec(v_a_2029_);
lean_dec(v_a_2027_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v_fst_2016_);
lean_dec_ref(v_target_2014_);
lean_dec_ref(v_hyps_2013_);
lean_dec(v_hyp_2012_);
lean_dec_ref(v___x_2011_);
lean_dec_ref(v_00_u03c3s_2010_);
lean_dec(v_u_2009_);
v_a_2106_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2048_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2048_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec_ref_known(v___x_2035_, 2);
lean_dec(v_a_2029_);
lean_dec(v_a_2027_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v_fst_2016_);
lean_dec_ref(v_target_2014_);
lean_dec_ref(v_hyps_2013_);
lean_dec(v_hyp_2012_);
lean_dec_ref(v___x_2011_);
lean_dec_ref(v_00_u03c3s_2010_);
lean_dec(v_u_2009_);
v_a_2114_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2041_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2041_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec(v_a_2027_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v_fst_2016_);
lean_dec_ref(v_target_2014_);
lean_dec_ref(v_hyps_2013_);
lean_dec(v_hyp_2012_);
lean_dec_ref(v___x_2011_);
lean_dec_ref(v_00_u03c3s_2010_);
lean_dec(v_u_2009_);
v_a_2122_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2028_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2028_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v_fst_2016_);
lean_dec_ref(v_target_2014_);
lean_dec_ref(v_hyps_2013_);
lean_dec(v_hyp_2012_);
lean_dec_ref(v___x_2011_);
lean_dec_ref(v_00_u03c3s_2010_);
lean_dec(v_u_2009_);
v_a_2130_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2026_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2026_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___boxed(lean_object** _args){
lean_object* v___x_2138_ = _args[0];
lean_object* v___x_2139_ = _args[1];
lean_object* v___x_2140_ = _args[2];
lean_object* v_u_2141_ = _args[3];
lean_object* v_00_u03c3s_2142_ = _args[4];
lean_object* v___x_2143_ = _args[5];
lean_object* v_hyp_2144_ = _args[6];
lean_object* v_hyps_2145_ = _args[7];
lean_object* v_target_2146_ = _args[8];
lean_object* v_args_2147_ = _args[9];
lean_object* v_fst_2148_ = _args[10];
lean_object* v___y_2149_ = _args[11];
lean_object* v___y_2150_ = _args[12];
lean_object* v___y_2151_ = _args[13];
lean_object* v___y_2152_ = _args[14];
lean_object* v___y_2153_ = _args[15];
lean_object* v___y_2154_ = _args[16];
lean_object* v___y_2155_ = _args[17];
lean_object* v___y_2156_ = _args[18];
lean_object* v___y_2157_ = _args[19];
_start:
{
uint8_t v___x_8366__boxed_2158_; lean_object* v_res_2159_; 
v___x_8366__boxed_2158_ = lean_unbox(v___x_2140_);
v_res_2159_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0(v___x_2138_, v___x_2139_, v___x_8366__boxed_2158_, v_u_2141_, v_00_u03c3s_2142_, v___x_2143_, v_hyp_2144_, v_hyps_2145_, v_target_2146_, v_args_2147_, v_fst_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec_ref(v_args_2147_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure(lean_object* v_x_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2183_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_2184_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1));
lean_inc(v_x_2173_);
v___x_2185_ = l_Lean_Syntax_isOfKind(v_x_2173_, v___x_2184_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; 
lean_dec(v_x_2173_);
v___x_2186_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_2186_;
}
else
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; 
v___x_2187_ = lean_unsigned_to_nat(1u);
v___x_2188_ = l_Lean_Syntax_getArg(v_x_2173_, v___x_2187_);
v___x_2189_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4));
lean_inc(v___x_2188_);
v___x_2190_ = l_Lean_Syntax_isOfKind(v___x_2188_, v___x_2189_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; 
lean_dec(v___x_2188_);
lean_dec(v_x_2173_);
v___x_2191_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_2191_;
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
v___x_2192_ = lean_unsigned_to_nat(0u);
v___x_2193_ = lean_unsigned_to_nat(2u);
v___x_2194_ = l_Lean_Syntax_getArg(v_x_2173_, v___x_2193_);
v___x_2195_ = l_Lean_Syntax_matchesNull(v___x_2194_, v___x_2192_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; 
lean_dec(v___x_2188_);
lean_dec(v_x_2173_);
v___x_2196_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_2196_;
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v_hyp_2200_; lean_object* v_args_2201_; lean_object* v___x_2202_; 
v___x_2197_ = l_Lean_Syntax_getArg(v___x_2188_, v___x_2192_);
v___x_2198_ = l_Lean_Syntax_getArg(v___x_2188_, v___x_2187_);
lean_dec(v___x_2188_);
v___x_2199_ = lean_unsigned_to_nat(4u);
v_hyp_2200_ = l_Lean_Syntax_getArg(v_x_2173_, v___x_2199_);
lean_dec(v_x_2173_);
v_args_2201_ = l_Lean_Syntax_getArgs(v___x_2198_);
lean_dec(v___x_2198_);
v___x_2202_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_2175_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v_snd_2204_; lean_object* v_fst_2205_; lean_object* v_u_2206_; lean_object* v_00_u03c3s_2207_; lean_object* v_hyps_2208_; lean_object* v_target_2209_; lean_object* v___x_2210_; uint8_t v___x_2211_; lean_object* v___x_2212_; lean_object* v___f_2213_; lean_object* v___x_2214_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2202_, 1);
v_snd_2204_ = lean_ctor_get(v_a_2203_, 1);
lean_inc(v_snd_2204_);
v_fst_2205_ = lean_ctor_get(v_a_2203_, 0);
lean_inc_n(v_fst_2205_, 2);
lean_dec(v_a_2203_);
v_u_2206_ = lean_ctor_get(v_snd_2204_, 0);
lean_inc(v_u_2206_);
v_00_u03c3s_2207_ = lean_ctor_get(v_snd_2204_, 1);
lean_inc_ref(v_00_u03c3s_2207_);
v_hyps_2208_ = lean_ctor_get(v_snd_2204_, 2);
lean_inc_ref(v_hyps_2208_);
v_target_2209_ = lean_ctor_get(v_snd_2204_, 3);
lean_inc_ref(v_target_2209_);
lean_dec(v_snd_2204_);
v___x_2210_ = lean_box(0);
v___x_2211_ = 0;
v___x_2212_ = lean_box(v___x_2211_);
v___f_2213_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___boxed), 20, 11);
lean_closure_set(v___f_2213_, 0, v___x_2197_);
lean_closure_set(v___f_2213_, 1, v___x_2210_);
lean_closure_set(v___f_2213_, 2, v___x_2212_);
lean_closure_set(v___f_2213_, 3, v_u_2206_);
lean_closure_set(v___f_2213_, 4, v_00_u03c3s_2207_);
lean_closure_set(v___f_2213_, 5, v___x_2183_);
lean_closure_set(v___f_2213_, 6, v_hyp_2200_);
lean_closure_set(v___f_2213_, 7, v_hyps_2208_);
lean_closure_set(v___f_2213_, 8, v_target_2209_);
lean_closure_set(v___f_2213_, 9, v_args_2201_);
lean_closure_set(v___f_2213_, 10, v_fst_2205_);
v___x_2214_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_fst_2205_, v___f_2213_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
return v___x_2214_;
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec_ref(v_args_2201_);
lean_dec(v_hyp_2200_);
lean_dec(v___x_2197_);
v_a_2215_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2202_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2202_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___boxed(lean_object* v_x_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure(v_x_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1(){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2243_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2244_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1));
v___x_2245_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1));
v___x_2246_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___boxed), 10, 0);
v___x_2247_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2243_, v___x_2244_, v___x_2245_, v___x_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___boxed(lean_object* v_a_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1();
return v_res_2249_;
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
