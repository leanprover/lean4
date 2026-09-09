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
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v_ref_136_; lean_object* v___x_137_; lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_182_; 
v_ref_136_ = lean_ctor_get(v___y_133_, 2);
v___x_137_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(v_msg_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
v_a_138_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_182_ == 0)
{
v___x_140_ = v___x_137_;
v_isShared_141_ = v_isSharedCheck_182_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_137_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_182_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v_traceState_143_; lean_object* v_env_144_; lean_object* v_nextMacroScope_145_; lean_object* v_ngen_146_; lean_object* v_auxDeclNGen_147_; lean_object* v_cache_148_; lean_object* v_messages_149_; lean_object* v_infoState_150_; lean_object* v_snapshotTasks_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_181_; 
v___x_142_ = lean_st_ref_take(v___y_134_);
v_traceState_143_ = lean_ctor_get(v___x_142_, 4);
v_env_144_ = lean_ctor_get(v___x_142_, 0);
v_nextMacroScope_145_ = lean_ctor_get(v___x_142_, 1);
v_ngen_146_ = lean_ctor_get(v___x_142_, 2);
v_auxDeclNGen_147_ = lean_ctor_get(v___x_142_, 3);
v_cache_148_ = lean_ctor_get(v___x_142_, 5);
v_messages_149_ = lean_ctor_get(v___x_142_, 6);
v_infoState_150_ = lean_ctor_get(v___x_142_, 7);
v_snapshotTasks_151_ = lean_ctor_get(v___x_142_, 8);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_181_ == 0)
{
v___x_153_ = v___x_142_;
v_isShared_154_ = v_isSharedCheck_181_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_snapshotTasks_151_);
lean_inc(v_infoState_150_);
lean_inc(v_messages_149_);
lean_inc(v_cache_148_);
lean_inc(v_traceState_143_);
lean_inc(v_auxDeclNGen_147_);
lean_inc(v_ngen_146_);
lean_inc(v_nextMacroScope_145_);
lean_inc(v_env_144_);
lean_dec(v___x_142_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_181_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
uint64_t v_tid_155_; lean_object* v_traces_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_180_; 
v_tid_155_ = lean_ctor_get_uint64(v_traceState_143_, sizeof(void*)*1);
v_traces_156_ = lean_ctor_get(v_traceState_143_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v_traceState_143_);
if (v_isSharedCheck_180_ == 0)
{
v___x_158_ = v_traceState_143_;
v_isShared_159_ = v_isSharedCheck_180_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_traces_156_);
lean_dec(v_traceState_143_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_180_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; double v___x_161_; uint8_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_160_ = lean_box(0);
v___x_161_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0);
v___x_162_ = 0;
v___x_163_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__1));
v___x_164_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_164_, 0, v_cls_129_);
lean_ctor_set(v___x_164_, 1, v___x_160_);
lean_ctor_set(v___x_164_, 2, v___x_163_);
lean_ctor_set_float(v___x_164_, sizeof(void*)*3, v___x_161_);
lean_ctor_set_float(v___x_164_, sizeof(void*)*3 + 8, v___x_161_);
lean_ctor_set_uint8(v___x_164_, sizeof(void*)*3 + 16, v___x_162_);
v___x_165_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__2));
v___x_166_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v_a_138_);
lean_ctor_set(v___x_166_, 2, v___x_165_);
lean_inc(v_ref_136_);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v_ref_136_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = l_Lean_PersistentArray_push___redArg(v_traces_156_, v___x_167_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_168_);
v___x_170_ = v___x_158_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_168_);
lean_ctor_set_uint64(v_reuseFailAlloc_179_, sizeof(void*)*1, v_tid_155_);
v___x_170_ = v_reuseFailAlloc_179_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_172_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 4, v___x_170_);
v___x_172_ = v___x_153_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_env_144_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_nextMacroScope_145_);
lean_ctor_set(v_reuseFailAlloc_178_, 2, v_ngen_146_);
lean_ctor_set(v_reuseFailAlloc_178_, 3, v_auxDeclNGen_147_);
lean_ctor_set(v_reuseFailAlloc_178_, 4, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_178_, 5, v_cache_148_);
lean_ctor_set(v_reuseFailAlloc_178_, 6, v_messages_149_);
lean_ctor_set(v_reuseFailAlloc_178_, 7, v_infoState_150_);
lean_ctor_set(v_reuseFailAlloc_178_, 8, v_snapshotTasks_151_);
v___x_172_ = v_reuseFailAlloc_178_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_173_ = lean_st_ref_put(v___y_134_, v___x_172_);
v___x_174_ = lean_box(0);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_174_);
v___x_176_ = v___x_140_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___boxed(lean_object* v_cls_183_, lean_object* v_msg_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v_cls_183_, v_msg_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(lean_object* v_msg_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_ref_197_; lean_object* v___x_198_; lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_207_; 
v_ref_197_ = lean_ctor_get(v___y_194_, 2);
v___x_198_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(v_msg_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
v_a_199_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_207_ == 0)
{
v___x_201_ = v___x_198_;
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_205_; 
lean_inc(v_ref_197_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_ref_197_);
lean_ctor_set(v___x_203_, 1, v_a_199_);
if (v_isShared_202_ == 0)
{
lean_ctor_set_tag(v___x_201_, 1);
lean_ctor_set(v___x_201_, 0, v___x_203_);
v___x_205_ = v___x_201_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg___boxed(lean_object* v_msg_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v_msg_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
return v_res_214_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__5));
v___x_228_ = l_Lean_stringToMessageData(v___x_227_);
return v___x_228_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__7));
v___x_231_ = l_Lean_stringToMessageData(v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_236_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__10));
v___x_237_ = l_Lean_Name_append(v___x_236_, v___x_235_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__12));
v___x_240_ = l_Lean_stringToMessageData(v___x_239_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__14));
v___x_243_ = l_Lean_stringToMessageData(v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(lean_object* v_P_244_, lean_object* v_QR_245_, lean_object* v_arg_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
uint8_t v___x_259_; 
v___x_259_ = l_Lean_Syntax_isIdent(v_arg_246_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v_arg_246_);
lean_dec_ref(v_QR_245_);
lean_dec_ref(v_P_244_);
v___x_260_ = lean_box(0);
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
return v___x_261_;
}
else
{
lean_object* v___x_262_; 
lean_inc_ref(v_QR_245_);
v___x_262_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_QR_245_);
if (lean_obj_tag(v___x_262_) == 1)
{
lean_object* v_val_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_420_; 
v_val_263_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_420_ == 0)
{
v___x_265_ = v___x_262_;
v_isShared_266_ = v_isSharedCheck_420_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_val_263_);
lean_dec(v___x_262_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_420_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v_p_267_; 
v_p_267_ = lean_ctor_get(v_val_263_, 2);
lean_inc_ref(v_p_267_);
if (lean_obj_tag(v_p_267_) == 5)
{
lean_object* v_fn_268_; 
v_fn_268_ = lean_ctor_get(v_p_267_, 0);
if (lean_obj_tag(v_fn_268_) == 5)
{
lean_object* v_fn_269_; 
v_fn_269_ = lean_ctor_get(v_fn_268_, 0);
if (lean_obj_tag(v_fn_269_) == 5)
{
lean_object* v_fn_270_; 
v_fn_270_ = lean_ctor_get(v_fn_269_, 0);
if (lean_obj_tag(v_fn_270_) == 4)
{
lean_object* v_declName_271_; 
v_declName_271_ = lean_ctor_get(v_fn_270_, 0);
if (lean_obj_tag(v_declName_271_) == 1)
{
lean_object* v_pre_272_; 
v_pre_272_ = lean_ctor_get(v_declName_271_, 0);
if (lean_obj_tag(v_pre_272_) == 1)
{
lean_object* v_pre_273_; 
v_pre_273_ = lean_ctor_get(v_pre_272_, 0);
if (lean_obj_tag(v_pre_273_) == 1)
{
lean_object* v_pre_274_; 
v_pre_274_ = lean_ctor_get(v_pre_273_, 0);
if (lean_obj_tag(v_pre_274_) == 1)
{
lean_object* v_pre_275_; 
v_pre_275_ = lean_ctor_get(v_pre_274_, 0);
if (lean_obj_tag(v_pre_275_) == 0)
{
lean_object* v_name_276_; lean_object* v_uniq_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_418_; 
v_name_276_ = lean_ctor_get(v_val_263_, 0);
v_uniq_277_ = lean_ctor_get(v_val_263_, 1);
v_isSharedCheck_418_ = !lean_is_exclusive(v_val_263_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; 
v_unused_419_ = lean_ctor_get(v_val_263_, 2);
lean_dec(v_unused_419_);
v___x_279_ = v_val_263_;
v_isShared_280_ = v_isSharedCheck_418_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_uniq_277_);
lean_inc(v_name_276_);
lean_dec(v_val_263_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_418_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v_arg_281_; lean_object* v_arg_282_; lean_object* v_arg_283_; lean_object* v_us_284_; lean_object* v_str_285_; lean_object* v_str_286_; lean_object* v_str_287_; lean_object* v_str_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v_arg_281_ = lean_ctor_get(v_p_267_, 1);
v_arg_282_ = lean_ctor_get(v_fn_268_, 1);
v_arg_283_ = lean_ctor_get(v_fn_269_, 1);
v_us_284_ = lean_ctor_get(v_fn_270_, 1);
v_str_285_ = lean_ctor_get(v_declName_271_, 1);
v_str_286_ = lean_ctor_get(v_pre_272_, 1);
v_str_287_ = lean_ctor_get(v_pre_273_, 1);
v_str_288_ = lean_ctor_get(v_pre_274_, 1);
v___x_289_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_290_ = lean_string_dec_eq(v_str_288_, v___x_289_);
if (v___x_290_ == 0)
{
lean_del_object(v___x_279_);
lean_dec(v_uniq_277_);
lean_dec(v_name_276_);
lean_dec_ref_known(v_p_267_, 2);
lean_del_object(v___x_265_);
lean_dec(v_arg_246_);
lean_dec_ref(v_QR_245_);
lean_dec_ref(v_P_244_);
goto v___jp_256_;
}
else
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_292_ = lean_string_dec_eq(v_str_287_, v___x_291_);
if (v___x_292_ == 0)
{
lean_del_object(v___x_279_);
lean_dec(v_uniq_277_);
lean_dec(v_name_276_);
lean_dec_ref_known(v_p_267_, 2);
lean_del_object(v___x_265_);
lean_dec(v_arg_246_);
lean_dec_ref(v_QR_245_);
lean_dec_ref(v_P_244_);
goto v___jp_256_;
}
else
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_294_ = lean_string_dec_eq(v_str_286_, v___x_293_);
if (v___x_294_ == 0)
{
lean_del_object(v___x_279_);
lean_dec(v_uniq_277_);
lean_dec(v_name_276_);
lean_dec_ref_known(v_p_267_, 2);
lean_del_object(v___x_265_);
lean_dec(v_arg_246_);
lean_dec_ref(v_QR_245_);
lean_dec_ref(v_P_244_);
goto v___jp_256_;
}
else
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__2));
v___x_296_ = lean_string_dec_eq(v_str_285_, v___x_295_);
if (v___x_296_ == 0)
{
lean_del_object(v___x_279_);
lean_dec(v_uniq_277_);
lean_dec(v_name_276_);
lean_dec_ref_known(v_p_267_, 2);
lean_del_object(v___x_265_);
lean_dec(v_arg_246_);
lean_dec_ref(v_QR_245_);
lean_dec_ref(v_P_244_);
goto v___jp_256_;
}
else
{
if (lean_obj_tag(v_us_284_) == 1)
{
lean_object* v_tail_297_; 
v_tail_297_ = lean_ctor_get(v_us_284_, 1);
if (lean_obj_tag(v_tail_297_) == 0)
{
lean_object* v_head_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_head_298_ = lean_ctor_get(v_us_284_, 0);
lean_inc_ref(v_P_244_);
lean_inc_ref_n(v_arg_283_, 2);
lean_inc_n(v_head_298_, 2);
v___x_299_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_head_298_, v_arg_283_, v_P_244_, v_QR_245_);
v___x_300_ = l_Lean_Syntax_getId(v_arg_246_);
v___x_301_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(v_head_298_, v_arg_283_, v___x_299_, v___x_300_);
lean_dec(v___x_300_);
if (lean_obj_tag(v___x_301_) == 1)
{
lean_object* v_val_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_413_; 
lean_del_object(v___x_265_);
v_val_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_413_ == 0)
{
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_413_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_val_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_413_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v_focusHyp_306_; lean_object* v_restHyps_307_; lean_object* v_proof_308_; lean_object* v___x_309_; 
v_focusHyp_306_ = lean_ctor_get(v_val_302_, 0);
lean_inc_ref_n(v_focusHyp_306_, 2);
v_restHyps_307_ = lean_ctor_get(v_val_302_, 1);
lean_inc_ref(v_restHyps_307_);
v_proof_308_ = lean_ctor_get(v_val_302_, 2);
lean_inc_ref(v_proof_308_);
lean_dec(v_val_302_);
v___x_309_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_306_);
if (lean_obj_tag(v___x_309_) == 1)
{
lean_object* v_val_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_408_; 
lean_del_object(v___x_304_);
v_val_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_408_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_408_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_val_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_408_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
uint8_t v___x_314_; lean_object* v___x_315_; 
v___x_314_ = 0;
lean_inc_ref(v_arg_283_);
v___x_315_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_arg_246_, v_arg_283_, v_val_310_, v___x_314_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_398_; 
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_398_ == 0)
{
lean_object* v_unused_399_; 
v_unused_399_ = lean_ctor_get(v___x_315_, 0);
lean_dec(v_unused_399_);
v___x_317_ = v___x_315_;
v_isShared_318_ = v_isSharedCheck_398_;
goto v_resetjp_316_;
}
else
{
lean_dec(v___x_315_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_398_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v_toCold_319_; lean_object* v_options_320_; lean_object* v_inheritedTraceOptions_321_; uint8_t v_hasTrace_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; 
v_toCold_319_ = lean_ctor_get(v_a_253_, 0);
v_options_320_ = lean_ctor_get(v_toCold_319_, 2);
v_inheritedTraceOptions_321_ = lean_ctor_get(v_toCold_319_, 11);
v_hasTrace_322_ = lean_ctor_get_uint8(v_options_320_, sizeof(void*)*1);
v___x_323_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4));
lean_inc_ref(v_us_284_);
v___x_324_ = l_Lean_mkConst(v___x_323_, v_us_284_);
lean_inc_ref(v_arg_281_);
lean_inc_ref(v_focusHyp_306_);
lean_inc_ref(v_P_244_);
lean_inc_ref(v_arg_283_);
v___x_325_ = l_Lean_mkApp6(v___x_324_, v_arg_283_, v_P_244_, v_restHyps_307_, v_focusHyp_306_, v_arg_281_, v_proof_308_);
if (v_hasTrace_322_ == 0)
{
lean_dec_ref(v_P_244_);
v___y_339_ = v_a_247_;
v___y_340_ = v_a_248_;
v___y_341_ = v_a_249_;
v___y_342_ = v_a_250_;
v___y_343_ = v_a_251_;
v___y_344_ = v_a_252_;
v___y_345_ = v_a_253_;
v___y_346_ = v_a_254_;
goto v___jp_338_;
}
else
{
lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_374_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_375_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11);
v___x_376_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_321_, v_options_320_, v___x_375_);
if (v___x_376_ == 0)
{
lean_dec_ref(v_P_244_);
v___y_339_ = v_a_247_;
v___y_340_ = v_a_248_;
v___y_341_ = v_a_249_;
v___y_342_ = v_a_250_;
v___y_343_ = v_a_251_;
v___y_344_ = v_a_252_;
v___y_345_ = v_a_253_;
v___y_346_ = v_a_254_;
goto v___jp_338_;
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_377_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13);
lean_inc_ref(v_p_267_);
v___x_378_ = l_Lean_MessageData_ofExpr(v_p_267_);
v___x_379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_377_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_379_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
lean_inc_ref(v_focusHyp_306_);
v___x_382_ = l_Lean_MessageData_ofExpr(v_focusHyp_306_);
v___x_383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_381_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
v___x_384_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15);
v___x_385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_383_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
lean_inc_ref(v_arg_281_);
lean_inc_ref(v_arg_283_);
lean_inc(v_head_298_);
v___x_386_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_head_298_, v_arg_283_, v_P_244_, v_arg_281_);
v___x_387_ = l_Lean_MessageData_ofExpr(v___x_386_);
v___x_388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_385_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v___x_374_, v___x_388_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_dec_ref_known(v___x_389_, 1);
v___y_339_ = v_a_247_;
v___y_340_ = v_a_248_;
v___y_341_ = v_a_249_;
v___y_342_ = v_a_250_;
v___y_343_ = v_a_251_;
v___y_344_ = v_a_252_;
v___y_345_ = v_a_253_;
v___y_346_ = v_a_254_;
goto v___jp_338_;
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec_ref(v___x_325_);
lean_del_object(v___x_317_);
lean_del_object(v___x_312_);
lean_dec_ref(v_focusHyp_306_);
lean_del_object(v___x_279_);
lean_dec(v_uniq_277_);
lean_dec(v_name_276_);
lean_dec_ref_known(v_p_267_, 2);
v_a_390_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_389_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_389_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
v___jp_326_:
{
lean_object* v___x_328_; 
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 2, v_arg_281_);
v___x_328_ = v___x_279_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_name_276_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_uniq_277_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_arg_281_);
v___x_328_ = v_reuseFailAlloc_337_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_329_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_328_);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_325_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_330_);
v___x_332_ = v___x_312_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_330_);
v___x_332_ = v_reuseFailAlloc_336_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_334_; 
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_332_);
v___x_334_ = v___x_317_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
v___jp_338_:
{
lean_object* v___x_347_; 
lean_inc_ref(v_arg_282_);
lean_inc_ref(v_focusHyp_306_);
v___x_347_ = l_Lean_Meta_isExprDefEq(v_focusHyp_306_, v_arg_282_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; uint8_t v___x_349_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 1);
v___x_349_ = lean_unbox(v_a_348_);
lean_dec(v_a_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec_ref(v___x_325_);
lean_del_object(v___x_317_);
lean_del_object(v___x_312_);
lean_del_object(v___x_279_);
lean_dec(v_uniq_277_);
lean_dec(v_name_276_);
v___x_350_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6);
v___x_351_ = l_Lean_MessageData_ofExpr(v_p_267_);
v___x_352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_352_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = l_Lean_MessageData_ofExpr(v_focusHyp_306_);
v___x_356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_356_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
else
{
lean_inc_ref(v_arg_281_);
lean_dec_ref(v_focusHyp_306_);
lean_dec_ref_known(v_p_267_, 2);
goto v___jp_326_;
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_dec_ref(v___x_325_);
lean_del_object(v___x_317_);
lean_del_object(v___x_312_);
lean_dec_ref(v_focusHyp_306_);
lean_del_object(v___x_279_);
lean_dec(v_uniq_277_);
lean_dec(v_name_276_);
lean_dec_ref_known(v_p_267_, 2);
v_a_366_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_347_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_347_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_del_object(v___x_312_);
lean_dec_ref(v_proof_308_);
lean_dec_ref(v_restHyps_307_);
lean_dec_ref(v_focusHyp_306_);
lean_del_object(v___x_279_);
lean_dec(v_uniq_277_);
lean_dec(v_name_276_);
lean_dec_ref_known(v_p_267_, 2);
lean_dec_ref(v_P_244_);
v_a_400_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_315_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_315_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
else
{
lean_object* v___x_409_; lean_object* v___x_411_; 
lean_dec(v___x_309_);
lean_dec_ref(v_proof_308_);
lean_dec_ref(v_restHyps_307_);
lean_dec_ref(v_focusHyp_306_);
lean_del_object(v___x_279_);
lean_dec(v_uniq_277_);
lean_dec(v_name_276_);
lean_dec_ref_known(v_p_267_, 2);
lean_dec(v_arg_246_);
lean_dec_ref(v_P_244_);
v___x_409_ = lean_box(0);
if (v_isShared_305_ == 0)
{
lean_ctor_set_tag(v___x_304_, 0);
lean_ctor_set(v___x_304_, 0, v___x_409_);
v___x_411_ = v___x_304_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
else
{
lean_object* v___x_414_; lean_object* v___x_416_; 
lean_dec(v___x_301_);
lean_del_object(v___x_279_);
lean_dec(v_uniq_277_);
lean_dec(v_name_276_);
lean_dec_ref_known(v_p_267_, 2);
lean_dec(v_arg_246_);
lean_dec_ref(v_P_244_);
v___x_414_ = lean_box(0);
if (v_isShared_266_ == 0)
{
lean_ctor_set_tag(v___x_265_, 0);
lean_ctor_set(v___x_265_, 0, v___x_414_);
v___x_416_ = v___x_265_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
else
{
lean_del_object(v___x_279_);
lean_dec(v_uniq_277_);
lean_dec(v_name_276_);
lean_dec_ref_known(v_p_267_, 2);
lean_del_object(v___x_265_);
lean_dec(v_arg_246_);
lean_dec_ref(v_QR_245_);
lean_dec_ref(v_P_244_);
goto v___jp_256_;
}
}
else
{
lean_del_object(v___x_279_);
lean_dec(v_uniq_277_);
lean_dec(v_name_276_);
lean_dec_ref_known(v_p_267_, 2);
lean_del_object(v___x_265_);
lean_dec(v_arg_246_);
lean_dec_ref(v_QR_245_);
lean_dec_ref(v_P_244_);
goto v___jp_256_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_p_267_, 2);
lean_del_object(v___x_265_);
lean_dec(v_val_263_);
lean_dec(v_arg_246_);
lean_dec_ref(v_QR_245_);
lean_dec_ref(v_P_244_);
goto v___jp_256_;
}
}
else
{
lean_dec_ref_known(v_p_267_, 2);
lean_del_object(v___x_265_);
lean_dec(v_val_263_);
lean_dec(v_arg_246_);
lean_dec_ref(v_QR_245_);
lean_dec_ref(v_P_244_);
goto v___jp_256_;
}
}
else
{
lean_dec_ref_known(v_p_267_, 2);
lean_del_object(v___x_265_);
lean_dec(v_val_263_);
lean_dec(v_arg_246_);
lean_dec_ref(v_QR_245_);
lean_dec_ref(v_P_244_);
goto v___jp_256_;
}
}
else
{
lean_dec_ref_known(v_p_267_, 2);
lean_del_object(v___x_265_);
lean_dec(v_val_263_);
lean_dec(v_arg_246_);
lean_dec_ref(v_QR_245_);
lean_dec_ref(v_P_244_);
goto v___jp_256_;
}
}
else
{
lean_dec_ref_known(v_p_267_, 2);
lean_del_object(v___x_265_);
lean_dec(v_val_263_);
lean_dec(v_arg_246_);
lean_dec_ref(v_QR_245_);
lean_dec_ref(v_P_244_);
goto v___jp_256_;
}
}
else
{
lean_dec_ref_known(v_p_267_, 2);
lean_del_object(v___x_265_);
lean_dec(v_val_263_);
lean_dec(v_arg_246_);
lean_dec_ref(v_QR_245_);
lean_dec_ref(v_P_244_);
goto v___jp_256_;
}
}
else
{
lean_dec_ref_known(v_p_267_, 2);
lean_del_object(v___x_265_);
lean_dec(v_val_263_);
lean_dec(v_arg_246_);
lean_dec_ref(v_QR_245_);
lean_dec_ref(v_P_244_);
goto v___jp_256_;
}
}
else
{
lean_dec_ref_known(v_p_267_, 2);
lean_del_object(v___x_265_);
lean_dec(v_val_263_);
lean_dec(v_arg_246_);
lean_dec_ref(v_QR_245_);
lean_dec_ref(v_P_244_);
goto v___jp_256_;
}
}
else
{
lean_dec_ref(v_p_267_);
lean_del_object(v___x_265_);
lean_dec(v_val_263_);
lean_dec(v_arg_246_);
lean_dec_ref(v_QR_245_);
lean_dec_ref(v_P_244_);
goto v___jp_256_;
}
}
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec(v___x_262_);
lean_dec(v_arg_246_);
lean_dec_ref(v_QR_245_);
lean_dec_ref(v_P_244_);
v___x_421_ = lean_box(0);
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
return v___x_422_;
}
}
v___jp_256_:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_box(0);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___boxed(lean_object* v_P_423_, lean_object* v_QR_424_, lean_object* v_arg_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(v_P_423_, v_QR_424_, v_arg_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0(lean_object* v_00_u03b1_436_, lean_object* v_msg_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v_msg_437_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___boxed(lean_object* v_00_u03b1_448_, lean_object* v_msg_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0(v_00_u03b1_448_, v_msg_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1(lean_object* v_cls_460_, lean_object* v_msg_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v_cls_460_, v_msg_461_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___boxed(lean_object* v_cls_472_, lean_object* v_msg_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1(v_cls_472_, v_msg_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
return v_res_483_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0(void){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_instMonadEIO(lean_box(0));
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(lean_object* v_msg_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v_toApplicative_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_595_; 
v___x_501_ = lean_obj_once(&l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0, &l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0);
v___x_502_ = l_StateRefT_x27_instMonad___redArg(v___x_501_);
v_toApplicative_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; 
v_unused_596_ = lean_ctor_get(v___x_502_, 1);
lean_dec(v_unused_596_);
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_595_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_toApplicative_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_595_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v_toFunctor_507_; lean_object* v_toSeq_508_; lean_object* v_toSeqLeft_509_; lean_object* v_toSeqRight_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_593_; 
v_toFunctor_507_ = lean_ctor_get(v_toApplicative_503_, 0);
v_toSeq_508_ = lean_ctor_get(v_toApplicative_503_, 2);
v_toSeqLeft_509_ = lean_ctor_get(v_toApplicative_503_, 3);
v_toSeqRight_510_ = lean_ctor_get(v_toApplicative_503_, 4);
v_isSharedCheck_593_ = !lean_is_exclusive(v_toApplicative_503_);
if (v_isSharedCheck_593_ == 0)
{
lean_object* v_unused_594_; 
v_unused_594_ = lean_ctor_get(v_toApplicative_503_, 1);
lean_dec(v_unused_594_);
v___x_512_ = v_toApplicative_503_;
v_isShared_513_ = v_isSharedCheck_593_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_toSeqRight_510_);
lean_inc(v_toSeqLeft_509_);
lean_inc(v_toSeq_508_);
lean_inc(v_toFunctor_507_);
lean_dec(v_toApplicative_503_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_593_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___f_514_; lean_object* v___f_515_; lean_object* v___f_516_; lean_object* v___f_517_; lean_object* v___x_518_; lean_object* v___f_519_; lean_object* v___f_520_; lean_object* v___f_521_; lean_object* v___x_523_; 
v___f_514_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__1));
v___f_515_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__2));
lean_inc_ref(v_toFunctor_507_);
v___f_516_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_516_, 0, v_toFunctor_507_);
v___f_517_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_517_, 0, v_toFunctor_507_);
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v___f_516_);
lean_ctor_set(v___x_518_, 1, v___f_517_);
v___f_519_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_519_, 0, v_toSeqRight_510_);
v___f_520_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_520_, 0, v_toSeqLeft_509_);
v___f_521_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_521_, 0, v_toSeq_508_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v___f_519_);
lean_ctor_set(v___x_512_, 3, v___f_520_);
lean_ctor_set(v___x_512_, 2, v___f_521_);
lean_ctor_set(v___x_512_, 1, v___f_514_);
lean_ctor_set(v___x_512_, 0, v___x_518_);
v___x_523_ = v___x_512_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v___f_514_);
lean_ctor_set(v_reuseFailAlloc_592_, 2, v___f_521_);
lean_ctor_set(v_reuseFailAlloc_592_, 3, v___f_520_);
lean_ctor_set(v_reuseFailAlloc_592_, 4, v___f_519_);
v___x_523_ = v_reuseFailAlloc_592_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
lean_object* v___x_525_; 
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 1, v___f_515_);
lean_ctor_set(v___x_505_, 0, v___x_523_);
v___x_525_ = v___x_505_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v___f_515_);
v___x_525_ = v_reuseFailAlloc_591_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_526_; lean_object* v_toApplicative_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_589_; 
v___x_526_ = l_StateRefT_x27_instMonad___redArg(v___x_525_);
v_toApplicative_527_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; 
v_unused_590_ = lean_ctor_get(v___x_526_, 1);
lean_dec(v_unused_590_);
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_589_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_toApplicative_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_589_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v_toFunctor_531_; lean_object* v_toSeq_532_; lean_object* v_toSeqLeft_533_; lean_object* v_toSeqRight_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_587_; 
v_toFunctor_531_ = lean_ctor_get(v_toApplicative_527_, 0);
v_toSeq_532_ = lean_ctor_get(v_toApplicative_527_, 2);
v_toSeqLeft_533_ = lean_ctor_get(v_toApplicative_527_, 3);
v_toSeqRight_534_ = lean_ctor_get(v_toApplicative_527_, 4);
v_isSharedCheck_587_ = !lean_is_exclusive(v_toApplicative_527_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; 
v_unused_588_ = lean_ctor_get(v_toApplicative_527_, 1);
lean_dec(v_unused_588_);
v___x_536_ = v_toApplicative_527_;
v_isShared_537_ = v_isSharedCheck_587_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_toSeqRight_534_);
lean_inc(v_toSeqLeft_533_);
lean_inc(v_toSeq_532_);
lean_inc(v_toFunctor_531_);
lean_dec(v_toApplicative_527_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_587_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___f_538_; lean_object* v___f_539_; lean_object* v___f_540_; lean_object* v___f_541_; lean_object* v___x_542_; lean_object* v___f_543_; lean_object* v___f_544_; lean_object* v___f_545_; lean_object* v___x_547_; 
v___f_538_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__3));
v___f_539_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__4));
lean_inc_ref(v_toFunctor_531_);
v___f_540_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_540_, 0, v_toFunctor_531_);
v___f_541_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_541_, 0, v_toFunctor_531_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___f_540_);
lean_ctor_set(v___x_542_, 1, v___f_541_);
v___f_543_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_543_, 0, v_toSeqRight_534_);
v___f_544_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_544_, 0, v_toSeqLeft_533_);
v___f_545_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_545_, 0, v_toSeq_532_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 4, v___f_543_);
lean_ctor_set(v___x_536_, 3, v___f_544_);
lean_ctor_set(v___x_536_, 2, v___f_545_);
lean_ctor_set(v___x_536_, 1, v___f_538_);
lean_ctor_set(v___x_536_, 0, v___x_542_);
v___x_547_ = v___x_536_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v___f_538_);
lean_ctor_set(v_reuseFailAlloc_586_, 2, v___f_545_);
lean_ctor_set(v_reuseFailAlloc_586_, 3, v___f_544_);
lean_ctor_set(v_reuseFailAlloc_586_, 4, v___f_543_);
v___x_547_ = v_reuseFailAlloc_586_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_549_; 
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 1, v___f_539_);
lean_ctor_set(v___x_529_, 0, v___x_547_);
v___x_549_ = v___x_529_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v___f_539_);
v___x_549_ = v_reuseFailAlloc_585_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; lean_object* v_toApplicative_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_583_; 
v___x_550_ = l_StateRefT_x27_instMonad___redArg(v___x_549_);
v_toApplicative_551_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_583_ == 0)
{
lean_object* v_unused_584_; 
v_unused_584_ = lean_ctor_get(v___x_550_, 1);
lean_dec(v_unused_584_);
v___x_553_ = v___x_550_;
v_isShared_554_ = v_isSharedCheck_583_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_toApplicative_551_);
lean_dec(v___x_550_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_583_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v_toFunctor_555_; lean_object* v_toSeq_556_; lean_object* v_toSeqLeft_557_; lean_object* v_toSeqRight_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_581_; 
v_toFunctor_555_ = lean_ctor_get(v_toApplicative_551_, 0);
v_toSeq_556_ = lean_ctor_get(v_toApplicative_551_, 2);
v_toSeqLeft_557_ = lean_ctor_get(v_toApplicative_551_, 3);
v_toSeqRight_558_ = lean_ctor_get(v_toApplicative_551_, 4);
v_isSharedCheck_581_ = !lean_is_exclusive(v_toApplicative_551_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v_toApplicative_551_, 1);
lean_dec(v_unused_582_);
v___x_560_ = v_toApplicative_551_;
v_isShared_561_ = v_isSharedCheck_581_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_toSeqRight_558_);
lean_inc(v_toSeqLeft_557_);
lean_inc(v_toSeq_556_);
lean_inc(v_toFunctor_555_);
lean_dec(v_toApplicative_551_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_581_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___f_562_; lean_object* v___f_563_; lean_object* v___f_564_; lean_object* v___f_565_; lean_object* v___x_566_; lean_object* v___f_567_; lean_object* v___f_568_; lean_object* v___f_569_; lean_object* v___x_571_; 
v___f_562_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__5));
v___f_563_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__6));
lean_inc_ref(v_toFunctor_555_);
v___f_564_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_564_, 0, v_toFunctor_555_);
v___f_565_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_565_, 0, v_toFunctor_555_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v___f_564_);
lean_ctor_set(v___x_566_, 1, v___f_565_);
v___f_567_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_567_, 0, v_toSeqRight_558_);
v___f_568_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_568_, 0, v_toSeqLeft_557_);
v___f_569_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_569_, 0, v_toSeq_556_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 4, v___f_567_);
lean_ctor_set(v___x_560_, 3, v___f_568_);
lean_ctor_set(v___x_560_, 2, v___f_569_);
lean_ctor_set(v___x_560_, 1, v___f_562_);
lean_ctor_set(v___x_560_, 0, v___x_566_);
v___x_571_ = v___x_560_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v___f_562_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v___f_569_);
lean_ctor_set(v_reuseFailAlloc_580_, 3, v___f_568_);
lean_ctor_set(v_reuseFailAlloc_580_, 4, v___f_567_);
v___x_571_ = v_reuseFailAlloc_580_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_573_; 
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 1, v___f_563_);
lean_ctor_set(v___x_553_, 0, v___x_571_);
v___x_573_ = v___x_553_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v___f_563_);
v___x_573_ = v_reuseFailAlloc_579_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_10547__overap_577_; lean_object* v___x_578_; 
v___x_574_ = l_StateRefT_x27_instMonad___redArg(v___x_573_);
v___x_575_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_575_, 0, lean_box(0));
lean_closure_set(v___x_575_, 1, lean_box(0));
lean_closure_set(v___x_575_, 2, v___x_574_);
v___x_576_ = l_OptionT_instInhabitedOfPure___redArg(v___x_575_);
v___x_10547__overap_577_ = lean_panic_fn_borrowed(v___x_576_, v_msg_491_);
lean_dec(v___x_576_);
lean_inc(v___y_499_);
lean_inc_ref(v___y_498_);
lean_inc(v___y_497_);
lean_inc_ref(v___y_496_);
lean_inc(v___y_495_);
lean_inc_ref(v___y_494_);
lean_inc(v___y_493_);
lean_inc_ref(v___y_492_);
v___x_578_ = lean_apply_9(v___x_10547__overap_577_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, lean_box(0));
return v___x_578_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___boxed(lean_object* v_msg_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(v_msg_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
return v_res_607_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_box(0);
v___x_609_ = l_Lean_mkSort(v___x_608_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0);
v___x_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__9));
v___x_638_ = l_Lean_stringToMessageData(v___x_637_);
return v___x_638_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_657_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__17));
v___x_658_ = lean_unsigned_to_nat(37u);
v___x_659_ = lean_unsigned_to_nat(45u);
v___x_660_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__16));
v___x_661_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15));
v___x_662_ = l_mkPanicMessageWithDecl(v___x_661_, v___x_660_, v___x_659_, v___x_658_, v___x_657_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(lean_object* v_P_663_, lean_object* v_QR_664_, lean_object* v_arg_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_QR_664_);
if (lean_obj_tag(v___x_678_) == 1)
{
lean_object* v_val_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_857_; 
v_val_679_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_857_ == 0)
{
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_857_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_val_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_857_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v_p_683_; 
v_p_683_ = lean_ctor_get(v_val_679_, 2);
lean_inc_ref(v_p_683_);
if (lean_obj_tag(v_p_683_) == 5)
{
lean_object* v_name_684_; lean_object* v_uniq_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_855_; 
v_name_684_ = lean_ctor_get(v_val_679_, 0);
v_uniq_685_ = lean_ctor_get(v_val_679_, 1);
v_isSharedCheck_855_ = !lean_is_exclusive(v_val_679_);
if (v_isSharedCheck_855_ == 0)
{
lean_object* v_unused_856_; 
v_unused_856_ = lean_ctor_get(v_val_679_, 2);
lean_dec(v_unused_856_);
v___x_687_ = v_val_679_;
v_isShared_688_ = v_isSharedCheck_855_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_uniq_685_);
lean_inc(v_name_684_);
lean_dec(v_val_679_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_855_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v_fn_689_; lean_object* v_arg_690_; lean_object* v___y_692_; 
v_fn_689_ = lean_ctor_get(v_p_683_, 0);
v_arg_690_ = lean_ctor_get(v_p_683_, 1);
lean_inc_ref(v_arg_690_);
if (lean_obj_tag(v_fn_689_) == 5)
{
lean_object* v_fn_702_; 
v_fn_702_ = lean_ctor_get(v_fn_689_, 0);
if (lean_obj_tag(v_fn_702_) == 5)
{
lean_object* v_fn_703_; 
v_fn_703_ = lean_ctor_get(v_fn_702_, 0);
if (lean_obj_tag(v_fn_703_) == 4)
{
lean_object* v_declName_704_; 
v_declName_704_ = lean_ctor_get(v_fn_703_, 0);
if (lean_obj_tag(v_declName_704_) == 1)
{
lean_object* v_pre_705_; 
v_pre_705_ = lean_ctor_get(v_declName_704_, 0);
if (lean_obj_tag(v_pre_705_) == 1)
{
lean_object* v_pre_706_; 
v_pre_706_ = lean_ctor_get(v_pre_705_, 0);
if (lean_obj_tag(v_pre_706_) == 1)
{
lean_object* v_pre_707_; 
v_pre_707_ = lean_ctor_get(v_pre_706_, 0);
if (lean_obj_tag(v_pre_707_) == 1)
{
lean_object* v_pre_708_; 
v_pre_708_ = lean_ctor_get(v_pre_707_, 0);
if (lean_obj_tag(v_pre_708_) == 0)
{
lean_object* v_arg_709_; lean_object* v_arg_710_; lean_object* v_us_711_; lean_object* v_str_712_; lean_object* v_str_713_; lean_object* v_str_714_; lean_object* v_str_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v_arg_709_ = lean_ctor_get(v_fn_689_, 1);
lean_inc_ref(v_arg_709_);
v_arg_710_ = lean_ctor_get(v_fn_702_, 1);
lean_inc_ref(v_arg_710_);
v_us_711_ = lean_ctor_get(v_fn_703_, 1);
v_str_712_ = lean_ctor_get(v_declName_704_, 1);
v_str_713_ = lean_ctor_get(v_pre_705_, 1);
v_str_714_ = lean_ctor_get(v_pre_706_, 1);
v_str_715_ = lean_ctor_get(v_pre_707_, 1);
v___x_716_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_717_ = lean_string_dec_eq(v_str_715_, v___x_716_);
if (v___x_717_ == 0)
{
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_709_);
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec(v_name_684_);
lean_dec_ref_known(v_p_683_, 2);
lean_del_object(v___x_681_);
lean_dec(v_arg_665_);
lean_dec_ref(v_P_663_);
goto v___jp_675_;
}
else
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_719_ = lean_string_dec_eq(v_str_714_, v___x_718_);
if (v___x_719_ == 0)
{
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_709_);
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec(v_name_684_);
lean_dec_ref_known(v_p_683_, 2);
lean_del_object(v___x_681_);
lean_dec(v_arg_665_);
lean_dec_ref(v_P_663_);
goto v___jp_675_;
}
else
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_721_ = lean_string_dec_eq(v_str_713_, v___x_720_);
if (v___x_721_ == 0)
{
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_709_);
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec(v_name_684_);
lean_dec_ref_known(v_p_683_, 2);
lean_del_object(v___x_681_);
lean_dec(v_arg_665_);
lean_dec_ref(v_P_663_);
goto v___jp_675_;
}
else
{
lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_722_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__2));
v___x_723_ = lean_string_dec_eq(v_str_712_, v___x_722_);
if (v___x_723_ == 0)
{
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_709_);
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec(v_name_684_);
lean_dec_ref_known(v_p_683_, 2);
lean_del_object(v___x_681_);
lean_dec(v_arg_665_);
lean_dec_ref(v_P_663_);
goto v___jp_675_;
}
else
{
if (lean_obj_tag(v_us_711_) == 1)
{
lean_object* v_tail_724_; 
v_tail_724_ = lean_ctor_get(v_us_711_, 1);
if (lean_obj_tag(v_tail_724_) == 0)
{
lean_object* v_head_725_; lean_object* v___x_726_; uint8_t v___x_727_; lean_object* v___x_728_; 
v_head_725_ = lean_ctor_get(v_us_711_, 0);
lean_inc(v_head_725_);
v___x_726_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1);
v___x_727_ = 0;
v___x_728_ = l_Lean_Meta_mkFreshExprMVar(v___x_726_, v___x_727_, v_pre_708_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc_n(v_a_729_, 2);
lean_dec_ref_known(v___x_728_, 1);
v___x_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_730_, 0, v_a_729_);
v___x_731_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2));
v___x_732_ = lean_box(0);
v___x_733_ = l_Lean_Elab_Tactic_elabTermWithHoles(v_arg_665_, v___x_730_, v___x_731_, v___x_723_, v___x_732_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v_fst_735_; lean_object* v_snd_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_831_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_733_, 1);
v_fst_735_ = lean_ctor_get(v_a_734_, 0);
v_snd_736_ = lean_ctor_get(v_a_734_, 1);
v_isSharedCheck_831_ = !lean_is_exclusive(v_a_734_);
if (v_isSharedCheck_831_ == 0)
{
v___x_738_ = v_a_734_;
v_isShared_739_ = v_isSharedCheck_831_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_snd_736_);
lean_inc(v_fst_735_);
lean_dec(v_a_734_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_831_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_740_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4));
lean_inc_ref(v_us_711_);
v___x_741_ = l_Lean_mkConst(v___x_740_, v_us_711_);
lean_inc(v_a_729_);
lean_inc_ref(v_arg_709_);
lean_inc_ref(v_arg_710_);
v___x_742_ = l_Lean_mkApp3(v___x_741_, v_arg_710_, v_arg_709_, v_a_729_);
v___x_743_ = l_Lean_Meta_synthInstance_x3f(v___x_742_, v___x_732_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v_00_u03c6_746_; lean_object* v_h_u03c6_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref_known(v___x_743_, 1);
if (lean_obj_tag(v_a_744_) == 1)
{
lean_object* v_val_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v_val_816_ = lean_ctor_get(v_a_744_, 0);
lean_inc(v_val_816_);
lean_dec_ref_known(v_a_744_, 1);
v___x_817_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12));
lean_inc_ref_n(v_us_711_, 2);
v___x_818_ = l_Lean_mkConst(v___x_817_, v_us_711_);
lean_inc_ref_n(v_arg_709_, 2);
lean_inc_ref_n(v_arg_710_, 2);
v___x_819_ = l_Lean_mkApp5(v___x_818_, v_arg_710_, v_a_729_, v_arg_709_, v_val_816_, v_fst_735_);
v___x_820_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14));
v___x_821_ = l_Lean_mkConst(v___x_820_, v_us_711_);
v___x_822_ = l_Lean_mkAppB(v___x_821_, v_arg_710_, v_arg_709_);
v_00_u03c6_746_ = v___x_822_;
v_h_u03c6_747_ = v___x_819_;
v___y_748_ = v_a_667_;
v___y_749_ = v_a_670_;
v___y_750_ = v_a_671_;
v___y_751_ = v_a_672_;
v___y_752_ = v_a_673_;
goto v___jp_745_;
}
else
{
lean_dec(v_a_744_);
v_00_u03c6_746_ = v_a_729_;
v_h_u03c6_747_ = v_fst_735_;
v___y_748_ = v_a_667_;
v___y_749_ = v_a_670_;
v___y_750_ = v_a_671_;
v___y_751_ = v_a_672_;
v___y_752_ = v_a_673_;
goto v___jp_745_;
}
v___jp_745_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_753_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6));
lean_inc_ref(v_us_711_);
v___x_754_ = l_Lean_mkConst(v___x_753_, v_us_711_);
lean_inc_ref(v_arg_709_);
lean_inc_ref(v_arg_710_);
lean_inc_ref(v_00_u03c6_746_);
v___x_755_ = l_Lean_mkApp3(v___x_754_, v_00_u03c6_746_, v_arg_710_, v_arg_709_);
v___x_756_ = l_Lean_Meta_synthInstance_x3f(v___x_755_, v___x_732_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_807_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_807_ == 0)
{
v___x_759_ = v___x_756_;
v_isShared_760_ = v_isSharedCheck_807_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_756_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_807_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
if (lean_obj_tag(v_a_757_) == 1)
{
lean_object* v_val_761_; lean_object* v___x_762_; 
lean_del_object(v___x_759_);
v_val_761_ = lean_ctor_get(v_a_757_, 0);
lean_inc(v_val_761_);
lean_dec_ref_known(v_a_757_, 1);
v___x_762_ = l_Lean_Elab_Tactic_pushGoals___redArg(v_snd_736_, v___y_748_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_toCold_763_; lean_object* v_options_764_; lean_object* v_inheritedTraceOptions_765_; uint8_t v_hasTrace_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
lean_dec_ref_known(v___x_762_, 1);
v_toCold_763_ = lean_ctor_get(v___y_751_, 0);
v_options_764_ = lean_ctor_get(v_toCold_763_, 2);
v_inheritedTraceOptions_765_ = lean_ctor_get(v_toCold_763_, 11);
v_hasTrace_766_ = lean_ctor_get_uint8(v_options_764_, sizeof(void*)*1);
v___x_767_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8));
lean_inc_ref(v_us_711_);
v___x_768_ = l_Lean_mkConst(v___x_767_, v_us_711_);
lean_inc_ref(v_arg_690_);
lean_inc_ref(v_arg_709_);
lean_inc_ref(v_P_663_);
lean_inc_ref(v_arg_710_);
v___x_769_ = l_Lean_mkApp7(v___x_768_, v_arg_710_, v_00_u03c6_746_, v_P_663_, v_arg_709_, v_arg_690_, v_val_761_, v_h_u03c6_747_);
if (v_hasTrace_766_ == 0)
{
lean_del_object(v___x_738_);
lean_dec(v_head_725_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_709_);
lean_dec_ref_known(v_p_683_, 2);
lean_dec_ref(v_P_663_);
v___y_692_ = v___x_769_;
goto v___jp_691_;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_770_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_771_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11);
v___x_772_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_765_, v_options_764_, v___x_771_);
if (v___x_772_ == 0)
{
lean_del_object(v___x_738_);
lean_dec(v_head_725_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_709_);
lean_dec_ref_known(v_p_683_, 2);
lean_dec_ref(v_P_663_);
v___y_692_ = v___x_769_;
goto v___jp_691_;
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_773_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10);
v___x_774_ = l_Lean_MessageData_ofExpr(v_p_683_);
if (v_isShared_739_ == 0)
{
lean_ctor_set_tag(v___x_738_, 7);
lean_ctor_set(v___x_738_, 1, v___x_774_);
lean_ctor_set(v___x_738_, 0, v___x_773_);
v___x_776_ = v___x_738_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___x_774_);
v___x_776_ = v_reuseFailAlloc_795_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_777_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = l_Lean_MessageData_ofExpr(v_arg_709_);
v___x_780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_778_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15);
v___x_782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
lean_inc_ref(v_arg_690_);
v___x_783_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_head_725_, v_arg_710_, v_P_663_, v_arg_690_);
v___x_784_ = l_Lean_MessageData_ofExpr(v___x_783_);
v___x_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_782_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v___x_770_, v___x_785_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_dec_ref_known(v___x_786_, 1);
v___y_692_ = v___x_769_;
goto v___jp_691_;
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec_ref(v___x_769_);
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec(v_name_684_);
lean_del_object(v___x_681_);
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec(v_val_761_);
lean_dec_ref(v_h_u03c6_747_);
lean_dec_ref(v_00_u03c6_746_);
lean_del_object(v___x_738_);
lean_dec(v_head_725_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_709_);
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec_ref_known(v_p_683_, 2);
lean_dec(v_name_684_);
lean_del_object(v___x_681_);
lean_dec_ref(v_P_663_);
v_a_796_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_762_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_762_);
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
else
{
lean_object* v___x_805_; 
lean_dec(v_a_757_);
lean_dec_ref(v_h_u03c6_747_);
lean_dec_ref(v_00_u03c6_746_);
lean_del_object(v___x_738_);
lean_dec(v_snd_736_);
lean_dec(v_head_725_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_709_);
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec_ref_known(v_p_683_, 2);
lean_dec(v_name_684_);
lean_del_object(v___x_681_);
lean_dec_ref(v_P_663_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_732_);
v___x_805_ = v___x_759_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_732_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v_h_u03c6_747_);
lean_dec_ref(v_00_u03c6_746_);
lean_del_object(v___x_738_);
lean_dec(v_snd_736_);
lean_dec(v_head_725_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_709_);
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec_ref_known(v_p_683_, 2);
lean_dec(v_name_684_);
lean_del_object(v___x_681_);
lean_dec_ref(v_P_663_);
v_a_808_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_756_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_756_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_del_object(v___x_738_);
lean_dec(v_snd_736_);
lean_dec(v_fst_735_);
lean_dec(v_a_729_);
lean_dec(v_head_725_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_709_);
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec_ref_known(v_p_683_, 2);
lean_dec(v_name_684_);
lean_del_object(v___x_681_);
lean_dec_ref(v_P_663_);
v_a_823_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_743_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_743_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_846_; 
lean_dec(v_a_729_);
lean_dec(v_head_725_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_709_);
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec_ref_known(v_p_683_, 2);
lean_dec(v_name_684_);
lean_del_object(v___x_681_);
lean_dec_ref(v_P_663_);
v_a_832_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_846_ == 0)
{
v___x_834_ = v___x_733_;
v_isShared_835_ = v_isSharedCheck_846_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_733_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_846_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
uint8_t v___y_837_; uint8_t v___x_844_; 
v___x_844_ = l_Lean_Exception_isInterrupt(v_a_832_);
if (v___x_844_ == 0)
{
uint8_t v___x_845_; 
lean_inc(v_a_832_);
v___x_845_ = l_Lean_Exception_isRuntime(v_a_832_);
v___y_837_ = v___x_845_;
goto v___jp_836_;
}
else
{
v___y_837_ = v___x_844_;
goto v___jp_836_;
}
v___jp_836_:
{
if (v___y_837_ == 0)
{
lean_object* v___x_839_; 
lean_dec(v_a_832_);
if (v_isShared_835_ == 0)
{
lean_ctor_set_tag(v___x_834_, 0);
lean_ctor_set(v___x_834_, 0, v___x_732_);
v___x_839_ = v___x_834_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_732_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
else
{
lean_object* v___x_842_; 
if (v_isShared_835_ == 0)
{
v___x_842_ = v___x_834_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_832_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec(v_head_725_);
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_709_);
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec(v_name_684_);
lean_dec_ref_known(v_p_683_, 2);
lean_del_object(v___x_681_);
lean_dec(v_arg_665_);
lean_dec_ref(v_P_663_);
v_a_847_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_728_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_728_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
else
{
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_709_);
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec(v_name_684_);
lean_dec_ref_known(v_p_683_, 2);
lean_del_object(v___x_681_);
lean_dec(v_arg_665_);
lean_dec_ref(v_P_663_);
goto v___jp_675_;
}
}
else
{
lean_dec_ref(v_arg_710_);
lean_dec_ref(v_arg_709_);
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec(v_name_684_);
lean_dec_ref_known(v_p_683_, 2);
lean_del_object(v___x_681_);
lean_dec(v_arg_665_);
lean_dec_ref(v_P_663_);
goto v___jp_675_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec(v_name_684_);
lean_dec_ref_known(v_p_683_, 2);
lean_del_object(v___x_681_);
lean_dec(v_arg_665_);
lean_dec_ref(v_P_663_);
goto v___jp_675_;
}
}
else
{
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec(v_name_684_);
lean_dec_ref_known(v_p_683_, 2);
lean_del_object(v___x_681_);
lean_dec(v_arg_665_);
lean_dec_ref(v_P_663_);
goto v___jp_675_;
}
}
else
{
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec(v_name_684_);
lean_dec_ref_known(v_p_683_, 2);
lean_del_object(v___x_681_);
lean_dec(v_arg_665_);
lean_dec_ref(v_P_663_);
goto v___jp_675_;
}
}
else
{
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec(v_name_684_);
lean_dec_ref_known(v_p_683_, 2);
lean_del_object(v___x_681_);
lean_dec(v_arg_665_);
lean_dec_ref(v_P_663_);
goto v___jp_675_;
}
}
else
{
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec(v_name_684_);
lean_dec_ref_known(v_p_683_, 2);
lean_del_object(v___x_681_);
lean_dec(v_arg_665_);
lean_dec_ref(v_P_663_);
goto v___jp_675_;
}
}
else
{
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec(v_name_684_);
lean_dec_ref_known(v_p_683_, 2);
lean_del_object(v___x_681_);
lean_dec(v_arg_665_);
lean_dec_ref(v_P_663_);
goto v___jp_675_;
}
}
else
{
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec(v_name_684_);
lean_dec_ref_known(v_p_683_, 2);
lean_del_object(v___x_681_);
lean_dec(v_arg_665_);
lean_dec_ref(v_P_663_);
goto v___jp_675_;
}
}
else
{
lean_dec_ref(v_arg_690_);
lean_del_object(v___x_687_);
lean_dec(v_uniq_685_);
lean_dec(v_name_684_);
lean_dec_ref_known(v_p_683_, 2);
lean_del_object(v___x_681_);
lean_dec(v_arg_665_);
lean_dec_ref(v_P_663_);
goto v___jp_675_;
}
v___jp_691_:
{
lean_object* v___x_694_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 2, v_arg_690_);
v___x_694_ = v___x_687_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_name_684_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_uniq_685_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_arg_690_);
v___x_694_ = v_reuseFailAlloc_701_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_695_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_694_);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v___y_692_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_696_);
v___x_698_ = v___x_681_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_700_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; 
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_683_);
lean_del_object(v___x_681_);
lean_dec(v_val_679_);
lean_dec(v_arg_665_);
lean_dec_ref(v_P_663_);
goto v___jp_675_;
}
}
}
else
{
lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec(v___x_678_);
lean_dec(v_arg_665_);
lean_dec_ref(v_P_663_);
v___x_858_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18);
v___x_859_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(v___x_858_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
return v___x_859_;
}
v___jp_675_:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_box(0);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___boxed(lean_object* v_P_860_, lean_object* v_QR_861_, lean_object* v_arg_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(v_P_860_, v_QR_861_, v_arg_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
lean_dec(v_a_870_);
lean_dec_ref(v_a_869_);
lean_dec(v_a_868_);
lean_dec_ref(v_a_867_);
lean_dec(v_a_866_);
lean_dec_ref(v_a_865_);
lean_dec(v_a_864_);
lean_dec_ref(v_a_863_);
return v_res_872_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__2));
v___x_883_ = l_Lean_stringToMessageData(v___x_882_);
return v___x_883_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_886_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__5));
v___x_887_ = lean_unsigned_to_nat(36u);
v___x_888_ = lean_unsigned_to_nat(73u);
v___x_889_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__4));
v___x_890_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15));
v___x_891_ = l_mkPanicMessageWithDecl(v___x_890_, v___x_889_, v___x_888_, v___x_887_, v___x_886_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(lean_object* v_P_892_, lean_object* v_00_u03a8_893_, lean_object* v_arg_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_00_u03a8_893_);
if (lean_obj_tag(v___x_907_) == 1)
{
lean_object* v_val_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_1043_; 
v_val_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_1043_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_val_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_1043_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v_p_912_; 
v_p_912_ = lean_ctor_get(v_val_908_, 2);
lean_inc_ref(v_p_912_);
if (lean_obj_tag(v_p_912_) == 5)
{
lean_object* v_fn_913_; 
v_fn_913_ = lean_ctor_get(v_p_912_, 0);
if (lean_obj_tag(v_fn_913_) == 5)
{
lean_object* v_fn_914_; 
v_fn_914_ = lean_ctor_get(v_fn_913_, 0);
if (lean_obj_tag(v_fn_914_) == 5)
{
lean_object* v_fn_915_; 
v_fn_915_ = lean_ctor_get(v_fn_914_, 0);
if (lean_obj_tag(v_fn_915_) == 4)
{
lean_object* v_declName_916_; 
v_declName_916_ = lean_ctor_get(v_fn_915_, 0);
if (lean_obj_tag(v_declName_916_) == 1)
{
lean_object* v_pre_917_; 
v_pre_917_ = lean_ctor_get(v_declName_916_, 0);
if (lean_obj_tag(v_pre_917_) == 1)
{
lean_object* v_pre_918_; 
v_pre_918_ = lean_ctor_get(v_pre_917_, 0);
if (lean_obj_tag(v_pre_918_) == 1)
{
lean_object* v_pre_919_; 
v_pre_919_ = lean_ctor_get(v_pre_918_, 0);
if (lean_obj_tag(v_pre_919_) == 1)
{
lean_object* v_pre_920_; 
v_pre_920_ = lean_ctor_get(v_pre_919_, 0);
if (lean_obj_tag(v_pre_920_) == 0)
{
lean_object* v_name_921_; lean_object* v_uniq_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_1041_; 
v_name_921_ = lean_ctor_get(v_val_908_, 0);
v_uniq_922_ = lean_ctor_get(v_val_908_, 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_val_908_);
if (v_isSharedCheck_1041_ == 0)
{
lean_object* v_unused_1042_; 
v_unused_1042_ = lean_ctor_get(v_val_908_, 2);
lean_dec(v_unused_1042_);
v___x_924_ = v_val_908_;
v_isShared_925_ = v_isSharedCheck_1041_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_uniq_922_);
lean_inc(v_name_921_);
lean_dec(v_val_908_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_1041_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v_arg_926_; lean_object* v_arg_927_; lean_object* v_arg_928_; lean_object* v_us_929_; lean_object* v_str_930_; lean_object* v_str_931_; lean_object* v_str_932_; lean_object* v_str_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v_arg_926_ = lean_ctor_get(v_p_912_, 1);
v_arg_927_ = lean_ctor_get(v_fn_913_, 1);
lean_inc_ref(v_arg_927_);
v_arg_928_ = lean_ctor_get(v_fn_914_, 1);
v_us_929_ = lean_ctor_get(v_fn_915_, 1);
v_str_930_ = lean_ctor_get(v_declName_916_, 1);
v_str_931_ = lean_ctor_get(v_pre_917_, 1);
v_str_932_ = lean_ctor_get(v_pre_918_, 1);
v_str_933_ = lean_ctor_get(v_pre_919_, 1);
v___x_934_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_935_ = lean_string_dec_eq(v_str_933_, v___x_934_);
if (v___x_935_ == 0)
{
lean_dec_ref(v_arg_927_);
lean_del_object(v___x_924_);
lean_dec(v_uniq_922_);
lean_dec(v_name_921_);
lean_dec_ref_known(v_p_912_, 2);
lean_del_object(v___x_910_);
lean_dec(v_arg_894_);
lean_dec_ref(v_P_892_);
goto v___jp_904_;
}
else
{
lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_936_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_937_ = lean_string_dec_eq(v_str_932_, v___x_936_);
if (v___x_937_ == 0)
{
lean_dec_ref(v_arg_927_);
lean_del_object(v___x_924_);
lean_dec(v_uniq_922_);
lean_dec(v_name_921_);
lean_dec_ref_known(v_p_912_, 2);
lean_del_object(v___x_910_);
lean_dec(v_arg_894_);
lean_dec_ref(v_P_892_);
goto v___jp_904_;
}
else
{
lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_938_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_939_ = lean_string_dec_eq(v_str_931_, v___x_938_);
if (v___x_939_ == 0)
{
lean_dec_ref(v_arg_927_);
lean_del_object(v___x_924_);
lean_dec(v_uniq_922_);
lean_dec(v_name_921_);
lean_dec_ref_known(v_p_912_, 2);
lean_del_object(v___x_910_);
lean_dec(v_arg_894_);
lean_dec_ref(v_P_892_);
goto v___jp_904_;
}
else
{
lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_940_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__0));
v___x_941_ = lean_string_dec_eq(v_str_930_, v___x_940_);
if (v___x_941_ == 0)
{
lean_dec_ref(v_arg_927_);
lean_del_object(v___x_924_);
lean_dec(v_uniq_922_);
lean_dec(v_name_921_);
lean_dec_ref_known(v_p_912_, 2);
lean_del_object(v___x_910_);
lean_dec(v_arg_894_);
lean_dec_ref(v_P_892_);
goto v___jp_904_;
}
else
{
if (lean_obj_tag(v_us_929_) == 1)
{
lean_object* v_tail_942_; 
v_tail_942_ = lean_ctor_get(v_us_929_, 1);
lean_inc(v_tail_942_);
if (lean_obj_tag(v_tail_942_) == 1)
{
lean_object* v_tail_943_; 
v_tail_943_ = lean_ctor_get(v_tail_942_, 1);
if (lean_obj_tag(v_tail_943_) == 0)
{
lean_object* v_head_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_1039_; 
v_head_944_ = lean_ctor_get(v_tail_942_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_tail_942_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; 
v_unused_1040_ = lean_ctor_get(v_tail_942_, 1);
lean_dec(v_unused_1040_);
v___x_946_ = v_tail_942_;
v_isShared_947_ = v_isSharedCheck_1039_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_head_944_);
lean_dec(v_tail_942_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_1039_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
lean_inc_ref(v_arg_928_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v_arg_928_);
v___x_949_ = v___x_910_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_arg_928_);
v___x_949_ = v_reuseFailAlloc_1038_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_950_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2));
v___x_951_ = lean_box(0);
v___x_952_ = l_Lean_Elab_Tactic_elabTermWithHoles(v_arg_894_, v___x_949_, v___x_950_, v___x_941_, v___x_951_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v_fst_954_; lean_object* v_snd_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_1022_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_952_, 1);
v_fst_954_ = lean_ctor_get(v_a_953_, 0);
v_snd_955_ = lean_ctor_get(v_a_953_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_a_953_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_957_ = v_a_953_;
v_isShared_958_ = v_isSharedCheck_1022_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_snd_955_);
lean_inc(v_fst_954_);
lean_dec(v_a_953_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_1022_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_Elab_Tactic_pushGoals___redArg(v_snd_955_, v_a_896_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_1012_; 
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v___x_959_, 0);
lean_dec(v_unused_1013_);
v___x_961_ = v___x_959_;
v_isShared_962_ = v_isSharedCheck_1012_;
goto v_resetjp_960_;
}
else
{
lean_dec(v___x_959_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_1012_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v_toCold_963_; lean_object* v_options_964_; lean_object* v_inheritedTraceOptions_965_; uint8_t v_hasTrace_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v_toCold_963_ = lean_ctor_get(v_a_901_, 0);
v_options_964_ = lean_ctor_get(v_toCold_963_, 2);
v_inheritedTraceOptions_965_ = lean_ctor_get(v_toCold_963_, 11);
v_hasTrace_966_ = lean_ctor_get_uint8(v_options_964_, sizeof(void*)*1);
v___x_967_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1));
lean_inc_ref(v_us_929_);
v___x_968_ = l_Lean_mkConst(v___x_967_, v_us_929_);
lean_inc_n(v_fst_954_, 2);
lean_inc_ref(v_P_892_);
lean_inc_ref_n(v_arg_926_, 2);
lean_inc_ref(v_arg_927_);
lean_inc_ref(v_arg_928_);
v___x_969_ = l_Lean_mkApp5(v___x_968_, v_arg_928_, v_arg_927_, v_arg_926_, v_P_892_, v_fst_954_);
v___x_970_ = lean_unsigned_to_nat(1u);
v___x_971_ = lean_mk_empty_array_with_capacity(v___x_970_);
v___x_972_ = lean_array_push(v___x_971_, v_fst_954_);
v___x_973_ = l_Lean_Expr_beta(v_arg_926_, v___x_972_);
if (v_hasTrace_966_ == 0)
{
lean_dec(v_fst_954_);
lean_del_object(v___x_946_);
lean_dec(v_head_944_);
lean_dec_ref(v_arg_927_);
lean_dec_ref_known(v_p_912_, 2);
lean_dec_ref(v_P_892_);
goto v___jp_974_;
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_986_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_987_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11);
v___x_988_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_965_, v_options_964_, v___x_987_);
if (v___x_988_ == 0)
{
lean_dec(v_fst_954_);
lean_del_object(v___x_946_);
lean_dec(v_head_944_);
lean_dec_ref(v_arg_927_);
lean_dec_ref_known(v_p_912_, 2);
lean_dec_ref(v_P_892_);
goto v___jp_974_;
}
else
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_989_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3);
v___x_990_ = l_Lean_MessageData_ofExpr(v_p_912_);
if (v_isShared_947_ == 0)
{
lean_ctor_set_tag(v___x_946_, 7);
lean_ctor_set(v___x_946_, 1, v___x_990_);
lean_ctor_set(v___x_946_, 0, v___x_989_);
v___x_992_ = v___x_946_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v___x_990_);
v___x_992_ = v_reuseFailAlloc_1011_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_993_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = l_Lean_MessageData_ofExpr(v_fst_954_);
v___x_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_994_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15);
v___x_998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
lean_inc_ref(v___x_973_);
v___x_999_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_head_944_, v_arg_927_, v_P_892_, v___x_973_);
v___x_1000_ = l_Lean_MessageData_ofExpr(v___x_999_);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_998_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v___x_986_, v___x_1001_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_dec_ref_known(v___x_1002_, 1);
goto v___jp_974_;
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref(v___x_973_);
lean_dec_ref(v___x_969_);
lean_del_object(v___x_961_);
lean_del_object(v___x_957_);
lean_del_object(v___x_924_);
lean_dec(v_uniq_922_);
lean_dec(v_name_921_);
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
}
v___jp_974_:
{
lean_object* v___x_976_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 2, v___x_973_);
v___x_976_ = v___x_924_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_name_921_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_uniq_922_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v___x_973_);
v___x_976_ = v_reuseFailAlloc_985_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_977_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_976_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v___x_969_);
lean_ctor_set(v___x_957_, 0, v___x_977_);
v___x_979_ = v___x_957_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v___x_969_);
v___x_979_ = v_reuseFailAlloc_984_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_980_);
v___x_982_ = v___x_961_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_del_object(v___x_957_);
lean_dec(v_fst_954_);
lean_del_object(v___x_946_);
lean_dec(v_head_944_);
lean_dec_ref(v_arg_927_);
lean_del_object(v___x_924_);
lean_dec(v_uniq_922_);
lean_dec(v_name_921_);
lean_dec_ref_known(v_p_912_, 2);
lean_dec_ref(v_P_892_);
v_a_1014_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_959_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_959_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1037_; 
lean_del_object(v___x_946_);
lean_dec(v_head_944_);
lean_dec_ref(v_arg_927_);
lean_del_object(v___x_924_);
lean_dec(v_uniq_922_);
lean_dec(v_name_921_);
lean_dec_ref_known(v_p_912_, 2);
lean_dec_ref(v_P_892_);
v_a_1023_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1025_ = v___x_952_;
v_isShared_1026_ = v_isSharedCheck_1037_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_952_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1037_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
uint8_t v___y_1028_; uint8_t v___x_1035_; 
v___x_1035_ = l_Lean_Exception_isInterrupt(v_a_1023_);
if (v___x_1035_ == 0)
{
uint8_t v___x_1036_; 
lean_inc(v_a_1023_);
v___x_1036_ = l_Lean_Exception_isRuntime(v_a_1023_);
v___y_1028_ = v___x_1036_;
goto v___jp_1027_;
}
else
{
v___y_1028_ = v___x_1035_;
goto v___jp_1027_;
}
v___jp_1027_:
{
if (v___y_1028_ == 0)
{
lean_object* v___x_1030_; 
lean_dec(v_a_1023_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set_tag(v___x_1025_, 0);
lean_ctor_set(v___x_1025_, 0, v___x_951_);
v___x_1030_ = v___x_1025_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_951_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
else
{
lean_object* v___x_1033_; 
if (v_isShared_1026_ == 0)
{
v___x_1033_ = v___x_1025_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1023_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
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
lean_dec_ref_known(v_tail_942_, 2);
lean_dec_ref(v_arg_927_);
lean_del_object(v___x_924_);
lean_dec(v_uniq_922_);
lean_dec(v_name_921_);
lean_dec_ref_known(v_p_912_, 2);
lean_del_object(v___x_910_);
lean_dec(v_arg_894_);
lean_dec_ref(v_P_892_);
goto v___jp_904_;
}
}
else
{
lean_dec(v_tail_942_);
lean_dec_ref(v_arg_927_);
lean_del_object(v___x_924_);
lean_dec(v_uniq_922_);
lean_dec(v_name_921_);
lean_dec_ref_known(v_p_912_, 2);
lean_del_object(v___x_910_);
lean_dec(v_arg_894_);
lean_dec_ref(v_P_892_);
goto v___jp_904_;
}
}
else
{
lean_dec_ref(v_arg_927_);
lean_del_object(v___x_924_);
lean_dec(v_uniq_922_);
lean_dec(v_name_921_);
lean_dec_ref_known(v_p_912_, 2);
lean_del_object(v___x_910_);
lean_dec(v_arg_894_);
lean_dec_ref(v_P_892_);
goto v___jp_904_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_p_912_, 2);
lean_del_object(v___x_910_);
lean_dec(v_val_908_);
lean_dec(v_arg_894_);
lean_dec_ref(v_P_892_);
goto v___jp_904_;
}
}
else
{
lean_dec_ref_known(v_p_912_, 2);
lean_del_object(v___x_910_);
lean_dec(v_val_908_);
lean_dec(v_arg_894_);
lean_dec_ref(v_P_892_);
goto v___jp_904_;
}
}
else
{
lean_dec_ref_known(v_p_912_, 2);
lean_del_object(v___x_910_);
lean_dec(v_val_908_);
lean_dec(v_arg_894_);
lean_dec_ref(v_P_892_);
goto v___jp_904_;
}
}
else
{
lean_dec_ref_known(v_p_912_, 2);
lean_del_object(v___x_910_);
lean_dec(v_val_908_);
lean_dec(v_arg_894_);
lean_dec_ref(v_P_892_);
goto v___jp_904_;
}
}
else
{
lean_dec_ref_known(v_p_912_, 2);
lean_del_object(v___x_910_);
lean_dec(v_val_908_);
lean_dec(v_arg_894_);
lean_dec_ref(v_P_892_);
goto v___jp_904_;
}
}
else
{
lean_dec_ref_known(v_p_912_, 2);
lean_del_object(v___x_910_);
lean_dec(v_val_908_);
lean_dec(v_arg_894_);
lean_dec_ref(v_P_892_);
goto v___jp_904_;
}
}
else
{
lean_dec_ref_known(v_p_912_, 2);
lean_del_object(v___x_910_);
lean_dec(v_val_908_);
lean_dec(v_arg_894_);
lean_dec_ref(v_P_892_);
goto v___jp_904_;
}
}
else
{
lean_dec_ref_known(v_p_912_, 2);
lean_del_object(v___x_910_);
lean_dec(v_val_908_);
lean_dec(v_arg_894_);
lean_dec_ref(v_P_892_);
goto v___jp_904_;
}
}
else
{
lean_dec_ref(v_p_912_);
lean_del_object(v___x_910_);
lean_dec(v_val_908_);
lean_dec(v_arg_894_);
lean_dec_ref(v_P_892_);
goto v___jp_904_;
}
}
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_dec(v___x_907_);
lean_dec(v_arg_894_);
lean_dec_ref(v_P_892_);
v___x_1044_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6);
v___x_1045_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(v___x_1044_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
return v___x_1045_;
}
v___jp_904_:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_box(0);
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
return v___x_906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___boxed(lean_object* v_P_1046_, lean_object* v_00_u03a8_1047_, lean_object* v_arg_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(v_P_1046_, v_00_u03a8_1047_, v_arg_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
return v_res_1058_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1059_ = lean_box(0);
v___x_1060_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v___x_1059_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg(){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0);
v___x_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___boxed(lean_object* v___y_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0(lean_object* v_00_u03b1_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___boxed(lean_object* v_00_u03b1_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0(v_00_u03b1_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(lean_object* v_msg_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___f_1100_; lean_object* v___x_5040__overap_1101_; lean_object* v___x_1102_; 
v___f_1100_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3___closed__0));
v___x_5040__overap_1101_ = lean_panic_fn_borrowed(v___f_1100_, v_msg_1090_);
lean_inc(v___y_1098_);
lean_inc_ref(v___y_1097_);
lean_inc(v___y_1096_);
lean_inc_ref(v___y_1095_);
lean_inc(v___y_1094_);
lean_inc_ref(v___y_1093_);
lean_inc(v___y_1092_);
lean_inc_ref(v___y_1091_);
v___x_1102_ = lean_apply_9(v___x_5040__overap_1101_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, lean_box(0));
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3___boxed(lean_object* v_msg_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(v_msg_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0(lean_object* v_x_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v___x_1124_; 
lean_inc(v___y_1118_);
lean_inc_ref(v___y_1117_);
lean_inc(v___y_1116_);
lean_inc_ref(v___y_1115_);
v___x_1124_ = lean_apply_9(v_x_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, lean_box(0));
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0___boxed(lean_object* v_x_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0(v_x_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(lean_object* v_mvarId_1136_, lean_object* v_x_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v___f_1147_; lean_object* v___x_1148_; 
lean_inc(v___y_1141_);
lean_inc_ref(v___y_1140_);
lean_inc(v___y_1139_);
lean_inc_ref(v___y_1138_);
v___f_1147_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1147_, 0, v_x_1137_);
lean_closure_set(v___f_1147_, 1, v___y_1138_);
lean_closure_set(v___f_1147_, 2, v___y_1139_);
lean_closure_set(v___f_1147_, 3, v___y_1140_);
lean_closure_set(v___f_1147_, 4, v___y_1141_);
v___x_1148_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1136_, v___f_1147_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
if (lean_obj_tag(v___x_1148_) == 0)
{
return v___x_1148_;
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1148_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___boxed(lean_object* v_mvarId_1157_, lean_object* v_x_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_mvarId_1157_, v_x_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4(lean_object* v_00_u03b1_1169_, lean_object* v_mvarId_1170_, lean_object* v_x_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_mvarId_1170_, v_x_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___boxed(lean_object* v_00_u03b1_1182_, lean_object* v_mvarId_1183_, lean_object* v_x_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4(v_00_u03b1_1182_, v_mvarId_1183_, v_x_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0(lean_object* v___x_1197_, lean_object* v___x_1198_, lean_object* v___x_1199_, lean_object* v___x_1200_, lean_object* v___x_1201_, lean_object* v___x_1202_, lean_object* v___x_1203_, lean_object* v_fst_1204_, lean_object* v_fst_1205_, lean_object* v___x_1206_, lean_object* v_snd_1207_, lean_object* v_snd_1208_, lean_object* v_hgoal_1209_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1210_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__0));
v___x_1211_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__1));
v___x_1212_ = l_Lean_Name_mkStr5(v___x_1197_, v___x_1198_, v___x_1199_, v___x_1210_, v___x_1211_);
v___x_1213_ = l_Lean_mkConst(v___x_1212_, v___x_1200_);
lean_inc_ref(v___x_1203_);
lean_inc_ref_n(v___x_1202_, 2);
lean_inc(v___x_1201_);
v___x_1214_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v___x_1201_, v___x_1202_, v___x_1203_, v_fst_1204_);
v___x_1215_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v___x_1201_, v___x_1202_, v___x_1203_, v_fst_1205_);
v___x_1216_ = l_Lean_mkApp6(v___x_1213_, v___x_1202_, v___x_1214_, v___x_1215_, v___x_1206_, v_snd_1207_, v_hgoal_1209_);
v___x_1217_ = lean_apply_1(v_snd_1208_, v___x_1216_);
return v___x_1217_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__0));
v___x_1220_ = l_Lean_stringToMessageData(v___x_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1(lean_object* v___x_1221_, lean_object* v___x_1222_, lean_object* v___x_1223_, lean_object* v___x_1224_, lean_object* v___x_1225_, lean_object* v_as_1226_, size_t v_sz_1227_, size_t v_i_1228_, lean_object* v_b_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_a_1240_; uint8_t v___x_1244_; 
v___x_1244_ = lean_usize_dec_lt(v_i_1228_, v_sz_1227_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; 
lean_dec_ref(v___x_1225_);
lean_dec_ref(v___x_1224_);
lean_dec_ref(v___x_1223_);
lean_dec(v___x_1222_);
lean_dec(v___x_1221_);
v___x_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1245_, 0, v_b_1229_);
return v___x_1245_;
}
else
{
lean_object* v_fst_1246_; lean_object* v_snd_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1301_; 
v_fst_1246_ = lean_ctor_get(v_b_1229_, 0);
v_snd_1247_ = lean_ctor_get(v_b_1229_, 1);
v_isSharedCheck_1301_ = !lean_is_exclusive(v_b_1229_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1249_ = v_b_1229_;
v_isShared_1250_ = v_isSharedCheck_1301_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_snd_1247_);
lean_inc(v_fst_1246_);
lean_dec(v_b_1229_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1301_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v_a_1254_; lean_object* v___y_1256_; lean_object* v___x_1296_; 
v___x_1251_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_1252_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1253_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v_a_1254_ = lean_array_uget_borrowed(v_as_1226_, v_i_1228_);
lean_inc(v_a_1254_);
lean_inc(v_fst_1246_);
lean_inc_ref(v___x_1224_);
v___x_1296_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(v___x_1224_, v_fst_1246_, v_a_1254_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
if (lean_obj_tag(v_a_1297_) == 0)
{
lean_object* v___x_1298_; 
lean_dec_ref_known(v___x_1296_, 1);
lean_inc(v_a_1254_);
lean_inc(v_fst_1246_);
lean_inc_ref(v___x_1224_);
v___x_1298_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(v___x_1224_, v_fst_1246_, v_a_1254_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1299_);
if (lean_obj_tag(v_a_1299_) == 0)
{
lean_object* v___x_1300_; 
lean_dec_ref_known(v___x_1298_, 1);
lean_inc(v_a_1254_);
lean_inc(v_fst_1246_);
lean_inc_ref(v___x_1224_);
v___x_1300_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(v___x_1224_, v_fst_1246_, v_a_1254_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
v___y_1256_ = v___x_1300_;
goto v___jp_1255_;
}
else
{
lean_dec_ref_known(v_a_1299_, 1);
v___y_1256_ = v___x_1298_;
goto v___jp_1255_;
}
}
else
{
v___y_1256_ = v___x_1298_;
goto v___jp_1255_;
}
}
else
{
lean_dec_ref_known(v_a_1297_, 1);
v___y_1256_ = v___x_1296_;
goto v___jp_1255_;
}
}
else
{
v___y_1256_ = v___x_1296_;
goto v___jp_1255_;
}
v___jp_1255_:
{
if (lean_obj_tag(v___y_1256_) == 0)
{
lean_object* v_a_1257_; 
v_a_1257_ = lean_ctor_get(v___y_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___y_1256_, 1);
if (lean_obj_tag(v_a_1257_) == 0)
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1258_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1);
lean_inc(v_fst_1246_);
v___x_1259_ = l_Lean_MessageData_ofExpr(v_fst_1246_);
v___x_1260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1258_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_1262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
lean_inc(v_a_1254_);
v___x_1263_ = l_Lean_MessageData_ofSyntax(v_a_1254_);
v___x_1264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_1264_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v___x_1267_; 
lean_dec_ref_known(v___x_1265_, 1);
if (v_isShared_1250_ == 0)
{
v___x_1267_ = v___x_1249_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_fst_1246_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_snd_1247_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
v_a_1240_ = v___x_1267_;
goto v___jp_1239_;
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_del_object(v___x_1249_);
lean_dec(v_snd_1247_);
lean_dec(v_fst_1246_);
lean_dec_ref(v___x_1225_);
lean_dec_ref(v___x_1224_);
lean_dec_ref(v___x_1223_);
lean_dec(v___x_1222_);
lean_dec(v___x_1221_);
v_a_1269_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1265_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1265_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
else
{
lean_object* v_val_1277_; lean_object* v_fst_1278_; lean_object* v_snd_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1287_; 
lean_del_object(v___x_1249_);
v_val_1277_ = lean_ctor_get(v_a_1257_, 0);
lean_inc(v_val_1277_);
lean_dec_ref_known(v_a_1257_, 1);
v_fst_1278_ = lean_ctor_get(v_val_1277_, 0);
v_snd_1279_ = lean_ctor_get(v_val_1277_, 1);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_val_1277_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1281_ = v_val_1277_;
v_isShared_1282_ = v_isSharedCheck_1287_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_snd_1279_);
lean_inc(v_fst_1278_);
lean_dec(v_val_1277_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1287_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___f_1283_; lean_object* v___x_1285_; 
lean_inc_ref(v___x_1225_);
lean_inc(v_fst_1278_);
lean_inc_ref(v___x_1224_);
lean_inc_ref(v___x_1223_);
lean_inc(v___x_1222_);
lean_inc(v___x_1221_);
v___f_1283_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0), 13, 12);
lean_closure_set(v___f_1283_, 0, v___x_1251_);
lean_closure_set(v___f_1283_, 1, v___x_1252_);
lean_closure_set(v___f_1283_, 2, v___x_1253_);
lean_closure_set(v___f_1283_, 3, v___x_1221_);
lean_closure_set(v___f_1283_, 4, v___x_1222_);
lean_closure_set(v___f_1283_, 5, v___x_1223_);
lean_closure_set(v___f_1283_, 6, v___x_1224_);
lean_closure_set(v___f_1283_, 7, v_fst_1246_);
lean_closure_set(v___f_1283_, 8, v_fst_1278_);
lean_closure_set(v___f_1283_, 9, v___x_1225_);
lean_closure_set(v___f_1283_, 10, v_snd_1279_);
lean_closure_set(v___f_1283_, 11, v_snd_1247_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v___f_1283_);
v___x_1285_ = v___x_1281_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_fst_1278_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v___f_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
v_a_1240_ = v___x_1285_;
goto v___jp_1239_;
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_del_object(v___x_1249_);
lean_dec(v_snd_1247_);
lean_dec(v_fst_1246_);
lean_dec_ref(v___x_1225_);
lean_dec_ref(v___x_1224_);
lean_dec_ref(v___x_1223_);
lean_dec(v___x_1222_);
lean_dec(v___x_1221_);
v_a_1288_ = lean_ctor_get(v___y_1256_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___y_1256_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___y_1256_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___y_1256_);
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
}
v___jp_1239_:
{
size_t v___x_1241_; size_t v___x_1242_; 
v___x_1241_ = ((size_t)1ULL);
v___x_1242_ = lean_usize_add(v_i_1228_, v___x_1241_);
v_i_1228_ = v___x_1242_;
v_b_1229_ = v_a_1240_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___boxed(lean_object** _args){
lean_object* v___x_1302_ = _args[0];
lean_object* v___x_1303_ = _args[1];
lean_object* v___x_1304_ = _args[2];
lean_object* v___x_1305_ = _args[3];
lean_object* v___x_1306_ = _args[4];
lean_object* v_as_1307_ = _args[5];
lean_object* v_sz_1308_ = _args[6];
lean_object* v_i_1309_ = _args[7];
lean_object* v_b_1310_ = _args[8];
lean_object* v___y_1311_ = _args[9];
lean_object* v___y_1312_ = _args[10];
lean_object* v___y_1313_ = _args[11];
lean_object* v___y_1314_ = _args[12];
lean_object* v___y_1315_ = _args[13];
lean_object* v___y_1316_ = _args[14];
lean_object* v___y_1317_ = _args[15];
lean_object* v___y_1318_ = _args[16];
lean_object* v___y_1319_ = _args[17];
_start:
{
size_t v_sz_boxed_1320_; size_t v_i_boxed_1321_; lean_object* v_res_1322_; 
v_sz_boxed_1320_ = lean_unbox_usize(v_sz_1308_);
lean_dec(v_sz_1308_);
v_i_boxed_1321_ = lean_unbox_usize(v_i_1309_);
lean_dec(v_i_1309_);
v_res_1322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1(v___x_1302_, v___x_1303_, v___x_1304_, v___x_1305_, v___x_1306_, v_as_1307_, v_sz_boxed_1320_, v_i_boxed_1321_, v_b_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec_ref(v_as_1307_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7___redArg(lean_object* v_x_1323_, lean_object* v_x_1324_, lean_object* v_x_1325_, lean_object* v_x_1326_){
_start:
{
lean_object* v_ks_1327_; lean_object* v_vs_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1352_; 
v_ks_1327_ = lean_ctor_get(v_x_1323_, 0);
v_vs_1328_ = lean_ctor_get(v_x_1323_, 1);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_x_1323_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1330_ = v_x_1323_;
v_isShared_1331_ = v_isSharedCheck_1352_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_vs_1328_);
lean_inc(v_ks_1327_);
lean_dec(v_x_1323_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1352_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1332_ = lean_array_get_size(v_ks_1327_);
v___x_1333_ = lean_nat_dec_lt(v_x_1324_, v___x_1332_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
lean_dec(v_x_1324_);
v___x_1334_ = lean_array_push(v_ks_1327_, v_x_1325_);
v___x_1335_ = lean_array_push(v_vs_1328_, v_x_1326_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 1, v___x_1335_);
lean_ctor_set(v___x_1330_, 0, v___x_1334_);
v___x_1337_ = v___x_1330_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
else
{
lean_object* v_k_x27_1339_; uint8_t v___x_1340_; 
v_k_x27_1339_ = lean_array_fget_borrowed(v_ks_1327_, v_x_1324_);
v___x_1340_ = l_Lean_instBEqMVarId_beq(v_x_1325_, v_k_x27_1339_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1342_; 
if (v_isShared_1331_ == 0)
{
v___x_1342_ = v___x_1330_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_ks_1327_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_vs_1328_);
v___x_1342_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_unsigned_to_nat(1u);
v___x_1344_ = lean_nat_add(v_x_1324_, v___x_1343_);
lean_dec(v_x_1324_);
v_x_1323_ = v___x_1342_;
v_x_1324_ = v___x_1344_;
goto _start;
}
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1347_ = lean_array_fset(v_ks_1327_, v_x_1324_, v_x_1325_);
v___x_1348_ = lean_array_fset(v_vs_1328_, v_x_1324_, v_x_1326_);
lean_dec(v_x_1324_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 1, v___x_1348_);
lean_ctor_set(v___x_1330_, 0, v___x_1347_);
v___x_1350_ = v___x_1330_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1347_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6___redArg(lean_object* v_n_1353_, lean_object* v_k_1354_, lean_object* v_v_1355_){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_unsigned_to_nat(0u);
v___x_1357_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7___redArg(v_n_1353_, v___x_1356_, v_k_1354_, v_v_1355_);
return v___x_1357_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(lean_object* v_x_1359_, size_t v_x_1360_, size_t v_x_1361_, lean_object* v_x_1362_, lean_object* v_x_1363_){
_start:
{
if (lean_obj_tag(v_x_1359_) == 0)
{
lean_object* v_es_1364_; size_t v___x_1365_; size_t v___x_1366_; lean_object* v_j_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v_es_1364_ = lean_ctor_get(v_x_1359_, 0);
v___x_1365_ = ((size_t)31ULL);
v___x_1366_ = lean_usize_land(v_x_1360_, v___x_1365_);
v_j_1367_ = lean_usize_to_nat(v___x_1366_);
v___x_1368_ = lean_array_get_size(v_es_1364_);
v___x_1369_ = lean_nat_dec_lt(v_j_1367_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_dec(v_j_1367_);
lean_dec(v_x_1363_);
lean_dec(v_x_1362_);
return v_x_1359_;
}
else
{
lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1408_; 
lean_inc_ref(v_es_1364_);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_x_1359_);
if (v_isSharedCheck_1408_ == 0)
{
lean_object* v_unused_1409_; 
v_unused_1409_ = lean_ctor_get(v_x_1359_, 0);
lean_dec(v_unused_1409_);
v___x_1371_ = v_x_1359_;
v_isShared_1372_ = v_isSharedCheck_1408_;
goto v_resetjp_1370_;
}
else
{
lean_dec(v_x_1359_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1408_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v_v_1373_; lean_object* v___x_1374_; lean_object* v_xs_x27_1375_; lean_object* v___y_1377_; 
v_v_1373_ = lean_array_fget(v_es_1364_, v_j_1367_);
v___x_1374_ = lean_box(0);
v_xs_x27_1375_ = lean_array_fset(v_es_1364_, v_j_1367_, v___x_1374_);
switch(lean_obj_tag(v_v_1373_))
{
case 0:
{
lean_object* v_key_1382_; lean_object* v_val_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1393_; 
v_key_1382_ = lean_ctor_get(v_v_1373_, 0);
v_val_1383_ = lean_ctor_get(v_v_1373_, 1);
v_isSharedCheck_1393_ = !lean_is_exclusive(v_v_1373_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1385_ = v_v_1373_;
v_isShared_1386_ = v_isSharedCheck_1393_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_val_1383_);
lean_inc(v_key_1382_);
lean_dec(v_v_1373_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1393_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
uint8_t v___x_1387_; 
v___x_1387_ = l_Lean_instBEqMVarId_beq(v_x_1362_, v_key_1382_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_del_object(v___x_1385_);
v___x_1388_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1382_, v_val_1383_, v_x_1362_, v_x_1363_);
v___x_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
v___y_1377_ = v___x_1389_;
goto v___jp_1376_;
}
else
{
lean_object* v___x_1391_; 
lean_dec(v_val_1383_);
lean_dec(v_key_1382_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 1, v_x_1363_);
lean_ctor_set(v___x_1385_, 0, v_x_1362_);
v___x_1391_ = v___x_1385_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_x_1362_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_x_1363_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
v___y_1377_ = v___x_1391_;
goto v___jp_1376_;
}
}
}
}
case 1:
{
lean_object* v_node_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1406_; 
v_node_1394_ = lean_ctor_get(v_v_1373_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v_v_1373_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1396_ = v_v_1373_;
v_isShared_1397_ = v_isSharedCheck_1406_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_node_1394_);
lean_dec(v_v_1373_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1406_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
size_t v___x_1398_; size_t v___x_1399_; size_t v___x_1400_; size_t v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1398_ = ((size_t)5ULL);
v___x_1399_ = lean_usize_shift_right(v_x_1360_, v___x_1398_);
v___x_1400_ = ((size_t)1ULL);
v___x_1401_ = lean_usize_add(v_x_1361_, v___x_1400_);
v___x_1402_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_node_1394_, v___x_1399_, v___x_1401_, v_x_1362_, v_x_1363_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v___x_1402_);
v___x_1404_ = v___x_1396_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
v___y_1377_ = v___x_1404_;
goto v___jp_1376_;
}
}
}
default: 
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v_x_1362_);
lean_ctor_set(v___x_1407_, 1, v_x_1363_);
v___y_1377_ = v___x_1407_;
goto v___jp_1376_;
}
}
v___jp_1376_:
{
lean_object* v___x_1378_; lean_object* v___x_1380_; 
v___x_1378_ = lean_array_fset(v_xs_x27_1375_, v_j_1367_, v___y_1377_);
lean_dec(v_j_1367_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1378_);
v___x_1380_ = v___x_1371_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
}
else
{
lean_object* v_ks_1410_; lean_object* v_vs_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1429_; 
v_ks_1410_ = lean_ctor_get(v_x_1359_, 0);
v_vs_1411_ = lean_ctor_get(v_x_1359_, 1);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_x_1359_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1413_ = v_x_1359_;
v_isShared_1414_ = v_isSharedCheck_1429_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_vs_1411_);
lean_inc(v_ks_1410_);
lean_dec(v_x_1359_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1429_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_ks_1410_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_vs_1411_);
v___x_1416_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v_newNode_1417_; size_t v___x_1418_; uint8_t v___x_1419_; 
v_newNode_1417_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6___redArg(v___x_1416_, v_x_1362_, v_x_1363_);
v___x_1418_ = ((size_t)7ULL);
v___x_1419_ = lean_usize_dec_le(v___x_1418_, v_x_1361_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1420_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1417_);
v___x_1421_ = lean_unsigned_to_nat(4u);
v___x_1422_ = lean_nat_dec_lt(v___x_1420_, v___x_1421_);
lean_dec(v___x_1420_);
if (v___x_1422_ == 0)
{
lean_object* v_ks_1423_; lean_object* v_vs_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v_ks_1423_ = lean_ctor_get(v_newNode_1417_, 0);
lean_inc_ref(v_ks_1423_);
v_vs_1424_ = lean_ctor_get(v_newNode_1417_, 1);
lean_inc_ref(v_vs_1424_);
lean_dec_ref(v_newNode_1417_);
v___x_1425_ = lean_unsigned_to_nat(0u);
v___x_1426_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0);
v___x_1427_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(v_x_1361_, v_ks_1423_, v_vs_1424_, v___x_1425_, v___x_1426_);
lean_dec_ref(v_vs_1424_);
lean_dec_ref(v_ks_1423_);
return v___x_1427_;
}
else
{
return v_newNode_1417_;
}
}
else
{
return v_newNode_1417_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(size_t v_depth_1430_, lean_object* v_keys_1431_, lean_object* v_vals_1432_, lean_object* v_i_1433_, lean_object* v_entries_1434_){
_start:
{
lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1435_ = lean_array_get_size(v_keys_1431_);
v___x_1436_ = lean_nat_dec_lt(v_i_1433_, v___x_1435_);
if (v___x_1436_ == 0)
{
lean_dec(v_i_1433_);
return v_entries_1434_;
}
else
{
lean_object* v_k_1437_; lean_object* v_v_1438_; uint64_t v___x_1439_; size_t v_h_1440_; size_t v___x_1441_; lean_object* v___x_1442_; size_t v___x_1443_; size_t v___x_1444_; size_t v___x_1445_; size_t v_h_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v_k_1437_ = lean_array_fget_borrowed(v_keys_1431_, v_i_1433_);
v_v_1438_ = lean_array_fget_borrowed(v_vals_1432_, v_i_1433_);
v___x_1439_ = l_Lean_instHashableMVarId_hash(v_k_1437_);
v_h_1440_ = lean_uint64_to_usize(v___x_1439_);
v___x_1441_ = ((size_t)5ULL);
v___x_1442_ = lean_unsigned_to_nat(1u);
v___x_1443_ = ((size_t)1ULL);
v___x_1444_ = lean_usize_sub(v_depth_1430_, v___x_1443_);
v___x_1445_ = lean_usize_mul(v___x_1441_, v___x_1444_);
v_h_1446_ = lean_usize_shift_right(v_h_1440_, v___x_1445_);
v___x_1447_ = lean_nat_add(v_i_1433_, v___x_1442_);
lean_dec(v_i_1433_);
lean_inc(v_v_1438_);
lean_inc(v_k_1437_);
v___x_1448_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_entries_1434_, v_h_1446_, v_depth_1430_, v_k_1437_, v_v_1438_);
v_i_1433_ = v___x_1447_;
v_entries_1434_ = v___x_1448_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_depth_1450_, lean_object* v_keys_1451_, lean_object* v_vals_1452_, lean_object* v_i_1453_, lean_object* v_entries_1454_){
_start:
{
size_t v_depth_boxed_1455_; lean_object* v_res_1456_; 
v_depth_boxed_1455_ = lean_unbox_usize(v_depth_1450_);
lean_dec(v_depth_1450_);
v_res_1456_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(v_depth_boxed_1455_, v_keys_1451_, v_vals_1452_, v_i_1453_, v_entries_1454_);
lean_dec_ref(v_vals_1452_);
lean_dec_ref(v_keys_1451_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_x_1457_, lean_object* v_x_1458_, lean_object* v_x_1459_, lean_object* v_x_1460_, lean_object* v_x_1461_){
_start:
{
size_t v_x_7372__boxed_1462_; size_t v_x_7373__boxed_1463_; lean_object* v_res_1464_; 
v_x_7372__boxed_1462_ = lean_unbox_usize(v_x_1458_);
lean_dec(v_x_1458_);
v_x_7373__boxed_1463_ = lean_unbox_usize(v_x_1459_);
lean_dec(v_x_1459_);
v_res_1464_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_x_1457_, v_x_7372__boxed_1462_, v_x_7373__boxed_1463_, v_x_1460_, v_x_1461_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2___redArg(lean_object* v_x_1465_, lean_object* v_x_1466_, lean_object* v_x_1467_){
_start:
{
uint64_t v___x_1468_; size_t v___x_1469_; size_t v___x_1470_; lean_object* v___x_1471_; 
v___x_1468_ = l_Lean_instHashableMVarId_hash(v_x_1466_);
v___x_1469_ = lean_uint64_to_usize(v___x_1468_);
v___x_1470_ = ((size_t)1ULL);
v___x_1471_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_x_1465_, v___x_1469_, v___x_1470_, v_x_1466_, v_x_1467_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(lean_object* v_mvarId_1472_, lean_object* v_val_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; lean_object* v_mctx_1477_; lean_object* v_cache_1478_; lean_object* v_zetaDeltaFVarIds_1479_; lean_object* v_postponed_1480_; lean_object* v_diag_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1510_; 
v___x_1476_ = lean_st_ref_take(v___y_1474_);
v_mctx_1477_ = lean_ctor_get(v___x_1476_, 0);
v_cache_1478_ = lean_ctor_get(v___x_1476_, 1);
v_zetaDeltaFVarIds_1479_ = lean_ctor_get(v___x_1476_, 2);
v_postponed_1480_ = lean_ctor_get(v___x_1476_, 3);
v_diag_1481_ = lean_ctor_get(v___x_1476_, 4);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1483_ = v___x_1476_;
v_isShared_1484_ = v_isSharedCheck_1510_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_diag_1481_);
lean_inc(v_postponed_1480_);
lean_inc(v_zetaDeltaFVarIds_1479_);
lean_inc(v_cache_1478_);
lean_inc(v_mctx_1477_);
lean_dec(v___x_1476_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1510_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v_depth_1485_; lean_object* v_levelAssignDepth_1486_; lean_object* v_lmvarCounter_1487_; lean_object* v_mvarCounter_1488_; lean_object* v_lDecls_1489_; lean_object* v_decls_1490_; lean_object* v_userNames_1491_; lean_object* v_lAssignment_1492_; lean_object* v_eAssignment_1493_; lean_object* v_dAssignment_1494_; lean_object* v_instanceTypedMVars_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1509_; 
v_depth_1485_ = lean_ctor_get(v_mctx_1477_, 0);
v_levelAssignDepth_1486_ = lean_ctor_get(v_mctx_1477_, 1);
v_lmvarCounter_1487_ = lean_ctor_get(v_mctx_1477_, 2);
v_mvarCounter_1488_ = lean_ctor_get(v_mctx_1477_, 3);
v_lDecls_1489_ = lean_ctor_get(v_mctx_1477_, 4);
v_decls_1490_ = lean_ctor_get(v_mctx_1477_, 5);
v_userNames_1491_ = lean_ctor_get(v_mctx_1477_, 6);
v_lAssignment_1492_ = lean_ctor_get(v_mctx_1477_, 7);
v_eAssignment_1493_ = lean_ctor_get(v_mctx_1477_, 8);
v_dAssignment_1494_ = lean_ctor_get(v_mctx_1477_, 9);
v_instanceTypedMVars_1495_ = lean_ctor_get(v_mctx_1477_, 10);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_mctx_1477_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1497_ = v_mctx_1477_;
v_isShared_1498_ = v_isSharedCheck_1509_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_instanceTypedMVars_1495_);
lean_inc(v_dAssignment_1494_);
lean_inc(v_eAssignment_1493_);
lean_inc(v_lAssignment_1492_);
lean_inc(v_userNames_1491_);
lean_inc(v_decls_1490_);
lean_inc(v_lDecls_1489_);
lean_inc(v_mvarCounter_1488_);
lean_inc(v_lmvarCounter_1487_);
lean_inc(v_levelAssignDepth_1486_);
lean_inc(v_depth_1485_);
lean_dec(v_mctx_1477_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1509_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; lean_object* v___x_1501_; 
v___x_1499_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2___redArg(v_eAssignment_1493_, v_mvarId_1472_, v_val_1473_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 8, v___x_1499_);
v___x_1501_ = v___x_1497_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_depth_1485_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_levelAssignDepth_1486_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_lmvarCounter_1487_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_mvarCounter_1488_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v_lDecls_1489_);
lean_ctor_set(v_reuseFailAlloc_1508_, 5, v_decls_1490_);
lean_ctor_set(v_reuseFailAlloc_1508_, 6, v_userNames_1491_);
lean_ctor_set(v_reuseFailAlloc_1508_, 7, v_lAssignment_1492_);
lean_ctor_set(v_reuseFailAlloc_1508_, 8, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1508_, 9, v_dAssignment_1494_);
lean_ctor_set(v_reuseFailAlloc_1508_, 10, v_instanceTypedMVars_1495_);
v___x_1501_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1503_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1501_);
v___x_1503_ = v___x_1483_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_cache_1478_);
lean_ctor_set(v_reuseFailAlloc_1507_, 2, v_zetaDeltaFVarIds_1479_);
lean_ctor_set(v_reuseFailAlloc_1507_, 3, v_postponed_1480_);
lean_ctor_set(v_reuseFailAlloc_1507_, 4, v_diag_1481_);
v___x_1503_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1504_ = lean_st_ref_put(v___y_1474_, v___x_1503_);
v___x_1505_ = lean_box(0);
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
return v___x_1506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg___boxed(lean_object* v_mvarId_1511_, lean_object* v_val_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_mvarId_1511_, v_val_1512_, v___y_1513_);
lean_dec(v___y_1513_);
return v_res_1515_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1519_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__2));
v___x_1520_ = lean_unsigned_to_nat(33u);
v___x_1521_ = lean_unsigned_to_nat(105u);
v___x_1522_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__1));
v___x_1523_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15));
v___x_1524_ = l_mkPanicMessageWithDecl(v___x_1523_, v___x_1522_, v___x_1521_, v___x_1520_, v___x_1519_);
return v___x_1524_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__4));
v___x_1527_ = l_Lean_stringToMessageData(v___x_1526_);
return v___x_1527_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__6));
v___x_1530_ = l_Lean_stringToMessageData(v___x_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0(lean_object* v___x_1531_, lean_object* v_snd_1532_, lean_object* v_hyp_1533_, lean_object* v___x_1534_, lean_object* v_args_1535_, lean_object* v_fst_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
if (lean_obj_tag(v___x_1531_) == 1)
{
lean_object* v_val_1546_; lean_object* v_focusHyp_1547_; lean_object* v_restHyps_1548_; lean_object* v_proof_1549_; lean_object* v___x_1550_; 
v_val_1546_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_val_1546_);
lean_dec_ref_known(v___x_1531_, 1);
v_focusHyp_1547_ = lean_ctor_get(v_val_1546_, 0);
lean_inc_ref_n(v_focusHyp_1547_, 2);
v_restHyps_1548_ = lean_ctor_get(v_val_1546_, 1);
lean_inc_ref(v_restHyps_1548_);
v_proof_1549_ = lean_ctor_get(v_val_1546_, 2);
lean_inc_ref(v_proof_1549_);
lean_dec(v_val_1546_);
v___x_1550_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_1547_);
if (lean_obj_tag(v___x_1550_) == 1)
{
lean_object* v_val_1551_; lean_object* v_u_1552_; lean_object* v_00_u03c3s_1553_; lean_object* v_hyps_1554_; lean_object* v_target_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1613_; 
v_val_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_val_1551_);
lean_dec_ref_known(v___x_1550_, 1);
v_u_1552_ = lean_ctor_get(v_snd_1532_, 0);
v_00_u03c3s_1553_ = lean_ctor_get(v_snd_1532_, 1);
v_hyps_1554_ = lean_ctor_get(v_snd_1532_, 2);
v_target_1555_ = lean_ctor_get(v_snd_1532_, 3);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_snd_1532_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1557_ = v_snd_1532_;
v_isShared_1558_ = v_isSharedCheck_1613_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_target_1555_);
lean_inc(v_hyps_1554_);
lean_inc(v_00_u03c3s_1553_);
lean_inc(v_u_1552_);
lean_dec(v_snd_1532_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1613_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
uint8_t v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = 0;
lean_inc_ref(v_00_u03c3s_1553_);
v___x_1560_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_hyp_1533_, v_00_u03c3s_1553_, v_val_1551_, v___x_1559_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; size_t v_sz_1572_; size_t v___x_1573_; lean_object* v___x_1574_; 
lean_dec_ref_known(v___x_1560_, 1);
v___x_1561_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_1562_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1563_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_1564_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1565_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__0));
v___x_1566_ = l_Lean_Name_mkStr6(v___x_1561_, v___x_1562_, v___x_1563_, v___x_1534_, v___x_1564_, v___x_1565_);
v___x_1567_ = lean_box(0);
lean_inc_n(v_u_1552_, 2);
v___x_1568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1568_, 0, v_u_1552_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
lean_inc_ref(v___x_1568_);
v___x_1569_ = l_Lean_mkConst(v___x_1566_, v___x_1568_);
lean_inc_ref_n(v_target_1555_, 2);
lean_inc_ref(v_focusHyp_1547_);
lean_inc_ref_n(v_restHyps_1548_, 2);
lean_inc_ref_n(v_00_u03c3s_1553_, 2);
v___x_1570_ = lean_alloc_closure((void*)(l_Lean_mkApp7), 8, 7);
lean_closure_set(v___x_1570_, 0, v___x_1569_);
lean_closure_set(v___x_1570_, 1, v_00_u03c3s_1553_);
lean_closure_set(v___x_1570_, 2, v_hyps_1554_);
lean_closure_set(v___x_1570_, 3, v_restHyps_1548_);
lean_closure_set(v___x_1570_, 4, v_focusHyp_1547_);
lean_closure_set(v___x_1570_, 5, v_target_1555_);
lean_closure_set(v___x_1570_, 6, v_proof_1549_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v_focusHyp_1547_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v_sz_1572_ = lean_array_size(v_args_1535_);
v___x_1573_ = ((size_t)0ULL);
v___x_1574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1(v___x_1568_, v_u_1552_, v_00_u03c3s_1553_, v_restHyps_1548_, v_target_1555_, v_args_1535_, v_sz_1572_, v___x_1573_, v___x_1571_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v_fst_1576_; lean_object* v_snd_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1604_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref_known(v___x_1574_, 1);
v_fst_1576_ = lean_ctor_get(v_a_1575_, 0);
v_snd_1577_ = lean_ctor_get(v_a_1575_, 1);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_a_1575_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1579_ = v_a_1575_;
v_isShared_1580_ = v_isSharedCheck_1604_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_snd_1577_);
lean_inc(v_fst_1576_);
lean_dec(v_a_1575_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1604_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; lean_object* v___x_1583_; 
lean_inc_ref(v_00_u03c3s_1553_);
lean_inc(v_u_1552_);
v___x_1581_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1552_, v_00_u03c3s_1553_, v_restHyps_1548_, v_fst_1576_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 2, v___x_1581_);
v___x_1583_ = v___x_1557_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_u_1552_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_00_u03c3s_1553_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v_target_1555_);
v___x_1583_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1584_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1583_);
v___x_1585_ = lean_box(0);
v___x_1586_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1584_, v___x_1585_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1592_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc_n(v_a_1587_, 2);
lean_dec_ref_known(v___x_1586_, 1);
v___x_1588_ = lean_apply_1(v_snd_1577_, v_a_1587_);
v___x_1589_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_fst_1536_, v___x_1588_, v___y_1542_);
lean_dec_ref(v___x_1589_);
v___x_1590_ = l_Lean_Expr_mvarId_x21(v_a_1587_);
lean_dec(v_a_1587_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set_tag(v___x_1579_, 1);
lean_ctor_set(v___x_1579_, 1, v___x_1567_);
lean_ctor_set(v___x_1579_, 0, v___x_1590_);
v___x_1592_ = v___x_1579_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v___x_1567_);
v___x_1592_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1592_, v___y_1538_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
return v___x_1593_;
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_del_object(v___x_1579_);
lean_dec(v_snd_1577_);
lean_dec(v_fst_1536_);
v_a_1595_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1586_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1586_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_del_object(v___x_1557_);
lean_dec_ref(v_target_1555_);
lean_dec_ref(v_00_u03c3s_1553_);
lean_dec(v_u_1552_);
lean_dec_ref(v_restHyps_1548_);
lean_dec(v_fst_1536_);
v_a_1605_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1574_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1574_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
else
{
lean_del_object(v___x_1557_);
lean_dec_ref(v_target_1555_);
lean_dec_ref(v_hyps_1554_);
lean_dec_ref(v_00_u03c3s_1553_);
lean_dec(v_u_1552_);
lean_dec_ref(v_proof_1549_);
lean_dec_ref(v_restHyps_1548_);
lean_dec_ref(v_focusHyp_1547_);
lean_dec(v_fst_1536_);
lean_dec_ref(v___x_1534_);
return v___x_1560_;
}
}
}
else
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
lean_dec(v___x_1550_);
lean_dec_ref(v_proof_1549_);
lean_dec_ref(v_restHyps_1548_);
lean_dec_ref(v_focusHyp_1547_);
lean_dec(v_fst_1536_);
lean_dec_ref(v___x_1534_);
lean_dec(v_hyp_1533_);
lean_dec_ref(v_snd_1532_);
v___x_1614_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3);
v___x_1615_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(v___x_1614_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
return v___x_1615_;
}
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
lean_dec(v_fst_1536_);
lean_dec_ref(v___x_1534_);
lean_dec_ref(v_snd_1532_);
lean_dec(v___x_1531_);
v___x_1616_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5);
v___x_1617_ = l_Lean_MessageData_ofSyntax(v_hyp_1533_);
v___x_1618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1616_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7);
v___x_1620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1618_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_1620_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
return v___x_1621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___boxed(lean_object* v___x_1622_, lean_object* v_snd_1623_, lean_object* v_hyp_1624_, lean_object* v___x_1625_, lean_object* v_args_1626_, lean_object* v_fst_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0(v___x_1622_, v_snd_1623_, v_hyp_1624_, v___x_1625_, v_args_1626_, v_fst_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec_ref(v_args_1626_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize(lean_object* v_x_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; 
v___x_1655_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1656_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2));
lean_inc(v_x_1645_);
v___x_1657_ = l_Lean_Syntax_isOfKind(v_x_1645_, v___x_1656_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; 
lean_dec(v_x_1645_);
v___x_1658_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_1658_;
}
else
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1647_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v_fst_1661_; lean_object* v_snd_1662_; lean_object* v___x_1663_; lean_object* v_hyp_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v_args_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___y_1670_; lean_object* v___x_1671_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1659_, 1);
v_fst_1661_ = lean_ctor_get(v_a_1660_, 0);
lean_inc_n(v_fst_1661_, 2);
v_snd_1662_ = lean_ctor_get(v_a_1660_, 1);
lean_inc_n(v_snd_1662_, 2);
lean_dec(v_a_1660_);
v___x_1663_ = lean_unsigned_to_nat(1u);
v_hyp_1664_ = l_Lean_Syntax_getArg(v_x_1645_, v___x_1663_);
v___x_1665_ = lean_unsigned_to_nat(2u);
v___x_1666_ = l_Lean_Syntax_getArg(v_x_1645_, v___x_1665_);
lean_dec(v_x_1645_);
v_args_1667_ = l_Lean_Syntax_getArgs(v___x_1666_);
lean_dec(v___x_1666_);
v___x_1668_ = l_Lean_TSyntax_getId(v_hyp_1664_);
v___x_1669_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_snd_1662_, v___x_1668_);
lean_dec(v___x_1668_);
v___y_1670_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___boxed), 15, 6);
lean_closure_set(v___y_1670_, 0, v___x_1669_);
lean_closure_set(v___y_1670_, 1, v_snd_1662_);
lean_closure_set(v___y_1670_, 2, v_hyp_1664_);
lean_closure_set(v___y_1670_, 3, v___x_1655_);
lean_closure_set(v___y_1670_, 4, v_args_1667_);
lean_closure_set(v___y_1670_, 5, v_fst_1661_);
v___x_1671_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_fst_1661_, v___y_1670_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
return v___x_1671_;
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec(v_x_1645_);
v_a_1672_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1659_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1659_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___boxed(lean_object* v_x_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize(v_x_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_);
lean_dec(v_a_1688_);
lean_dec_ref(v_a_1687_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2(lean_object* v_mvarId_1691_, lean_object* v_val_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_mvarId_1691_, v_val_1692_, v___y_1698_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___boxed(lean_object* v_mvarId_1703_, lean_object* v_val_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2(v_mvarId_1703_, v_val_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2(lean_object* v_00_u03b2_1715_, lean_object* v_x_1716_, lean_object* v_x_1717_, lean_object* v_x_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2___redArg(v_x_1716_, v_x_1717_, v_x_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_1720_, lean_object* v_x_1721_, size_t v_x_1722_, size_t v_x_1723_, lean_object* v_x_1724_, lean_object* v_x_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_x_1721_, v_x_1722_, v_x_1723_, v_x_1724_, v_x_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1727_, lean_object* v_x_1728_, lean_object* v_x_1729_, lean_object* v_x_1730_, lean_object* v_x_1731_, lean_object* v_x_1732_){
_start:
{
size_t v_x_7919__boxed_1733_; size_t v_x_7920__boxed_1734_; lean_object* v_res_1735_; 
v_x_7919__boxed_1733_ = lean_unbox_usize(v_x_1729_);
lean_dec(v_x_1729_);
v_x_7920__boxed_1734_ = lean_unbox_usize(v_x_1730_);
lean_dec(v_x_1730_);
v_res_1735_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5(v_00_u03b2_1727_, v_x_1728_, v_x_7919__boxed_1733_, v_x_7920__boxed_1734_, v_x_1731_, v_x_1732_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_1736_, lean_object* v_n_1737_, lean_object* v_k_1738_, lean_object* v_v_1739_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6___redArg(v_n_1737_, v_k_1738_, v_v_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7(lean_object* v_00_u03b2_1741_, size_t v_depth_1742_, lean_object* v_keys_1743_, lean_object* v_vals_1744_, lean_object* v_heq_1745_, lean_object* v_i_1746_, lean_object* v_entries_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(v_depth_1742_, v_keys_1743_, v_vals_1744_, v_i_1746_, v_entries_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b2_1749_, lean_object* v_depth_1750_, lean_object* v_keys_1751_, lean_object* v_vals_1752_, lean_object* v_heq_1753_, lean_object* v_i_1754_, lean_object* v_entries_1755_){
_start:
{
size_t v_depth_boxed_1756_; lean_object* v_res_1757_; 
v_depth_boxed_1756_ = lean_unbox_usize(v_depth_1750_);
lean_dec(v_depth_1750_);
v_res_1757_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7(v_00_u03b2_1749_, v_depth_boxed_1756_, v_keys_1751_, v_vals_1752_, v_heq_1753_, v_i_1754_, v_entries_1755_);
lean_dec_ref(v_vals_1752_);
lean_dec_ref(v_keys_1751_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_1758_, lean_object* v_x_1759_, lean_object* v_x_1760_, lean_object* v_x_1761_, lean_object* v_x_1762_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7___redArg(v_x_1759_, v_x_1760_, v_x_1761_, v_x_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1(){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1773_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1774_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2));
v___x_1775_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1));
v___x_1776_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___boxed), 10, 0);
v___x_1777_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1773_, v___x_1774_, v___x_1775_, v___x_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___boxed(lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1();
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; lean_object* v_ngen_1783_; lean_object* v_namePrefix_1784_; lean_object* v_idx_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1814_; 
v___x_1782_ = lean_st_ref_get(v___y_1780_);
v_ngen_1783_ = lean_ctor_get(v___x_1782_, 2);
lean_inc_ref(v_ngen_1783_);
lean_dec(v___x_1782_);
v_namePrefix_1784_ = lean_ctor_get(v_ngen_1783_, 0);
v_idx_1785_ = lean_ctor_get(v_ngen_1783_, 1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_ngen_1783_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1787_ = v_ngen_1783_;
v_isShared_1788_ = v_isSharedCheck_1814_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_idx_1785_);
lean_inc(v_namePrefix_1784_);
lean_dec(v_ngen_1783_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1814_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v_env_1790_; lean_object* v_nextMacroScope_1791_; lean_object* v_auxDeclNGen_1792_; lean_object* v_traceState_1793_; lean_object* v_cache_1794_; lean_object* v_messages_1795_; lean_object* v_infoState_1796_; lean_object* v_snapshotTasks_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1812_; 
v___x_1789_ = lean_st_ref_take(v___y_1780_);
v_env_1790_ = lean_ctor_get(v___x_1789_, 0);
v_nextMacroScope_1791_ = lean_ctor_get(v___x_1789_, 1);
v_auxDeclNGen_1792_ = lean_ctor_get(v___x_1789_, 3);
v_traceState_1793_ = lean_ctor_get(v___x_1789_, 4);
v_cache_1794_ = lean_ctor_get(v___x_1789_, 5);
v_messages_1795_ = lean_ctor_get(v___x_1789_, 6);
v_infoState_1796_ = lean_ctor_get(v___x_1789_, 7);
v_snapshotTasks_1797_ = lean_ctor_get(v___x_1789_, 8);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1812_ == 0)
{
lean_object* v_unused_1813_; 
v_unused_1813_ = lean_ctor_get(v___x_1789_, 2);
lean_dec(v_unused_1813_);
v___x_1799_ = v___x_1789_;
v_isShared_1800_ = v_isSharedCheck_1812_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_snapshotTasks_1797_);
lean_inc(v_infoState_1796_);
lean_inc(v_messages_1795_);
lean_inc(v_cache_1794_);
lean_inc(v_traceState_1793_);
lean_inc(v_auxDeclNGen_1792_);
lean_inc(v_nextMacroScope_1791_);
lean_inc(v_env_1790_);
lean_dec(v___x_1789_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1812_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v_r_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
lean_inc(v_idx_1785_);
lean_inc(v_namePrefix_1784_);
v_r_1801_ = l_Lean_Name_num___override(v_namePrefix_1784_, v_idx_1785_);
v___x_1802_ = lean_unsigned_to_nat(1u);
v___x_1803_ = lean_nat_add(v_idx_1785_, v___x_1802_);
lean_dec(v_idx_1785_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 1, v___x_1803_);
v___x_1805_ = v___x_1787_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_namePrefix_1784_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1807_; 
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 2, v___x_1805_);
v___x_1807_ = v___x_1799_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_env_1790_);
lean_ctor_set(v_reuseFailAlloc_1810_, 1, v_nextMacroScope_1791_);
lean_ctor_set(v_reuseFailAlloc_1810_, 2, v___x_1805_);
lean_ctor_set(v_reuseFailAlloc_1810_, 3, v_auxDeclNGen_1792_);
lean_ctor_set(v_reuseFailAlloc_1810_, 4, v_traceState_1793_);
lean_ctor_set(v_reuseFailAlloc_1810_, 5, v_cache_1794_);
lean_ctor_set(v_reuseFailAlloc_1810_, 6, v_messages_1795_);
lean_ctor_set(v_reuseFailAlloc_1810_, 7, v_infoState_1796_);
lean_ctor_set(v_reuseFailAlloc_1810_, 8, v_snapshotTasks_1797_);
v___x_1807_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = lean_st_ref_put(v___y_1780_, v___x_1807_);
v___x_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1809_, 0, v_r_1801_);
return v___x_1809_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg___boxed(lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(v___y_1815_);
lean_dec(v___y_1815_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0(lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(v___y_1825_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___boxed(lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0(v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(lean_object* v_e_1838_, lean_object* v___y_1839_){
_start:
{
uint8_t v___x_1841_; 
v___x_1841_ = l_Lean_Expr_hasMVar(v_e_1838_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1842_, 0, v_e_1838_);
return v___x_1842_;
}
else
{
lean_object* v___x_1843_; lean_object* v_mctx_1844_; lean_object* v___x_1845_; lean_object* v_fst_1846_; lean_object* v_snd_1847_; lean_object* v___x_1848_; lean_object* v_cache_1849_; lean_object* v_zetaDeltaFVarIds_1850_; lean_object* v_postponed_1851_; lean_object* v_diag_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1861_; 
v___x_1843_ = lean_st_ref_get(v___y_1839_);
v_mctx_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc_ref(v_mctx_1844_);
lean_dec(v___x_1843_);
v___x_1845_ = l_Lean_instantiateMVarsCore(v_mctx_1844_, v_e_1838_);
v_fst_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_fst_1846_);
v_snd_1847_ = lean_ctor_get(v___x_1845_, 1);
lean_inc(v_snd_1847_);
lean_dec_ref(v___x_1845_);
v___x_1848_ = lean_st_ref_take(v___y_1839_);
v_cache_1849_ = lean_ctor_get(v___x_1848_, 1);
v_zetaDeltaFVarIds_1850_ = lean_ctor_get(v___x_1848_, 2);
v_postponed_1851_ = lean_ctor_get(v___x_1848_, 3);
v_diag_1852_ = lean_ctor_get(v___x_1848_, 4);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1861_ == 0)
{
lean_object* v_unused_1862_; 
v_unused_1862_ = lean_ctor_get(v___x_1848_, 0);
lean_dec(v_unused_1862_);
v___x_1854_ = v___x_1848_;
v_isShared_1855_ = v_isSharedCheck_1861_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_diag_1852_);
lean_inc(v_postponed_1851_);
lean_inc(v_zetaDeltaFVarIds_1850_);
lean_inc(v_cache_1849_);
lean_dec(v___x_1848_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1861_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v_snd_1847_);
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_snd_1847_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_cache_1849_);
lean_ctor_set(v_reuseFailAlloc_1860_, 2, v_zetaDeltaFVarIds_1850_);
lean_ctor_set(v_reuseFailAlloc_1860_, 3, v_postponed_1851_);
lean_ctor_set(v_reuseFailAlloc_1860_, 4, v_diag_1852_);
v___x_1857_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = lean_st_ref_put(v___y_1839_, v___x_1857_);
v___x_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1859_, 0, v_fst_1846_);
return v___x_1859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg___boxed(lean_object* v_e_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(v_e_1863_, v___y_1864_);
lean_dec(v___y_1864_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1(lean_object* v_e_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(v_e_1867_, v___y_1873_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___boxed(lean_object* v_e_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1(v_e_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2(lean_object* v___x_1889_, lean_object* v___x_1890_, lean_object* v___x_1891_, lean_object* v___x_1892_, lean_object* v___x_1893_, lean_object* v_as_1894_, size_t v_sz_1895_, size_t v_i_1896_, lean_object* v_b_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_a_1908_; uint8_t v___x_1912_; 
v___x_1912_ = lean_usize_dec_lt(v_i_1896_, v_sz_1895_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; 
lean_dec_ref(v___x_1893_);
lean_dec_ref(v___x_1892_);
lean_dec_ref(v___x_1891_);
lean_dec(v___x_1890_);
lean_dec(v___x_1889_);
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v_b_1897_);
return v___x_1913_;
}
else
{
lean_object* v_fst_1914_; lean_object* v_snd_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1969_; 
v_fst_1914_ = lean_ctor_get(v_b_1897_, 0);
v_snd_1915_ = lean_ctor_get(v_b_1897_, 1);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_b_1897_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1917_ = v_b_1897_;
v_isShared_1918_ = v_isSharedCheck_1969_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_snd_1915_);
lean_inc(v_fst_1914_);
lean_dec(v_b_1897_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1969_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v_a_1922_; lean_object* v___y_1924_; lean_object* v___x_1964_; 
v___x_1919_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_1920_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1921_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v_a_1922_ = lean_array_uget_borrowed(v_as_1894_, v_i_1896_);
lean_inc(v_a_1922_);
lean_inc(v_fst_1914_);
lean_inc_ref(v___x_1892_);
v___x_1964_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(v___x_1892_, v_fst_1914_, v_a_1922_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
if (lean_obj_tag(v_a_1965_) == 0)
{
lean_object* v___x_1966_; 
lean_dec_ref_known(v___x_1964_, 1);
lean_inc(v_a_1922_);
lean_inc(v_fst_1914_);
lean_inc_ref(v___x_1892_);
v___x_1966_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(v___x_1892_, v_fst_1914_, v_a_1922_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
if (lean_obj_tag(v_a_1967_) == 0)
{
lean_object* v___x_1968_; 
lean_dec_ref_known(v___x_1966_, 1);
lean_inc(v_a_1922_);
lean_inc(v_fst_1914_);
lean_inc_ref(v___x_1892_);
v___x_1968_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(v___x_1892_, v_fst_1914_, v_a_1922_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
v___y_1924_ = v___x_1968_;
goto v___jp_1923_;
}
else
{
lean_dec_ref_known(v_a_1967_, 1);
v___y_1924_ = v___x_1966_;
goto v___jp_1923_;
}
}
else
{
v___y_1924_ = v___x_1966_;
goto v___jp_1923_;
}
}
else
{
lean_dec_ref_known(v_a_1965_, 1);
v___y_1924_ = v___x_1964_;
goto v___jp_1923_;
}
}
else
{
v___y_1924_ = v___x_1964_;
goto v___jp_1923_;
}
v___jp_1923_:
{
if (lean_obj_tag(v___y_1924_) == 0)
{
lean_object* v_a_1925_; 
v_a_1925_ = lean_ctor_get(v___y_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v___y_1924_, 1);
if (lean_obj_tag(v_a_1925_) == 0)
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1926_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1);
lean_inc(v_fst_1914_);
v___x_1927_ = l_Lean_MessageData_ofExpr(v_fst_1914_);
v___x_1928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1926_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v___x_1929_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_1930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1928_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
lean_inc(v_a_1922_);
v___x_1931_ = l_Lean_MessageData_ofSyntax(v_a_1922_);
v___x_1932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_1932_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v___x_1935_; 
lean_dec_ref_known(v___x_1933_, 1);
if (v_isShared_1918_ == 0)
{
v___x_1935_ = v___x_1917_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_fst_1914_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_snd_1915_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
v_a_1908_ = v___x_1935_;
goto v___jp_1907_;
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_del_object(v___x_1917_);
lean_dec(v_snd_1915_);
lean_dec(v_fst_1914_);
lean_dec_ref(v___x_1893_);
lean_dec_ref(v___x_1892_);
lean_dec_ref(v___x_1891_);
lean_dec(v___x_1890_);
lean_dec(v___x_1889_);
v_a_1937_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1933_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1933_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
else
{
lean_object* v_val_1945_; lean_object* v_fst_1946_; lean_object* v_snd_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1955_; 
lean_del_object(v___x_1917_);
v_val_1945_ = lean_ctor_get(v_a_1925_, 0);
lean_inc(v_val_1945_);
lean_dec_ref_known(v_a_1925_, 1);
v_fst_1946_ = lean_ctor_get(v_val_1945_, 0);
v_snd_1947_ = lean_ctor_get(v_val_1945_, 1);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_val_1945_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1949_ = v_val_1945_;
v_isShared_1950_ = v_isSharedCheck_1955_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_snd_1947_);
lean_inc(v_fst_1946_);
lean_dec(v_val_1945_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1955_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___f_1951_; lean_object* v___x_1953_; 
lean_inc_ref(v___x_1893_);
lean_inc(v_fst_1946_);
lean_inc_ref(v___x_1892_);
lean_inc_ref(v___x_1891_);
lean_inc(v___x_1890_);
lean_inc(v___x_1889_);
v___f_1951_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0), 13, 12);
lean_closure_set(v___f_1951_, 0, v___x_1919_);
lean_closure_set(v___f_1951_, 1, v___x_1920_);
lean_closure_set(v___f_1951_, 2, v___x_1921_);
lean_closure_set(v___f_1951_, 3, v___x_1889_);
lean_closure_set(v___f_1951_, 4, v___x_1890_);
lean_closure_set(v___f_1951_, 5, v___x_1891_);
lean_closure_set(v___f_1951_, 6, v___x_1892_);
lean_closure_set(v___f_1951_, 7, v_fst_1914_);
lean_closure_set(v___f_1951_, 8, v_fst_1946_);
lean_closure_set(v___f_1951_, 9, v___x_1893_);
lean_closure_set(v___f_1951_, 10, v_snd_1947_);
lean_closure_set(v___f_1951_, 11, v_snd_1915_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 1, v___f_1951_);
v___x_1953_ = v___x_1949_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_fst_1946_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v___f_1951_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
v_a_1908_ = v___x_1953_;
goto v___jp_1907_;
}
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_del_object(v___x_1917_);
lean_dec(v_snd_1915_);
lean_dec(v_fst_1914_);
lean_dec_ref(v___x_1893_);
lean_dec_ref(v___x_1892_);
lean_dec_ref(v___x_1891_);
lean_dec(v___x_1890_);
lean_dec(v___x_1889_);
v_a_1956_ = lean_ctor_get(v___y_1924_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___y_1924_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___y_1924_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___y_1924_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
}
}
v___jp_1907_:
{
size_t v___x_1909_; size_t v___x_1910_; 
v___x_1909_ = ((size_t)1ULL);
v___x_1910_ = lean_usize_add(v_i_1896_, v___x_1909_);
v_i_1896_ = v___x_1910_;
v_b_1897_ = v_a_1908_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2___boxed(lean_object** _args){
lean_object* v___x_1970_ = _args[0];
lean_object* v___x_1971_ = _args[1];
lean_object* v___x_1972_ = _args[2];
lean_object* v___x_1973_ = _args[3];
lean_object* v___x_1974_ = _args[4];
lean_object* v_as_1975_ = _args[5];
lean_object* v_sz_1976_ = _args[6];
lean_object* v_i_1977_ = _args[7];
lean_object* v_b_1978_ = _args[8];
lean_object* v___y_1979_ = _args[9];
lean_object* v___y_1980_ = _args[10];
lean_object* v___y_1981_ = _args[11];
lean_object* v___y_1982_ = _args[12];
lean_object* v___y_1983_ = _args[13];
lean_object* v___y_1984_ = _args[14];
lean_object* v___y_1985_ = _args[15];
lean_object* v___y_1986_ = _args[16];
lean_object* v___y_1987_ = _args[17];
_start:
{
size_t v_sz_boxed_1988_; size_t v_i_boxed_1989_; lean_object* v_res_1990_; 
v_sz_boxed_1988_ = lean_unbox_usize(v_sz_1976_);
lean_dec(v_sz_1976_);
v_i_boxed_1989_ = lean_unbox_usize(v_i_1977_);
lean_dec(v_i_1977_);
v_res_1990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2(v___x_1970_, v___x_1971_, v___x_1972_, v___x_1973_, v___x_1974_, v_as_1975_, v_sz_boxed_1988_, v_i_boxed_1989_, v_b_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec_ref(v_as_1975_);
return v_res_1990_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_1998_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__3));
v___x_1999_ = lean_unsigned_to_nat(33u);
v___x_2000_ = lean_unsigned_to_nat(175u);
v___x_2001_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__2));
v___x_2002_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15));
v___x_2003_ = l_mkPanicMessageWithDecl(v___x_2002_, v___x_2001_, v___x_2000_, v___x_1999_, v___x_1998_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0(lean_object* v___x_2004_, lean_object* v___x_2005_, uint8_t v___x_2006_, lean_object* v_u_2007_, lean_object* v_00_u03c3s_2008_, lean_object* v___x_2009_, lean_object* v_hyp_2010_, lean_object* v_hyps_2011_, lean_object* v_target_2012_, lean_object* v_args_2013_, lean_object* v_fst_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_Elab_Tactic_elabTerm(v___x_2004_, v___x_2005_, v___x_2006_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2026_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc_n(v_a_2025_, 2);
lean_dec_ref_known(v___x_2024_, 1);
lean_inc(v___y_2022_);
lean_inc_ref(v___y_2021_);
lean_inc(v___y_2020_);
lean_inc_ref(v___y_2019_);
v___x_2026_ = lean_infer_type(v_a_2025_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2026_, 1);
v___x_2028_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_2029_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_2030_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_2031_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0));
v___x_2032_ = lean_box(0);
lean_inc(v_u_2007_);
v___x_2033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2033_, 0, v_u_2007_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
lean_inc_ref(v___x_2033_);
v___x_2034_ = l_Lean_mkConst(v___x_2031_, v___x_2033_);
lean_inc_ref(v_00_u03c3s_2008_);
v___x_2035_ = l_Lean_Expr_app___override(v___x_2034_, v_00_u03c3s_2008_);
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
v___x_2037_ = 0;
v___x_2038_ = lean_box(0);
v___x_2039_ = l_Lean_Meta_mkFreshExprMVar(v___x_2036_, v___x_2037_, v___x_2038_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc_n(v_a_2040_, 2);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2041_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__5));
lean_inc_ref(v___x_2009_);
v___x_2042_ = l_Lean_Name_mkStr5(v___x_2028_, v___x_2029_, v___x_2030_, v___x_2009_, v___x_2041_);
lean_inc_ref(v___x_2033_);
v___x_2043_ = l_Lean_mkConst(v___x_2042_, v___x_2033_);
lean_inc_ref(v_00_u03c3s_2008_);
lean_inc(v_a_2027_);
v___x_2044_ = l_Lean_mkApp3(v___x_2043_, v_a_2027_, v_00_u03c3s_2008_, v_a_2040_);
v___x_2045_ = lean_box(0);
v___x_2046_ = l_Lean_Meta_synthInstance(v___x_2044_, v___x_2045_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2048_; lean_object* v_a_2049_; lean_object* v___x_2050_; lean_object* v_a_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; size_t v_sz_2061_; size_t v___x_2062_; lean_object* v___x_2063_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2046_, 1);
v___x_2048_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(v___y_2022_);
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2049_);
lean_dec_ref(v___x_2048_);
v___x_2050_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(v_a_2040_, v___y_2020_);
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref(v___x_2050_);
v___x_2052_ = l_Lean_TSyntax_getId(v_hyp_2010_);
v___x_2053_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
lean_ctor_set(v___x_2053_, 1, v_a_2049_);
lean_ctor_set(v___x_2053_, 2, v_a_2051_);
v___x_2054_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_2053_);
v___x_2055_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_2056_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__1));
v___x_2057_ = l_Lean_Name_mkStr6(v___x_2028_, v___x_2029_, v___x_2030_, v___x_2009_, v___x_2055_, v___x_2056_);
lean_inc_ref(v___x_2033_);
v___x_2058_ = l_Lean_mkConst(v___x_2057_, v___x_2033_);
lean_inc_ref_n(v_target_2012_, 2);
lean_inc_ref_n(v_hyps_2011_, 2);
lean_inc_ref(v___x_2054_);
lean_inc_ref_n(v_00_u03c3s_2008_, 2);
v___x_2059_ = lean_alloc_closure((void*)(l_Lean_mkApp8), 9, 8);
lean_closure_set(v___x_2059_, 0, v___x_2058_);
lean_closure_set(v___x_2059_, 1, v_00_u03c3s_2008_);
lean_closure_set(v___x_2059_, 2, v_a_2027_);
lean_closure_set(v___x_2059_, 3, v___x_2054_);
lean_closure_set(v___x_2059_, 4, v_hyps_2011_);
lean_closure_set(v___x_2059_, 5, v_target_2012_);
lean_closure_set(v___x_2059_, 6, v_a_2047_);
lean_closure_set(v___x_2059_, 7, v_a_2025_);
v___x_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2054_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
v_sz_2061_ = lean_array_size(v_args_2013_);
v___x_2062_ = ((size_t)0ULL);
lean_inc(v_u_2007_);
v___x_2063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2(v___x_2033_, v_u_2007_, v_00_u03c3s_2008_, v_hyps_2011_, v_target_2012_, v_args_2013_, v_sz_2061_, v___x_2062_, v___x_2060_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v_fst_2065_; lean_object* v_snd_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2095_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref_known(v___x_2063_, 1);
v_fst_2065_ = lean_ctor_get(v_a_2064_, 0);
v_snd_2066_ = lean_ctor_get(v_a_2064_, 1);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_a_2064_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2068_ = v_a_2064_;
v_isShared_2069_ = v_isSharedCheck_2095_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_snd_2066_);
lean_inc(v_fst_2065_);
lean_dec(v_a_2064_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2095_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; 
lean_inc(v_fst_2065_);
v___x_2070_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_fst_2065_);
if (lean_obj_tag(v___x_2070_) == 1)
{
lean_object* v_val_2071_; lean_object* v___x_2072_; 
v_val_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_val_2071_);
lean_dec_ref_known(v___x_2070_, 1);
lean_inc_ref(v_00_u03c3s_2008_);
v___x_2072_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_hyp_2010_, v_00_u03c3s_2008_, v_val_2071_, v___x_2006_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
lean_dec_ref_known(v___x_2072_, 1);
lean_inc_ref(v_00_u03c3s_2008_);
lean_inc(v_u_2007_);
v___x_2073_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_2007_, v_00_u03c3s_2008_, v_hyps_2011_, v_fst_2065_);
v___x_2074_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2074_, 0, v_u_2007_);
lean_ctor_set(v___x_2074_, 1, v_00_u03c3s_2008_);
lean_ctor_set(v___x_2074_, 2, v___x_2073_);
lean_ctor_set(v___x_2074_, 3, v_target_2012_);
v___x_2075_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_2074_);
v___x_2076_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2075_, v___x_2038_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2082_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc_n(v_a_2077_, 2);
lean_dec_ref_known(v___x_2076_, 1);
v___x_2078_ = lean_apply_1(v_snd_2066_, v_a_2077_);
v___x_2079_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_fst_2014_, v___x_2078_, v___y_2020_);
lean_dec_ref(v___x_2079_);
v___x_2080_ = l_Lean_Expr_mvarId_x21(v_a_2077_);
lean_dec(v_a_2077_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set_tag(v___x_2068_, 1);
lean_ctor_set(v___x_2068_, 1, v___x_2032_);
lean_ctor_set(v___x_2068_, 0, v___x_2080_);
v___x_2082_ = v___x_2068_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2080_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v___x_2032_);
v___x_2082_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2082_, v___y_2016_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
return v___x_2083_;
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_del_object(v___x_2068_);
lean_dec(v_snd_2066_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v_fst_2014_);
v_a_2085_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2076_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2076_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
else
{
lean_del_object(v___x_2068_);
lean_dec(v_snd_2066_);
lean_dec(v_fst_2065_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v_fst_2014_);
lean_dec_ref(v_target_2012_);
lean_dec_ref(v_hyps_2011_);
lean_dec_ref(v_00_u03c3s_2008_);
lean_dec(v_u_2007_);
return v___x_2072_;
}
}
else
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
lean_dec(v___x_2070_);
lean_del_object(v___x_2068_);
lean_dec(v_snd_2066_);
lean_dec(v_fst_2065_);
lean_dec(v_fst_2014_);
lean_dec_ref(v_target_2012_);
lean_dec_ref(v_hyps_2011_);
lean_dec(v_hyp_2010_);
lean_dec_ref(v_00_u03c3s_2008_);
lean_dec(v_u_2007_);
v___x_2093_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4, &l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4);
v___x_2094_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(v___x_2093_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
return v___x_2094_;
}
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v_fst_2014_);
lean_dec_ref(v_target_2012_);
lean_dec_ref(v_hyps_2011_);
lean_dec(v_hyp_2010_);
lean_dec_ref(v_00_u03c3s_2008_);
lean_dec(v_u_2007_);
v_a_2096_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2063_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2063_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec(v_a_2040_);
lean_dec_ref_known(v___x_2033_, 2);
lean_dec(v_a_2027_);
lean_dec(v_a_2025_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v_fst_2014_);
lean_dec_ref(v_target_2012_);
lean_dec_ref(v_hyps_2011_);
lean_dec(v_hyp_2010_);
lean_dec_ref(v___x_2009_);
lean_dec_ref(v_00_u03c3s_2008_);
lean_dec(v_u_2007_);
v_a_2104_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2046_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2046_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec_ref_known(v___x_2033_, 2);
lean_dec(v_a_2027_);
lean_dec(v_a_2025_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v_fst_2014_);
lean_dec_ref(v_target_2012_);
lean_dec_ref(v_hyps_2011_);
lean_dec(v_hyp_2010_);
lean_dec_ref(v___x_2009_);
lean_dec_ref(v_00_u03c3s_2008_);
lean_dec(v_u_2007_);
v_a_2112_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2039_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2039_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec(v_a_2025_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v_fst_2014_);
lean_dec_ref(v_target_2012_);
lean_dec_ref(v_hyps_2011_);
lean_dec(v_hyp_2010_);
lean_dec_ref(v___x_2009_);
lean_dec_ref(v_00_u03c3s_2008_);
lean_dec(v_u_2007_);
v_a_2120_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2026_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2026_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v_fst_2014_);
lean_dec_ref(v_target_2012_);
lean_dec_ref(v_hyps_2011_);
lean_dec(v_hyp_2010_);
lean_dec_ref(v___x_2009_);
lean_dec_ref(v_00_u03c3s_2008_);
lean_dec(v_u_2007_);
v_a_2128_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2024_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2024_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___boxed(lean_object** _args){
lean_object* v___x_2136_ = _args[0];
lean_object* v___x_2137_ = _args[1];
lean_object* v___x_2138_ = _args[2];
lean_object* v_u_2139_ = _args[3];
lean_object* v_00_u03c3s_2140_ = _args[4];
lean_object* v___x_2141_ = _args[5];
lean_object* v_hyp_2142_ = _args[6];
lean_object* v_hyps_2143_ = _args[7];
lean_object* v_target_2144_ = _args[8];
lean_object* v_args_2145_ = _args[9];
lean_object* v_fst_2146_ = _args[10];
lean_object* v___y_2147_ = _args[11];
lean_object* v___y_2148_ = _args[12];
lean_object* v___y_2149_ = _args[13];
lean_object* v___y_2150_ = _args[14];
lean_object* v___y_2151_ = _args[15];
lean_object* v___y_2152_ = _args[16];
lean_object* v___y_2153_ = _args[17];
lean_object* v___y_2154_ = _args[18];
lean_object* v___y_2155_ = _args[19];
_start:
{
uint8_t v___x_8346__boxed_2156_; lean_object* v_res_2157_; 
v___x_8346__boxed_2156_ = lean_unbox(v___x_2138_);
v_res_2157_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0(v___x_2136_, v___x_2137_, v___x_8346__boxed_2156_, v_u_2139_, v_00_u03c3s_2140_, v___x_2141_, v_hyp_2142_, v_hyps_2143_, v_target_2144_, v_args_2145_, v_fst_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec_ref(v_args_2145_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure(lean_object* v_x_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; 
v___x_2181_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_2182_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1));
lean_inc(v_x_2171_);
v___x_2183_ = l_Lean_Syntax_isOfKind(v_x_2171_, v___x_2182_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; 
lean_dec(v_x_2171_);
v___x_2184_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_2184_;
}
else
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; 
v___x_2185_ = lean_unsigned_to_nat(1u);
v___x_2186_ = l_Lean_Syntax_getArg(v_x_2171_, v___x_2185_);
v___x_2187_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4));
lean_inc(v___x_2186_);
v___x_2188_ = l_Lean_Syntax_isOfKind(v___x_2186_, v___x_2187_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2189_; 
lean_dec(v___x_2186_);
lean_dec(v_x_2171_);
v___x_2189_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_2189_;
}
else
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2190_ = lean_unsigned_to_nat(0u);
v___x_2191_ = lean_unsigned_to_nat(2u);
v___x_2192_ = l_Lean_Syntax_getArg(v_x_2171_, v___x_2191_);
v___x_2193_ = l_Lean_Syntax_matchesNull(v___x_2192_, v___x_2190_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; 
lean_dec(v___x_2186_);
lean_dec(v_x_2171_);
v___x_2194_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_2194_;
}
else
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_2173_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v_snd_2197_; lean_object* v_fst_2198_; lean_object* v_u_2199_; lean_object* v_00_u03c3s_2200_; lean_object* v_hyps_2201_; lean_object* v_target_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v_hyp_2206_; lean_object* v_args_2207_; lean_object* v___x_2208_; uint8_t v___x_2209_; lean_object* v___x_2210_; lean_object* v___f_2211_; lean_object* v___x_2212_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref_known(v___x_2195_, 1);
v_snd_2197_ = lean_ctor_get(v_a_2196_, 1);
lean_inc(v_snd_2197_);
v_fst_2198_ = lean_ctor_get(v_a_2196_, 0);
lean_inc_n(v_fst_2198_, 2);
lean_dec(v_a_2196_);
v_u_2199_ = lean_ctor_get(v_snd_2197_, 0);
lean_inc(v_u_2199_);
v_00_u03c3s_2200_ = lean_ctor_get(v_snd_2197_, 1);
lean_inc_ref(v_00_u03c3s_2200_);
v_hyps_2201_ = lean_ctor_get(v_snd_2197_, 2);
lean_inc_ref(v_hyps_2201_);
v_target_2202_ = lean_ctor_get(v_snd_2197_, 3);
lean_inc_ref(v_target_2202_);
lean_dec(v_snd_2197_);
v___x_2203_ = l_Lean_Syntax_getArg(v___x_2186_, v___x_2190_);
v___x_2204_ = l_Lean_Syntax_getArg(v___x_2186_, v___x_2185_);
lean_dec(v___x_2186_);
v___x_2205_ = lean_unsigned_to_nat(4u);
v_hyp_2206_ = l_Lean_Syntax_getArg(v_x_2171_, v___x_2205_);
lean_dec(v_x_2171_);
v_args_2207_ = l_Lean_Syntax_getArgs(v___x_2204_);
lean_dec(v___x_2204_);
v___x_2208_ = lean_box(0);
v___x_2209_ = 0;
v___x_2210_ = lean_box(v___x_2209_);
v___f_2211_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___boxed), 20, 11);
lean_closure_set(v___f_2211_, 0, v___x_2203_);
lean_closure_set(v___f_2211_, 1, v___x_2208_);
lean_closure_set(v___f_2211_, 2, v___x_2210_);
lean_closure_set(v___f_2211_, 3, v_u_2199_);
lean_closure_set(v___f_2211_, 4, v_00_u03c3s_2200_);
lean_closure_set(v___f_2211_, 5, v___x_2181_);
lean_closure_set(v___f_2211_, 6, v_hyp_2206_);
lean_closure_set(v___f_2211_, 7, v_hyps_2201_);
lean_closure_set(v___f_2211_, 8, v_target_2202_);
lean_closure_set(v___f_2211_, 9, v_args_2207_);
lean_closure_set(v___f_2211_, 10, v_fst_2198_);
v___x_2212_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_fst_2198_, v___f_2211_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
return v___x_2212_;
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec(v___x_2186_);
lean_dec(v_x_2171_);
v_a_2213_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2195_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2195_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___boxed(lean_object* v_x_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure(v_x_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1(){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2241_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2242_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1));
v___x_2243_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1));
v___x_2244_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___boxed), 10, 0);
v___x_2245_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2241_, v___x_2242_, v___x_2243_, v___x_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___boxed(lean_object* v_a_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1();
return v_res_2247_;
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
