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
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "specialize"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(218, 187, 99, 122, 205, 56, 35, 106)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 237, 62, 57, 45, 132, 211, 125)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(158, 126, 187, 23, 173, 74, 254, 143)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 138, 196, 39, 216, 198, 126, 202)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(114, 36, 95, 227, 89, 89, 172, 229)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(144, 46, 212, 242, 236, 17, 131, 103)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(109, 91, 243, 178, 107, 229, 236, 246)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 28, 66, 152, 156, 187, 94, 58)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 199, 97, 198, 237, 142, 216, 64)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Specialize"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(3, 86, 247, 14, 172, 154, 177, 91)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1458348229) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(151, 238, 33, 67, 234, 227, 148, 67)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(156, 165, 47, 122, 10, 183, 39, 41)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(104, 112, 125, 246, 240, 217, 127, 204)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(41, 133, 184, 64, 198, 8, 101, 215)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2____boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 115, 245, 151, 170, 35, 10, 68)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(241, 143, 174, 76, 41, 16, 248, 244)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "IsPure"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__3_value),LEAN_SCALAR_PTR_LITERAL(237, 27, 197, 114, 200, 2, 153, 253)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "PropAsSPredTautology"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 191, 216, 96, 0, 209, 179, 40)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "imp_pure"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 115, 245, 151, 170, 35, 10, 68)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__7_value),LEAN_SCALAR_PTR_LITERAL(194, 113, 147, 239, 22, 13, 55, 251)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Purely specialize "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "pure_taut"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 115, 245, 151, 170, 35, 10, 68)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__11_value),LEAN_SCALAR_PTR_LITERAL(154, 170, 199, 122, 147, 93, 65, 106)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "tautological"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 115, 245, 151, 170, 35, 10, 68)}};
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__2;
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
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "elabMSpecialize"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 116, 229, 144, 100, 97, 175, 56)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 62, 145, 88, 202, 28, 127)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "elabMspecializePure"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(150, 249, 52, 165, 26, 61, 227, 217)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_70_; uint8_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_71_ = 0;
v___x_72_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_73_ = l_Lean_registerTraceClass(v___x_70_, v___x_71_, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2____boxed(lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_();
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(lean_object* v_msgData_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v___x_82_; lean_object* v_env_83_; lean_object* v___x_84_; lean_object* v_mctx_85_; lean_object* v_lctx_86_; lean_object* v_options_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_82_ = lean_st_ref_get(v___y_80_);
v_env_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc_ref(v_env_83_);
lean_dec(v___x_82_);
v___x_84_ = lean_st_ref_get(v___y_78_);
v_mctx_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc_ref(v_mctx_85_);
lean_dec(v___x_84_);
v_lctx_86_ = lean_ctor_get(v___y_77_, 2);
v_options_87_ = lean_ctor_get(v___y_79_, 2);
lean_inc_ref(v_options_87_);
lean_inc_ref(v_lctx_86_);
v___x_88_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_88_, 0, v_env_83_);
lean_ctor_set(v___x_88_, 1, v_mctx_85_);
lean_ctor_set(v___x_88_, 2, v_lctx_86_);
lean_ctor_set(v___x_88_, 3, v_options_87_);
v___x_89_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v_msgData_76_);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0___boxed(lean_object* v_msgData_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(v_msgData_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
return v_res_97_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_98_; double v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_float_of_nat(v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(lean_object* v_cls_103_, lean_object* v_msg_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_ref_110_; lean_object* v___x_111_; lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_156_; 
v_ref_110_ = lean_ctor_get(v___y_107_, 5);
v___x_111_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(v_msg_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
v_a_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_156_ == 0)
{
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_156_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_156_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v_traceState_117_; lean_object* v_env_118_; lean_object* v_nextMacroScope_119_; lean_object* v_ngen_120_; lean_object* v_auxDeclNGen_121_; lean_object* v_cache_122_; lean_object* v_messages_123_; lean_object* v_infoState_124_; lean_object* v_snapshotTasks_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_155_; 
v___x_116_ = lean_st_ref_take(v___y_108_);
v_traceState_117_ = lean_ctor_get(v___x_116_, 4);
v_env_118_ = lean_ctor_get(v___x_116_, 0);
v_nextMacroScope_119_ = lean_ctor_get(v___x_116_, 1);
v_ngen_120_ = lean_ctor_get(v___x_116_, 2);
v_auxDeclNGen_121_ = lean_ctor_get(v___x_116_, 3);
v_cache_122_ = lean_ctor_get(v___x_116_, 5);
v_messages_123_ = lean_ctor_get(v___x_116_, 6);
v_infoState_124_ = lean_ctor_get(v___x_116_, 7);
v_snapshotTasks_125_ = lean_ctor_get(v___x_116_, 8);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_155_ == 0)
{
v___x_127_ = v___x_116_;
v_isShared_128_ = v_isSharedCheck_155_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_snapshotTasks_125_);
lean_inc(v_infoState_124_);
lean_inc(v_messages_123_);
lean_inc(v_cache_122_);
lean_inc(v_traceState_117_);
lean_inc(v_auxDeclNGen_121_);
lean_inc(v_ngen_120_);
lean_inc(v_nextMacroScope_119_);
lean_inc(v_env_118_);
lean_dec(v___x_116_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_155_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
uint64_t v_tid_129_; lean_object* v_traces_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_154_; 
v_tid_129_ = lean_ctor_get_uint64(v_traceState_117_, sizeof(void*)*1);
v_traces_130_ = lean_ctor_get(v_traceState_117_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v_traceState_117_);
if (v_isSharedCheck_154_ == 0)
{
v___x_132_ = v_traceState_117_;
v_isShared_133_ = v_isSharedCheck_154_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_traces_130_);
lean_dec(v_traceState_117_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_154_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; double v___x_135_; uint8_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_134_ = lean_box(0);
v___x_135_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0);
v___x_136_ = 0;
v___x_137_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__1));
v___x_138_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_138_, 0, v_cls_103_);
lean_ctor_set(v___x_138_, 1, v___x_134_);
lean_ctor_set(v___x_138_, 2, v___x_137_);
lean_ctor_set_float(v___x_138_, sizeof(void*)*3, v___x_135_);
lean_ctor_set_float(v___x_138_, sizeof(void*)*3 + 8, v___x_135_);
lean_ctor_set_uint8(v___x_138_, sizeof(void*)*3 + 16, v___x_136_);
v___x_139_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__2));
v___x_140_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_140_, 0, v___x_138_);
lean_ctor_set(v___x_140_, 1, v_a_112_);
lean_ctor_set(v___x_140_, 2, v___x_139_);
lean_inc(v_ref_110_);
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v_ref_110_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v___x_142_ = l_Lean_PersistentArray_push___redArg(v_traces_130_, v___x_141_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v___x_142_);
v___x_144_ = v___x_132_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_142_);
lean_ctor_set_uint64(v_reuseFailAlloc_153_, sizeof(void*)*1, v_tid_129_);
v___x_144_ = v_reuseFailAlloc_153_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_146_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 4, v___x_144_);
v___x_146_ = v___x_127_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_env_118_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_nextMacroScope_119_);
lean_ctor_set(v_reuseFailAlloc_152_, 2, v_ngen_120_);
lean_ctor_set(v_reuseFailAlloc_152_, 3, v_auxDeclNGen_121_);
lean_ctor_set(v_reuseFailAlloc_152_, 4, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_152_, 5, v_cache_122_);
lean_ctor_set(v_reuseFailAlloc_152_, 6, v_messages_123_);
lean_ctor_set(v_reuseFailAlloc_152_, 7, v_infoState_124_);
lean_ctor_set(v_reuseFailAlloc_152_, 8, v_snapshotTasks_125_);
v___x_146_ = v_reuseFailAlloc_152_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_147_ = lean_st_ref_set(v___y_108_, v___x_146_);
v___x_148_ = lean_box(0);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_148_);
v___x_150_ = v___x_114_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___boxed(lean_object* v_cls_157_, lean_object* v_msg_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v_cls_157_, v_msg_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(lean_object* v_msg_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_ref_171_; lean_object* v___x_172_; lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_181_; 
v_ref_171_ = lean_ctor_get(v___y_168_, 5);
v___x_172_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(v_msg_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_181_ == 0)
{
v___x_175_ = v___x_172_;
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
lean_inc(v_ref_171_);
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v_ref_171_);
lean_ctor_set(v___x_177_, 1, v_a_173_);
if (v_isShared_176_ == 0)
{
lean_ctor_set_tag(v___x_175_, 1);
lean_ctor_set(v___x_175_, 0, v___x_177_);
v___x_179_ = v___x_175_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg___boxed(lean_object* v_msg_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v_msg_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
return v_res_188_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__5));
v___x_202_ = l_Lean_stringToMessageData(v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__7));
v___x_205_ = l_Lean_stringToMessageData(v___x_204_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_210_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__10));
v___x_211_ = l_Lean_Name_append(v___x_210_, v___x_209_);
return v___x_211_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__12));
v___x_214_ = l_Lean_stringToMessageData(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__14));
v___x_217_ = l_Lean_stringToMessageData(v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(lean_object* v_P_218_, lean_object* v_QR_219_, lean_object* v_arg_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
uint8_t v___x_233_; 
v___x_233_ = l_Lean_Syntax_isIdent(v_arg_220_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; lean_object* v___x_235_; 
lean_dec(v_arg_220_);
lean_dec_ref(v_QR_219_);
lean_dec_ref(v_P_218_);
v___x_234_ = lean_box(0);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
else
{
lean_object* v___x_236_; 
lean_inc_ref(v_QR_219_);
v___x_236_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_QR_219_);
if (lean_obj_tag(v___x_236_) == 1)
{
lean_object* v_val_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_393_; 
v_val_237_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_393_ == 0)
{
v___x_239_ = v___x_236_;
v_isShared_240_ = v_isSharedCheck_393_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_val_237_);
lean_dec(v___x_236_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_393_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v_p_241_; 
v_p_241_ = lean_ctor_get(v_val_237_, 2);
lean_inc_ref(v_p_241_);
if (lean_obj_tag(v_p_241_) == 5)
{
lean_object* v_fn_242_; 
v_fn_242_ = lean_ctor_get(v_p_241_, 0);
if (lean_obj_tag(v_fn_242_) == 5)
{
lean_object* v_fn_243_; 
v_fn_243_ = lean_ctor_get(v_fn_242_, 0);
if (lean_obj_tag(v_fn_243_) == 5)
{
lean_object* v_fn_244_; 
v_fn_244_ = lean_ctor_get(v_fn_243_, 0);
if (lean_obj_tag(v_fn_244_) == 4)
{
lean_object* v_declName_245_; 
v_declName_245_ = lean_ctor_get(v_fn_244_, 0);
if (lean_obj_tag(v_declName_245_) == 1)
{
lean_object* v_pre_246_; 
v_pre_246_ = lean_ctor_get(v_declName_245_, 0);
if (lean_obj_tag(v_pre_246_) == 1)
{
lean_object* v_pre_247_; 
v_pre_247_ = lean_ctor_get(v_pre_246_, 0);
if (lean_obj_tag(v_pre_247_) == 1)
{
lean_object* v_pre_248_; 
v_pre_248_ = lean_ctor_get(v_pre_247_, 0);
if (lean_obj_tag(v_pre_248_) == 1)
{
lean_object* v_pre_249_; 
v_pre_249_ = lean_ctor_get(v_pre_248_, 0);
if (lean_obj_tag(v_pre_249_) == 0)
{
lean_object* v_name_250_; lean_object* v_uniq_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_391_; 
v_name_250_ = lean_ctor_get(v_val_237_, 0);
v_uniq_251_ = lean_ctor_get(v_val_237_, 1);
v_isSharedCheck_391_ = !lean_is_exclusive(v_val_237_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; 
v_unused_392_ = lean_ctor_get(v_val_237_, 2);
lean_dec(v_unused_392_);
v___x_253_ = v_val_237_;
v_isShared_254_ = v_isSharedCheck_391_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_uniq_251_);
lean_inc(v_name_250_);
lean_dec(v_val_237_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_391_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v_arg_255_; lean_object* v_arg_256_; lean_object* v_arg_257_; lean_object* v_us_258_; lean_object* v_str_259_; lean_object* v_str_260_; lean_object* v_str_261_; lean_object* v_str_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_arg_255_ = lean_ctor_get(v_p_241_, 1);
v_arg_256_ = lean_ctor_get(v_fn_242_, 1);
v_arg_257_ = lean_ctor_get(v_fn_243_, 1);
v_us_258_ = lean_ctor_get(v_fn_244_, 1);
v_str_259_ = lean_ctor_get(v_declName_245_, 1);
v_str_260_ = lean_ctor_get(v_pre_246_, 1);
v_str_261_ = lean_ctor_get(v_pre_247_, 1);
v_str_262_ = lean_ctor_get(v_pre_248_, 1);
v___x_263_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_264_ = lean_string_dec_eq(v_str_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_del_object(v___x_253_);
lean_dec(v_uniq_251_);
lean_dec(v_name_250_);
lean_dec_ref(v_p_241_);
lean_del_object(v___x_239_);
lean_dec(v_arg_220_);
lean_dec_ref(v_QR_219_);
lean_dec_ref(v_P_218_);
goto v___jp_230_;
}
else
{
lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_265_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_266_ = lean_string_dec_eq(v_str_261_, v___x_265_);
if (v___x_266_ == 0)
{
lean_del_object(v___x_253_);
lean_dec(v_uniq_251_);
lean_dec(v_name_250_);
lean_dec_ref(v_p_241_);
lean_del_object(v___x_239_);
lean_dec(v_arg_220_);
lean_dec_ref(v_QR_219_);
lean_dec_ref(v_P_218_);
goto v___jp_230_;
}
else
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_268_ = lean_string_dec_eq(v_str_260_, v___x_267_);
if (v___x_268_ == 0)
{
lean_del_object(v___x_253_);
lean_dec(v_uniq_251_);
lean_dec(v_name_250_);
lean_dec_ref(v_p_241_);
lean_del_object(v___x_239_);
lean_dec(v_arg_220_);
lean_dec_ref(v_QR_219_);
lean_dec_ref(v_P_218_);
goto v___jp_230_;
}
else
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__2));
v___x_270_ = lean_string_dec_eq(v_str_259_, v___x_269_);
if (v___x_270_ == 0)
{
lean_del_object(v___x_253_);
lean_dec(v_uniq_251_);
lean_dec(v_name_250_);
lean_dec_ref(v_p_241_);
lean_del_object(v___x_239_);
lean_dec(v_arg_220_);
lean_dec_ref(v_QR_219_);
lean_dec_ref(v_P_218_);
goto v___jp_230_;
}
else
{
if (lean_obj_tag(v_us_258_) == 1)
{
lean_object* v_tail_271_; 
v_tail_271_ = lean_ctor_get(v_us_258_, 1);
if (lean_obj_tag(v_tail_271_) == 0)
{
lean_object* v_head_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v_head_272_ = lean_ctor_get(v_us_258_, 0);
lean_inc_ref(v_P_218_);
lean_inc_ref_n(v_arg_257_, 2);
lean_inc_n(v_head_272_, 2);
v___x_273_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_head_272_, v_arg_257_, v_P_218_, v_QR_219_);
v___x_274_ = l_Lean_Syntax_getId(v_arg_220_);
v___x_275_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(v_head_272_, v_arg_257_, v___x_273_, v___x_274_);
lean_dec(v___x_274_);
if (lean_obj_tag(v___x_275_) == 1)
{
lean_object* v_val_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_386_; 
lean_del_object(v___x_239_);
v_val_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_386_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_386_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_val_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_386_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v_focusHyp_280_; lean_object* v_restHyps_281_; lean_object* v_proof_282_; lean_object* v___x_283_; 
v_focusHyp_280_ = lean_ctor_get(v_val_276_, 0);
lean_inc_ref_n(v_focusHyp_280_, 2);
v_restHyps_281_ = lean_ctor_get(v_val_276_, 1);
lean_inc_ref(v_restHyps_281_);
v_proof_282_ = lean_ctor_get(v_val_276_, 2);
lean_inc_ref(v_proof_282_);
lean_dec(v_val_276_);
v___x_283_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_280_);
if (lean_obj_tag(v___x_283_) == 1)
{
lean_object* v_val_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_381_; 
lean_del_object(v___x_278_);
v_val_284_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_381_ == 0)
{
v___x_286_ = v___x_283_;
v_isShared_287_ = v_isSharedCheck_381_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_val_284_);
lean_dec(v___x_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_381_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
uint8_t v___x_288_; lean_object* v___x_289_; 
v___x_288_ = 0;
lean_inc_ref(v_arg_257_);
v___x_289_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_arg_220_, v_arg_257_, v_val_284_, v___x_288_, v_a_225_, v_a_226_, v_a_227_, v_a_228_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_371_; 
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; 
v_unused_372_ = lean_ctor_get(v___x_289_, 0);
lean_dec(v_unused_372_);
v___x_291_ = v___x_289_;
v_isShared_292_ = v_isSharedCheck_371_;
goto v_resetjp_290_;
}
else
{
lean_dec(v___x_289_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_371_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v_options_293_; lean_object* v_inheritedTraceOptions_294_; uint8_t v_hasTrace_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; 
v_options_293_ = lean_ctor_get(v_a_227_, 2);
v_inheritedTraceOptions_294_ = lean_ctor_get(v_a_227_, 13);
v_hasTrace_295_ = lean_ctor_get_uint8(v_options_293_, sizeof(void*)*1);
v___x_296_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4));
lean_inc_ref(v_us_258_);
v___x_297_ = l_Lean_mkConst(v___x_296_, v_us_258_);
lean_inc_ref(v_arg_255_);
lean_inc_ref(v_focusHyp_280_);
lean_inc_ref(v_P_218_);
lean_inc_ref(v_arg_257_);
v___x_298_ = l_Lean_mkApp6(v___x_297_, v_arg_257_, v_P_218_, v_restHyps_281_, v_focusHyp_280_, v_arg_255_, v_proof_282_);
if (v_hasTrace_295_ == 0)
{
lean_dec_ref(v_P_218_);
v___y_312_ = v_a_221_;
v___y_313_ = v_a_222_;
v___y_314_ = v_a_223_;
v___y_315_ = v_a_224_;
v___y_316_ = v_a_225_;
v___y_317_ = v_a_226_;
v___y_318_ = v_a_227_;
v___y_319_ = v_a_228_;
goto v___jp_311_;
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_347_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_348_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11);
v___x_349_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_294_, v_options_293_, v___x_348_);
if (v___x_349_ == 0)
{
lean_dec_ref(v_P_218_);
v___y_312_ = v_a_221_;
v___y_313_ = v_a_222_;
v___y_314_ = v_a_223_;
v___y_315_ = v_a_224_;
v___y_316_ = v_a_225_;
v___y_317_ = v_a_226_;
v___y_318_ = v_a_227_;
v___y_319_ = v_a_228_;
goto v___jp_311_;
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_350_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13);
lean_inc_ref(v_p_241_);
v___x_351_ = l_Lean_MessageData_ofExpr(v_p_241_);
v___x_352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_352_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
lean_inc_ref(v_focusHyp_280_);
v___x_355_ = l_Lean_MessageData_ofExpr(v_focusHyp_280_);
v___x_356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15);
v___x_358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_356_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
lean_inc_ref(v_arg_255_);
lean_inc_ref(v_arg_257_);
lean_inc(v_head_272_);
v___x_359_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_head_272_, v_arg_257_, v_P_218_, v_arg_255_);
v___x_360_ = l_Lean_MessageData_ofExpr(v___x_359_);
v___x_361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_358_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v___x_347_, v___x_361_, v_a_225_, v_a_226_, v_a_227_, v_a_228_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_dec_ref(v___x_362_);
v___y_312_ = v_a_221_;
v___y_313_ = v_a_222_;
v___y_314_ = v_a_223_;
v___y_315_ = v_a_224_;
v___y_316_ = v_a_225_;
v___y_317_ = v_a_226_;
v___y_318_ = v_a_227_;
v___y_319_ = v_a_228_;
goto v___jp_311_;
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
lean_dec_ref(v___x_298_);
lean_del_object(v___x_291_);
lean_del_object(v___x_286_);
lean_dec_ref(v_focusHyp_280_);
lean_del_object(v___x_253_);
lean_dec(v_uniq_251_);
lean_dec(v_name_250_);
lean_dec_ref(v_p_241_);
v_a_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
v___jp_299_:
{
lean_object* v___x_301_; 
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 2, v_arg_255_);
v___x_301_ = v___x_253_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_name_250_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_uniq_251_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v_arg_255_);
v___x_301_ = v_reuseFailAlloc_310_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_302_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_301_);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v___x_298_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_303_);
v___x_305_ = v___x_286_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_303_);
v___x_305_ = v_reuseFailAlloc_309_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_307_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_305_);
v___x_307_ = v___x_291_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
v___jp_311_:
{
lean_object* v___x_320_; 
lean_inc_ref(v_arg_256_);
lean_inc_ref(v_focusHyp_280_);
v___x_320_ = l_Lean_Meta_isExprDefEq(v_focusHyp_280_, v_arg_256_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; uint8_t v___x_322_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref(v___x_320_);
v___x_322_ = lean_unbox(v_a_321_);
lean_dec(v_a_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec_ref(v___x_298_);
lean_del_object(v___x_291_);
lean_del_object(v___x_286_);
lean_del_object(v___x_253_);
lean_dec(v_uniq_251_);
lean_dec(v_name_250_);
v___x_323_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6);
v___x_324_ = l_Lean_MessageData_ofExpr(v_p_241_);
v___x_325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_323_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_325_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = l_Lean_MessageData_ofExpr(v_focusHyp_280_);
v___x_329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_327_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_329_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
else
{
lean_inc_ref(v_arg_255_);
lean_dec_ref(v_focusHyp_280_);
lean_dec_ref(v_p_241_);
goto v___jp_299_;
}
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec_ref(v___x_298_);
lean_del_object(v___x_291_);
lean_del_object(v___x_286_);
lean_dec_ref(v_focusHyp_280_);
lean_del_object(v___x_253_);
lean_dec(v_uniq_251_);
lean_dec(v_name_250_);
lean_dec_ref(v_p_241_);
v_a_339_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_320_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_320_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_del_object(v___x_286_);
lean_dec_ref(v_proof_282_);
lean_dec_ref(v_restHyps_281_);
lean_dec_ref(v_focusHyp_280_);
lean_del_object(v___x_253_);
lean_dec(v_uniq_251_);
lean_dec(v_name_250_);
lean_dec_ref(v_p_241_);
lean_dec_ref(v_P_218_);
v_a_373_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_289_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_289_);
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
else
{
lean_object* v___x_382_; lean_object* v___x_384_; 
lean_dec(v___x_283_);
lean_dec_ref(v_proof_282_);
lean_dec_ref(v_restHyps_281_);
lean_dec_ref(v_focusHyp_280_);
lean_del_object(v___x_253_);
lean_dec(v_uniq_251_);
lean_dec(v_name_250_);
lean_dec_ref(v_p_241_);
lean_dec(v_arg_220_);
lean_dec_ref(v_P_218_);
v___x_382_ = lean_box(0);
if (v_isShared_279_ == 0)
{
lean_ctor_set_tag(v___x_278_, 0);
lean_ctor_set(v___x_278_, 0, v___x_382_);
v___x_384_ = v___x_278_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
else
{
lean_object* v___x_387_; lean_object* v___x_389_; 
lean_dec(v___x_275_);
lean_del_object(v___x_253_);
lean_dec(v_uniq_251_);
lean_dec(v_name_250_);
lean_dec_ref(v_p_241_);
lean_dec(v_arg_220_);
lean_dec_ref(v_P_218_);
v___x_387_ = lean_box(0);
if (v_isShared_240_ == 0)
{
lean_ctor_set_tag(v___x_239_, 0);
lean_ctor_set(v___x_239_, 0, v___x_387_);
v___x_389_ = v___x_239_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
else
{
lean_del_object(v___x_253_);
lean_dec(v_uniq_251_);
lean_dec(v_name_250_);
lean_dec_ref(v_p_241_);
lean_del_object(v___x_239_);
lean_dec(v_arg_220_);
lean_dec_ref(v_QR_219_);
lean_dec_ref(v_P_218_);
goto v___jp_230_;
}
}
else
{
lean_del_object(v___x_253_);
lean_dec(v_uniq_251_);
lean_dec(v_name_250_);
lean_dec_ref(v_p_241_);
lean_del_object(v___x_239_);
lean_dec(v_arg_220_);
lean_dec_ref(v_QR_219_);
lean_dec_ref(v_P_218_);
goto v___jp_230_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_p_241_);
lean_del_object(v___x_239_);
lean_dec(v_val_237_);
lean_dec(v_arg_220_);
lean_dec_ref(v_QR_219_);
lean_dec_ref(v_P_218_);
goto v___jp_230_;
}
}
else
{
lean_dec_ref(v_p_241_);
lean_del_object(v___x_239_);
lean_dec(v_val_237_);
lean_dec(v_arg_220_);
lean_dec_ref(v_QR_219_);
lean_dec_ref(v_P_218_);
goto v___jp_230_;
}
}
else
{
lean_dec_ref(v_p_241_);
lean_del_object(v___x_239_);
lean_dec(v_val_237_);
lean_dec(v_arg_220_);
lean_dec_ref(v_QR_219_);
lean_dec_ref(v_P_218_);
goto v___jp_230_;
}
}
else
{
lean_dec_ref(v_p_241_);
lean_del_object(v___x_239_);
lean_dec(v_val_237_);
lean_dec(v_arg_220_);
lean_dec_ref(v_QR_219_);
lean_dec_ref(v_P_218_);
goto v___jp_230_;
}
}
else
{
lean_dec_ref(v_p_241_);
lean_del_object(v___x_239_);
lean_dec(v_val_237_);
lean_dec(v_arg_220_);
lean_dec_ref(v_QR_219_);
lean_dec_ref(v_P_218_);
goto v___jp_230_;
}
}
else
{
lean_dec_ref(v_p_241_);
lean_del_object(v___x_239_);
lean_dec(v_val_237_);
lean_dec(v_arg_220_);
lean_dec_ref(v_QR_219_);
lean_dec_ref(v_P_218_);
goto v___jp_230_;
}
}
else
{
lean_dec_ref(v_p_241_);
lean_del_object(v___x_239_);
lean_dec(v_val_237_);
lean_dec(v_arg_220_);
lean_dec_ref(v_QR_219_);
lean_dec_ref(v_P_218_);
goto v___jp_230_;
}
}
else
{
lean_dec_ref(v_p_241_);
lean_del_object(v___x_239_);
lean_dec(v_val_237_);
lean_dec(v_arg_220_);
lean_dec_ref(v_QR_219_);
lean_dec_ref(v_P_218_);
goto v___jp_230_;
}
}
else
{
lean_dec_ref(v_p_241_);
lean_del_object(v___x_239_);
lean_dec(v_val_237_);
lean_dec(v_arg_220_);
lean_dec_ref(v_QR_219_);
lean_dec_ref(v_P_218_);
goto v___jp_230_;
}
}
}
else
{
lean_object* v___x_394_; lean_object* v___x_395_; 
lean_dec(v___x_236_);
lean_dec(v_arg_220_);
lean_dec_ref(v_QR_219_);
lean_dec_ref(v_P_218_);
v___x_394_ = lean_box(0);
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
return v___x_395_;
}
}
v___jp_230_:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_box(0);
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___boxed(lean_object* v_P_396_, lean_object* v_QR_397_, lean_object* v_arg_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(v_P_396_, v_QR_397_, v_arg_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0(lean_object* v_00_u03b1_409_, lean_object* v_msg_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v_msg_410_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___boxed(lean_object* v_00_u03b1_421_, lean_object* v_msg_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0(v_00_u03b1_421_, v_msg_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1(lean_object* v_cls_433_, lean_object* v_msg_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v_cls_433_, v_msg_434_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___boxed(lean_object* v_cls_445_, lean_object* v_msg_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1(v_cls_445_, v_msg_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
return v_res_456_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0(void){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_instMonadEIO(lean_box(0));
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(lean_object* v_msg_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_toApplicative_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_568_; 
v___x_474_ = lean_obj_once(&l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0, &l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0);
v___x_475_ = l_StateRefT_x27_instMonad___redArg(v___x_474_);
v_toApplicative_476_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; 
v_unused_569_ = lean_ctor_get(v___x_475_, 1);
lean_dec(v_unused_569_);
v___x_478_ = v___x_475_;
v_isShared_479_ = v_isSharedCheck_568_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_toApplicative_476_);
lean_dec(v___x_475_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_568_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v_toFunctor_480_; lean_object* v_toSeq_481_; lean_object* v_toSeqLeft_482_; lean_object* v_toSeqRight_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_566_; 
v_toFunctor_480_ = lean_ctor_get(v_toApplicative_476_, 0);
v_toSeq_481_ = lean_ctor_get(v_toApplicative_476_, 2);
v_toSeqLeft_482_ = lean_ctor_get(v_toApplicative_476_, 3);
v_toSeqRight_483_ = lean_ctor_get(v_toApplicative_476_, 4);
v_isSharedCheck_566_ = !lean_is_exclusive(v_toApplicative_476_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; 
v_unused_567_ = lean_ctor_get(v_toApplicative_476_, 1);
lean_dec(v_unused_567_);
v___x_485_ = v_toApplicative_476_;
v_isShared_486_ = v_isSharedCheck_566_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_toSeqRight_483_);
lean_inc(v_toSeqLeft_482_);
lean_inc(v_toSeq_481_);
lean_inc(v_toFunctor_480_);
lean_dec(v_toApplicative_476_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_566_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___f_487_; lean_object* v___f_488_; lean_object* v___f_489_; lean_object* v___f_490_; lean_object* v___x_491_; lean_object* v___f_492_; lean_object* v___f_493_; lean_object* v___f_494_; lean_object* v___x_496_; 
v___f_487_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__1));
v___f_488_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__2));
lean_inc_ref(v_toFunctor_480_);
v___f_489_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_489_, 0, v_toFunctor_480_);
v___f_490_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_490_, 0, v_toFunctor_480_);
v___x_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_491_, 0, v___f_489_);
lean_ctor_set(v___x_491_, 1, v___f_490_);
v___f_492_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_492_, 0, v_toSeqRight_483_);
v___f_493_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_493_, 0, v_toSeqLeft_482_);
v___f_494_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_494_, 0, v_toSeq_481_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 4, v___f_492_);
lean_ctor_set(v___x_485_, 3, v___f_493_);
lean_ctor_set(v___x_485_, 2, v___f_494_);
lean_ctor_set(v___x_485_, 1, v___f_487_);
lean_ctor_set(v___x_485_, 0, v___x_491_);
v___x_496_ = v___x_485_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v___f_487_);
lean_ctor_set(v_reuseFailAlloc_565_, 2, v___f_494_);
lean_ctor_set(v_reuseFailAlloc_565_, 3, v___f_493_);
lean_ctor_set(v_reuseFailAlloc_565_, 4, v___f_492_);
v___x_496_ = v_reuseFailAlloc_565_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_498_; 
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v___f_488_);
lean_ctor_set(v___x_478_, 0, v___x_496_);
v___x_498_ = v___x_478_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v___f_488_);
v___x_498_ = v_reuseFailAlloc_564_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_499_; lean_object* v_toApplicative_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_562_; 
v___x_499_ = l_StateRefT_x27_instMonad___redArg(v___x_498_);
v_toApplicative_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; 
v_unused_563_ = lean_ctor_get(v___x_499_, 1);
lean_dec(v_unused_563_);
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_562_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_toApplicative_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_562_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v_toFunctor_504_; lean_object* v_toSeq_505_; lean_object* v_toSeqLeft_506_; lean_object* v_toSeqRight_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_560_; 
v_toFunctor_504_ = lean_ctor_get(v_toApplicative_500_, 0);
v_toSeq_505_ = lean_ctor_get(v_toApplicative_500_, 2);
v_toSeqLeft_506_ = lean_ctor_get(v_toApplicative_500_, 3);
v_toSeqRight_507_ = lean_ctor_get(v_toApplicative_500_, 4);
v_isSharedCheck_560_ = !lean_is_exclusive(v_toApplicative_500_);
if (v_isSharedCheck_560_ == 0)
{
lean_object* v_unused_561_; 
v_unused_561_ = lean_ctor_get(v_toApplicative_500_, 1);
lean_dec(v_unused_561_);
v___x_509_ = v_toApplicative_500_;
v_isShared_510_ = v_isSharedCheck_560_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_toSeqRight_507_);
lean_inc(v_toSeqLeft_506_);
lean_inc(v_toSeq_505_);
lean_inc(v_toFunctor_504_);
lean_dec(v_toApplicative_500_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_560_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___f_511_; lean_object* v___f_512_; lean_object* v___f_513_; lean_object* v___f_514_; lean_object* v___x_515_; lean_object* v___f_516_; lean_object* v___f_517_; lean_object* v___f_518_; lean_object* v___x_520_; 
v___f_511_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__3));
v___f_512_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__4));
lean_inc_ref(v_toFunctor_504_);
v___f_513_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_513_, 0, v_toFunctor_504_);
v___f_514_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_514_, 0, v_toFunctor_504_);
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v___f_513_);
lean_ctor_set(v___x_515_, 1, v___f_514_);
v___f_516_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_516_, 0, v_toSeqRight_507_);
v___f_517_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_517_, 0, v_toSeqLeft_506_);
v___f_518_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_518_, 0, v_toSeq_505_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 4, v___f_516_);
lean_ctor_set(v___x_509_, 3, v___f_517_);
lean_ctor_set(v___x_509_, 2, v___f_518_);
lean_ctor_set(v___x_509_, 1, v___f_511_);
lean_ctor_set(v___x_509_, 0, v___x_515_);
v___x_520_ = v___x_509_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v___f_511_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v___f_518_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v___f_517_);
lean_ctor_set(v_reuseFailAlloc_559_, 4, v___f_516_);
v___x_520_ = v_reuseFailAlloc_559_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_522_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 1, v___f_512_);
lean_ctor_set(v___x_502_, 0, v___x_520_);
v___x_522_ = v___x_502_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v___f_512_);
v___x_522_ = v_reuseFailAlloc_558_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v_toApplicative_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_556_; 
v___x_523_ = l_StateRefT_x27_instMonad___redArg(v___x_522_);
v_toApplicative_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; 
v_unused_557_ = lean_ctor_get(v___x_523_, 1);
lean_dec(v_unused_557_);
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_556_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_toApplicative_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_556_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v_toFunctor_528_; lean_object* v_toSeq_529_; lean_object* v_toSeqLeft_530_; lean_object* v_toSeqRight_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_554_; 
v_toFunctor_528_ = lean_ctor_get(v_toApplicative_524_, 0);
v_toSeq_529_ = lean_ctor_get(v_toApplicative_524_, 2);
v_toSeqLeft_530_ = lean_ctor_get(v_toApplicative_524_, 3);
v_toSeqRight_531_ = lean_ctor_get(v_toApplicative_524_, 4);
v_isSharedCheck_554_ = !lean_is_exclusive(v_toApplicative_524_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; 
v_unused_555_ = lean_ctor_get(v_toApplicative_524_, 1);
lean_dec(v_unused_555_);
v___x_533_ = v_toApplicative_524_;
v_isShared_534_ = v_isSharedCheck_554_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_toSeqRight_531_);
lean_inc(v_toSeqLeft_530_);
lean_inc(v_toSeq_529_);
lean_inc(v_toFunctor_528_);
lean_dec(v_toApplicative_524_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_554_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___f_535_; lean_object* v___f_536_; lean_object* v___f_537_; lean_object* v___f_538_; lean_object* v___x_539_; lean_object* v___f_540_; lean_object* v___f_541_; lean_object* v___f_542_; lean_object* v___x_544_; 
v___f_535_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__5));
v___f_536_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__6));
lean_inc_ref(v_toFunctor_528_);
v___f_537_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_537_, 0, v_toFunctor_528_);
v___f_538_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_538_, 0, v_toFunctor_528_);
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v___f_537_);
lean_ctor_set(v___x_539_, 1, v___f_538_);
v___f_540_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_540_, 0, v_toSeqRight_531_);
v___f_541_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_541_, 0, v_toSeqLeft_530_);
v___f_542_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_542_, 0, v_toSeq_529_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 4, v___f_540_);
lean_ctor_set(v___x_533_, 3, v___f_541_);
lean_ctor_set(v___x_533_, 2, v___f_542_);
lean_ctor_set(v___x_533_, 1, v___f_535_);
lean_ctor_set(v___x_533_, 0, v___x_539_);
v___x_544_ = v___x_533_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v___f_535_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v___f_542_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v___f_541_);
lean_ctor_set(v_reuseFailAlloc_553_, 4, v___f_540_);
v___x_544_ = v_reuseFailAlloc_553_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_546_; 
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 1, v___f_536_);
lean_ctor_set(v___x_526_, 0, v___x_544_);
v___x_546_ = v___x_526_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v___f_536_);
v___x_546_ = v_reuseFailAlloc_552_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_10928__overap_550_; lean_object* v___x_551_; 
v___x_547_ = l_StateRefT_x27_instMonad___redArg(v___x_546_);
v___x_548_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_548_, 0, lean_box(0));
lean_closure_set(v___x_548_, 1, lean_box(0));
lean_closure_set(v___x_548_, 2, v___x_547_);
v___x_549_ = l_OptionT_instInhabitedOfPure___redArg(v___x_548_);
v___x_10928__overap_550_ = lean_panic_fn_borrowed(v___x_549_, v_msg_464_);
lean_dec(v___x_549_);
lean_inc(v___y_472_);
lean_inc_ref(v___y_471_);
lean_inc(v___y_470_);
lean_inc_ref(v___y_469_);
lean_inc(v___y_468_);
lean_inc_ref(v___y_467_);
lean_inc(v___y_466_);
lean_inc_ref(v___y_465_);
v___x_551_ = lean_apply_9(v___x_10928__overap_550_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, lean_box(0));
return v___x_551_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___boxed(lean_object* v_msg_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(v_msg_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
return v_res_580_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_box(0);
v___x_582_ = l_Lean_mkSort(v___x_581_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0);
v___x_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__9));
v___x_611_ = l_Lean_stringToMessageData(v___x_610_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_630_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__17));
v___x_631_ = lean_unsigned_to_nat(37u);
v___x_632_ = lean_unsigned_to_nat(45u);
v___x_633_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__16));
v___x_634_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15));
v___x_635_ = l_mkPanicMessageWithDecl(v___x_634_, v___x_633_, v___x_632_, v___x_631_, v___x_630_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(lean_object* v_P_636_, lean_object* v_QR_637_, lean_object* v_arg_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_QR_637_);
if (lean_obj_tag(v___x_651_) == 1)
{
lean_object* v_val_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_829_; 
v_val_652_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_829_ == 0)
{
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_829_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_val_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_829_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v_p_656_; 
v_p_656_ = lean_ctor_get(v_val_652_, 2);
lean_inc_ref(v_p_656_);
if (lean_obj_tag(v_p_656_) == 5)
{
lean_object* v_name_657_; lean_object* v_uniq_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_827_; 
v_name_657_ = lean_ctor_get(v_val_652_, 0);
v_uniq_658_ = lean_ctor_get(v_val_652_, 1);
v_isSharedCheck_827_ = !lean_is_exclusive(v_val_652_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; 
v_unused_828_ = lean_ctor_get(v_val_652_, 2);
lean_dec(v_unused_828_);
v___x_660_ = v_val_652_;
v_isShared_661_ = v_isSharedCheck_827_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_uniq_658_);
lean_inc(v_name_657_);
lean_dec(v_val_652_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_827_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v_fn_662_; lean_object* v_arg_663_; lean_object* v___y_665_; 
v_fn_662_ = lean_ctor_get(v_p_656_, 0);
v_arg_663_ = lean_ctor_get(v_p_656_, 1);
lean_inc_ref(v_arg_663_);
if (lean_obj_tag(v_fn_662_) == 5)
{
lean_object* v_fn_675_; 
v_fn_675_ = lean_ctor_get(v_fn_662_, 0);
if (lean_obj_tag(v_fn_675_) == 5)
{
lean_object* v_fn_676_; 
v_fn_676_ = lean_ctor_get(v_fn_675_, 0);
if (lean_obj_tag(v_fn_676_) == 4)
{
lean_object* v_declName_677_; 
v_declName_677_ = lean_ctor_get(v_fn_676_, 0);
if (lean_obj_tag(v_declName_677_) == 1)
{
lean_object* v_pre_678_; 
v_pre_678_ = lean_ctor_get(v_declName_677_, 0);
if (lean_obj_tag(v_pre_678_) == 1)
{
lean_object* v_pre_679_; 
v_pre_679_ = lean_ctor_get(v_pre_678_, 0);
if (lean_obj_tag(v_pre_679_) == 1)
{
lean_object* v_pre_680_; 
v_pre_680_ = lean_ctor_get(v_pre_679_, 0);
if (lean_obj_tag(v_pre_680_) == 1)
{
lean_object* v_pre_681_; 
v_pre_681_ = lean_ctor_get(v_pre_680_, 0);
if (lean_obj_tag(v_pre_681_) == 0)
{
lean_object* v_arg_682_; lean_object* v_arg_683_; lean_object* v_us_684_; lean_object* v_str_685_; lean_object* v_str_686_; lean_object* v_str_687_; lean_object* v_str_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v_arg_682_ = lean_ctor_get(v_fn_662_, 1);
lean_inc_ref(v_arg_682_);
v_arg_683_ = lean_ctor_get(v_fn_675_, 1);
lean_inc_ref(v_arg_683_);
v_us_684_ = lean_ctor_get(v_fn_676_, 1);
v_str_685_ = lean_ctor_get(v_declName_677_, 1);
v_str_686_ = lean_ctor_get(v_pre_678_, 1);
v_str_687_ = lean_ctor_get(v_pre_679_, 1);
v_str_688_ = lean_ctor_get(v_pre_680_, 1);
v___x_689_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_690_ = lean_string_dec_eq(v_str_688_, v___x_689_);
if (v___x_690_ == 0)
{
lean_dec_ref(v_arg_683_);
lean_dec_ref(v_arg_682_);
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec_ref(v_p_656_);
lean_dec(v_name_657_);
lean_del_object(v___x_654_);
lean_dec(v_arg_638_);
lean_dec_ref(v_P_636_);
goto v___jp_648_;
}
else
{
lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_691_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_692_ = lean_string_dec_eq(v_str_687_, v___x_691_);
if (v___x_692_ == 0)
{
lean_dec_ref(v_arg_683_);
lean_dec_ref(v_arg_682_);
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec_ref(v_p_656_);
lean_dec(v_name_657_);
lean_del_object(v___x_654_);
lean_dec(v_arg_638_);
lean_dec_ref(v_P_636_);
goto v___jp_648_;
}
else
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_694_ = lean_string_dec_eq(v_str_686_, v___x_693_);
if (v___x_694_ == 0)
{
lean_dec_ref(v_arg_683_);
lean_dec_ref(v_arg_682_);
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec_ref(v_p_656_);
lean_dec(v_name_657_);
lean_del_object(v___x_654_);
lean_dec(v_arg_638_);
lean_dec_ref(v_P_636_);
goto v___jp_648_;
}
else
{
lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_695_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__2));
v___x_696_ = lean_string_dec_eq(v_str_685_, v___x_695_);
if (v___x_696_ == 0)
{
lean_dec_ref(v_arg_683_);
lean_dec_ref(v_arg_682_);
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec_ref(v_p_656_);
lean_dec(v_name_657_);
lean_del_object(v___x_654_);
lean_dec(v_arg_638_);
lean_dec_ref(v_P_636_);
goto v___jp_648_;
}
else
{
if (lean_obj_tag(v_us_684_) == 1)
{
lean_object* v_tail_697_; 
v_tail_697_ = lean_ctor_get(v_us_684_, 1);
if (lean_obj_tag(v_tail_697_) == 0)
{
lean_object* v_head_698_; lean_object* v___x_699_; uint8_t v___x_700_; lean_object* v___x_701_; 
v_head_698_ = lean_ctor_get(v_us_684_, 0);
lean_inc(v_head_698_);
v___x_699_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1);
v___x_700_ = 0;
v___x_701_ = l_Lean_Meta_mkFreshExprMVar(v___x_699_, v___x_700_, v_pre_681_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc_n(v_a_702_, 2);
lean_dec_ref(v___x_701_);
v___x_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_703_, 0, v_a_702_);
v___x_704_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2));
v___x_705_ = lean_box(0);
v___x_706_ = l_Lean_Elab_Tactic_elabTermWithHoles(v_arg_638_, v___x_703_, v___x_704_, v___x_696_, v___x_705_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v_fst_708_; lean_object* v_snd_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_803_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref(v___x_706_);
v_fst_708_ = lean_ctor_get(v_a_707_, 0);
v_snd_709_ = lean_ctor_get(v_a_707_, 1);
v_isSharedCheck_803_ = !lean_is_exclusive(v_a_707_);
if (v_isSharedCheck_803_ == 0)
{
v___x_711_ = v_a_707_;
v_isShared_712_ = v_isSharedCheck_803_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_snd_709_);
lean_inc(v_fst_708_);
lean_dec(v_a_707_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_803_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_713_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4));
lean_inc_ref(v_us_684_);
v___x_714_ = l_Lean_mkConst(v___x_713_, v_us_684_);
lean_inc(v_a_702_);
lean_inc_ref(v_arg_682_);
lean_inc_ref(v_arg_683_);
v___x_715_ = l_Lean_mkApp3(v___x_714_, v_arg_683_, v_arg_682_, v_a_702_);
v___x_716_ = l_Lean_Meta_synthInstance_x3f(v___x_715_, v___x_705_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v_00_u03c6_719_; lean_object* v_h_u03c6_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref(v___x_716_);
if (lean_obj_tag(v_a_717_) == 1)
{
lean_object* v_val_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v_val_788_ = lean_ctor_get(v_a_717_, 0);
lean_inc(v_val_788_);
lean_dec_ref(v_a_717_);
v___x_789_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12));
lean_inc_ref_n(v_us_684_, 2);
v___x_790_ = l_Lean_mkConst(v___x_789_, v_us_684_);
lean_inc_ref_n(v_arg_682_, 2);
lean_inc_ref_n(v_arg_683_, 2);
v___x_791_ = l_Lean_mkApp5(v___x_790_, v_arg_683_, v_a_702_, v_arg_682_, v_val_788_, v_fst_708_);
v___x_792_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14));
v___x_793_ = l_Lean_mkConst(v___x_792_, v_us_684_);
v___x_794_ = l_Lean_mkAppB(v___x_793_, v_arg_683_, v_arg_682_);
v_00_u03c6_719_ = v___x_794_;
v_h_u03c6_720_ = v___x_791_;
v___y_721_ = v_a_640_;
v___y_722_ = v_a_643_;
v___y_723_ = v_a_644_;
v___y_724_ = v_a_645_;
v___y_725_ = v_a_646_;
goto v___jp_718_;
}
else
{
lean_dec(v_a_717_);
v_00_u03c6_719_ = v_a_702_;
v_h_u03c6_720_ = v_fst_708_;
v___y_721_ = v_a_640_;
v___y_722_ = v_a_643_;
v___y_723_ = v_a_644_;
v___y_724_ = v_a_645_;
v___y_725_ = v_a_646_;
goto v___jp_718_;
}
v___jp_718_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_726_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6));
lean_inc_ref(v_us_684_);
v___x_727_ = l_Lean_mkConst(v___x_726_, v_us_684_);
lean_inc_ref(v_arg_682_);
lean_inc_ref(v_arg_683_);
lean_inc_ref(v_00_u03c6_719_);
v___x_728_ = l_Lean_mkApp3(v___x_727_, v_00_u03c6_719_, v_arg_683_, v_arg_682_);
v___x_729_ = l_Lean_Meta_synthInstance_x3f(v___x_728_, v___x_705_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_779_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_779_ == 0)
{
v___x_732_ = v___x_729_;
v_isShared_733_ = v_isSharedCheck_779_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_729_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_779_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
if (lean_obj_tag(v_a_730_) == 1)
{
lean_object* v_val_734_; lean_object* v___x_735_; 
lean_del_object(v___x_732_);
v_val_734_ = lean_ctor_get(v_a_730_, 0);
lean_inc(v_val_734_);
lean_dec_ref(v_a_730_);
v___x_735_ = l_Lean_Elab_Tactic_pushGoals___redArg(v_snd_709_, v___y_721_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_options_736_; lean_object* v_inheritedTraceOptions_737_; uint8_t v_hasTrace_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec_ref(v___x_735_);
v_options_736_ = lean_ctor_get(v___y_724_, 2);
v_inheritedTraceOptions_737_ = lean_ctor_get(v___y_724_, 13);
v_hasTrace_738_ = lean_ctor_get_uint8(v_options_736_, sizeof(void*)*1);
v___x_739_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8));
lean_inc_ref(v_us_684_);
v___x_740_ = l_Lean_mkConst(v___x_739_, v_us_684_);
lean_inc_ref(v_arg_663_);
lean_inc_ref(v_arg_682_);
lean_inc_ref(v_P_636_);
lean_inc_ref(v_arg_683_);
v___x_741_ = l_Lean_mkApp7(v___x_740_, v_arg_683_, v_00_u03c6_719_, v_P_636_, v_arg_682_, v_arg_663_, v_val_734_, v_h_u03c6_720_);
if (v_hasTrace_738_ == 0)
{
lean_del_object(v___x_711_);
lean_dec(v_head_698_);
lean_dec_ref(v_arg_683_);
lean_dec_ref(v_arg_682_);
lean_dec_ref(v_p_656_);
lean_dec_ref(v_P_636_);
v___y_665_ = v___x_741_;
goto v___jp_664_;
}
else
{
lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_742_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_743_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11);
v___x_744_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_737_, v_options_736_, v___x_743_);
if (v___x_744_ == 0)
{
lean_del_object(v___x_711_);
lean_dec(v_head_698_);
lean_dec_ref(v_arg_683_);
lean_dec_ref(v_arg_682_);
lean_dec_ref(v_p_656_);
lean_dec_ref(v_P_636_);
v___y_665_ = v___x_741_;
goto v___jp_664_;
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_745_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10);
v___x_746_ = l_Lean_MessageData_ofExpr(v_p_656_);
if (v_isShared_712_ == 0)
{
lean_ctor_set_tag(v___x_711_, 7);
lean_ctor_set(v___x_711_, 1, v___x_746_);
lean_ctor_set(v___x_711_, 0, v___x_745_);
v___x_748_ = v___x_711_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v___x_746_);
v___x_748_ = v_reuseFailAlloc_767_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_749_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = l_Lean_MessageData_ofExpr(v_arg_682_);
v___x_752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_750_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15);
v___x_754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_752_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
lean_inc_ref(v_arg_663_);
v___x_755_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_head_698_, v_arg_683_, v_P_636_, v_arg_663_);
v___x_756_ = l_Lean_MessageData_ofExpr(v___x_755_);
v___x_757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_754_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v___x_742_, v___x_757_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_dec_ref(v___x_758_);
v___y_665_ = v___x_741_;
goto v___jp_664_;
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec_ref(v___x_741_);
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec(v_name_657_);
lean_del_object(v___x_654_);
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec(v_val_734_);
lean_dec_ref(v_h_u03c6_720_);
lean_dec_ref(v_00_u03c6_719_);
lean_del_object(v___x_711_);
lean_dec(v_head_698_);
lean_dec_ref(v_arg_683_);
lean_dec_ref(v_arg_682_);
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec_ref(v_p_656_);
lean_dec(v_name_657_);
lean_del_object(v___x_654_);
lean_dec_ref(v_P_636_);
v_a_768_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_735_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_735_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
else
{
lean_object* v___x_777_; 
lean_dec(v_a_730_);
lean_dec_ref(v_h_u03c6_720_);
lean_dec_ref(v_00_u03c6_719_);
lean_del_object(v___x_711_);
lean_dec(v_snd_709_);
lean_dec(v_head_698_);
lean_dec_ref(v_arg_683_);
lean_dec_ref(v_arg_682_);
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec_ref(v_p_656_);
lean_dec(v_name_657_);
lean_del_object(v___x_654_);
lean_dec_ref(v_P_636_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v___x_705_);
v___x_777_ = v___x_732_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_705_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec_ref(v_h_u03c6_720_);
lean_dec_ref(v_00_u03c6_719_);
lean_del_object(v___x_711_);
lean_dec(v_snd_709_);
lean_dec(v_head_698_);
lean_dec_ref(v_arg_683_);
lean_dec_ref(v_arg_682_);
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec_ref(v_p_656_);
lean_dec(v_name_657_);
lean_del_object(v___x_654_);
lean_dec_ref(v_P_636_);
v_a_780_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_729_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_729_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_del_object(v___x_711_);
lean_dec(v_snd_709_);
lean_dec(v_fst_708_);
lean_dec(v_a_702_);
lean_dec(v_head_698_);
lean_dec_ref(v_arg_683_);
lean_dec_ref(v_arg_682_);
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec(v_name_657_);
lean_dec_ref(v_p_656_);
lean_del_object(v___x_654_);
lean_dec_ref(v_P_636_);
v_a_795_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_716_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_716_);
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
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_818_; 
lean_dec(v_a_702_);
lean_dec(v_head_698_);
lean_dec_ref(v_arg_683_);
lean_dec_ref(v_arg_682_);
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec(v_name_657_);
lean_dec_ref(v_p_656_);
lean_del_object(v___x_654_);
lean_dec_ref(v_P_636_);
v_a_804_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_818_ == 0)
{
v___x_806_ = v___x_706_;
v_isShared_807_ = v_isSharedCheck_818_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_706_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_818_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
uint8_t v___y_809_; uint8_t v___x_816_; 
v___x_816_ = l_Lean_Exception_isInterrupt(v_a_804_);
if (v___x_816_ == 0)
{
uint8_t v___x_817_; 
lean_inc(v_a_804_);
v___x_817_ = l_Lean_Exception_isRuntime(v_a_804_);
v___y_809_ = v___x_817_;
goto v___jp_808_;
}
else
{
v___y_809_ = v___x_816_;
goto v___jp_808_;
}
v___jp_808_:
{
if (v___y_809_ == 0)
{
lean_object* v___x_811_; 
lean_dec(v_a_804_);
if (v_isShared_807_ == 0)
{
lean_ctor_set_tag(v___x_806_, 0);
lean_ctor_set(v___x_806_, 0, v___x_705_);
v___x_811_ = v___x_806_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_705_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
else
{
lean_object* v___x_814_; 
if (v_isShared_807_ == 0)
{
v___x_814_ = v___x_806_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_804_);
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
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec(v_head_698_);
lean_dec_ref(v_arg_683_);
lean_dec_ref(v_arg_682_);
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec_ref(v_p_656_);
lean_dec(v_name_657_);
lean_del_object(v___x_654_);
lean_dec(v_arg_638_);
lean_dec_ref(v_P_636_);
v_a_819_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_701_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_701_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_dec_ref(v_arg_683_);
lean_dec_ref(v_arg_682_);
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec_ref(v_p_656_);
lean_dec(v_name_657_);
lean_del_object(v___x_654_);
lean_dec(v_arg_638_);
lean_dec_ref(v_P_636_);
goto v___jp_648_;
}
}
else
{
lean_dec_ref(v_arg_683_);
lean_dec_ref(v_arg_682_);
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec_ref(v_p_656_);
lean_dec(v_name_657_);
lean_del_object(v___x_654_);
lean_dec(v_arg_638_);
lean_dec_ref(v_P_636_);
goto v___jp_648_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec_ref(v_p_656_);
lean_dec(v_name_657_);
lean_del_object(v___x_654_);
lean_dec(v_arg_638_);
lean_dec_ref(v_P_636_);
goto v___jp_648_;
}
}
else
{
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec_ref(v_p_656_);
lean_dec(v_name_657_);
lean_del_object(v___x_654_);
lean_dec(v_arg_638_);
lean_dec_ref(v_P_636_);
goto v___jp_648_;
}
}
else
{
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec_ref(v_p_656_);
lean_dec(v_name_657_);
lean_del_object(v___x_654_);
lean_dec(v_arg_638_);
lean_dec_ref(v_P_636_);
goto v___jp_648_;
}
}
else
{
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec_ref(v_p_656_);
lean_dec(v_name_657_);
lean_del_object(v___x_654_);
lean_dec(v_arg_638_);
lean_dec_ref(v_P_636_);
goto v___jp_648_;
}
}
else
{
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec_ref(v_p_656_);
lean_dec(v_name_657_);
lean_del_object(v___x_654_);
lean_dec(v_arg_638_);
lean_dec_ref(v_P_636_);
goto v___jp_648_;
}
}
else
{
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec_ref(v_p_656_);
lean_dec(v_name_657_);
lean_del_object(v___x_654_);
lean_dec(v_arg_638_);
lean_dec_ref(v_P_636_);
goto v___jp_648_;
}
}
else
{
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec_ref(v_p_656_);
lean_dec(v_name_657_);
lean_del_object(v___x_654_);
lean_dec(v_arg_638_);
lean_dec_ref(v_P_636_);
goto v___jp_648_;
}
}
else
{
lean_dec_ref(v_arg_663_);
lean_del_object(v___x_660_);
lean_dec(v_uniq_658_);
lean_dec_ref(v_p_656_);
lean_dec(v_name_657_);
lean_del_object(v___x_654_);
lean_dec(v_arg_638_);
lean_dec_ref(v_P_636_);
goto v___jp_648_;
}
v___jp_664_:
{
lean_object* v___x_667_; 
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 2, v_arg_663_);
v___x_667_ = v___x_660_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_name_657_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_uniq_658_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_arg_663_);
v___x_667_ = v_reuseFailAlloc_674_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_668_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_667_);
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
lean_ctor_set(v___x_669_, 1, v___y_665_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_669_);
v___x_671_ = v___x_654_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_669_);
v___x_671_ = v_reuseFailAlloc_673_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; 
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_656_);
lean_del_object(v___x_654_);
lean_dec(v_val_652_);
lean_dec(v_arg_638_);
lean_dec_ref(v_P_636_);
goto v___jp_648_;
}
}
}
else
{
lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec(v___x_651_);
lean_dec(v_arg_638_);
lean_dec_ref(v_P_636_);
v___x_830_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18);
v___x_831_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(v___x_830_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
return v___x_831_;
}
v___jp_648_:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_box(0);
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___boxed(lean_object* v_P_832_, lean_object* v_QR_833_, lean_object* v_arg_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(v_P_832_, v_QR_833_, v_arg_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
return v_res_844_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__2));
v___x_855_ = l_Lean_stringToMessageData(v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_858_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__5));
v___x_859_ = lean_unsigned_to_nat(36u);
v___x_860_ = lean_unsigned_to_nat(73u);
v___x_861_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__4));
v___x_862_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15));
v___x_863_ = l_mkPanicMessageWithDecl(v___x_862_, v___x_861_, v___x_860_, v___x_859_, v___x_858_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(lean_object* v_P_864_, lean_object* v_00_u03a8_865_, lean_object* v_arg_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_00_u03a8_865_);
if (lean_obj_tag(v___x_879_) == 1)
{
lean_object* v_val_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_1014_; 
v_val_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_1014_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_val_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_1014_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v_p_884_; 
v_p_884_ = lean_ctor_get(v_val_880_, 2);
lean_inc_ref(v_p_884_);
if (lean_obj_tag(v_p_884_) == 5)
{
lean_object* v_fn_885_; 
v_fn_885_ = lean_ctor_get(v_p_884_, 0);
if (lean_obj_tag(v_fn_885_) == 5)
{
lean_object* v_fn_886_; 
v_fn_886_ = lean_ctor_get(v_fn_885_, 0);
if (lean_obj_tag(v_fn_886_) == 5)
{
lean_object* v_fn_887_; 
v_fn_887_ = lean_ctor_get(v_fn_886_, 0);
if (lean_obj_tag(v_fn_887_) == 4)
{
lean_object* v_declName_888_; 
v_declName_888_ = lean_ctor_get(v_fn_887_, 0);
if (lean_obj_tag(v_declName_888_) == 1)
{
lean_object* v_pre_889_; 
v_pre_889_ = lean_ctor_get(v_declName_888_, 0);
if (lean_obj_tag(v_pre_889_) == 1)
{
lean_object* v_pre_890_; 
v_pre_890_ = lean_ctor_get(v_pre_889_, 0);
if (lean_obj_tag(v_pre_890_) == 1)
{
lean_object* v_pre_891_; 
v_pre_891_ = lean_ctor_get(v_pre_890_, 0);
if (lean_obj_tag(v_pre_891_) == 1)
{
lean_object* v_pre_892_; 
v_pre_892_ = lean_ctor_get(v_pre_891_, 0);
if (lean_obj_tag(v_pre_892_) == 0)
{
lean_object* v_name_893_; lean_object* v_uniq_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_1012_; 
v_name_893_ = lean_ctor_get(v_val_880_, 0);
v_uniq_894_ = lean_ctor_get(v_val_880_, 1);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_val_880_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v_val_880_, 2);
lean_dec(v_unused_1013_);
v___x_896_ = v_val_880_;
v_isShared_897_ = v_isSharedCheck_1012_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_uniq_894_);
lean_inc(v_name_893_);
lean_dec(v_val_880_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_1012_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_arg_898_; lean_object* v_arg_899_; lean_object* v_arg_900_; lean_object* v_us_901_; lean_object* v_str_902_; lean_object* v_str_903_; lean_object* v_str_904_; lean_object* v_str_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v_arg_898_ = lean_ctor_get(v_p_884_, 1);
v_arg_899_ = lean_ctor_get(v_fn_885_, 1);
lean_inc_ref(v_arg_899_);
v_arg_900_ = lean_ctor_get(v_fn_886_, 1);
v_us_901_ = lean_ctor_get(v_fn_887_, 1);
v_str_902_ = lean_ctor_get(v_declName_888_, 1);
v_str_903_ = lean_ctor_get(v_pre_889_, 1);
v_str_904_ = lean_ctor_get(v_pre_890_, 1);
v_str_905_ = lean_ctor_get(v_pre_891_, 1);
v___x_906_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_907_ = lean_string_dec_eq(v_str_905_, v___x_906_);
if (v___x_907_ == 0)
{
lean_dec_ref(v_arg_899_);
lean_del_object(v___x_896_);
lean_dec(v_uniq_894_);
lean_dec(v_name_893_);
lean_dec_ref(v_p_884_);
lean_del_object(v___x_882_);
lean_dec(v_arg_866_);
lean_dec_ref(v_P_864_);
goto v___jp_876_;
}
else
{
lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_908_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_909_ = lean_string_dec_eq(v_str_904_, v___x_908_);
if (v___x_909_ == 0)
{
lean_dec_ref(v_arg_899_);
lean_del_object(v___x_896_);
lean_dec(v_uniq_894_);
lean_dec(v_name_893_);
lean_dec_ref(v_p_884_);
lean_del_object(v___x_882_);
lean_dec(v_arg_866_);
lean_dec_ref(v_P_864_);
goto v___jp_876_;
}
else
{
lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_910_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_911_ = lean_string_dec_eq(v_str_903_, v___x_910_);
if (v___x_911_ == 0)
{
lean_dec_ref(v_arg_899_);
lean_del_object(v___x_896_);
lean_dec(v_uniq_894_);
lean_dec(v_name_893_);
lean_dec_ref(v_p_884_);
lean_del_object(v___x_882_);
lean_dec(v_arg_866_);
lean_dec_ref(v_P_864_);
goto v___jp_876_;
}
else
{
lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_912_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__0));
v___x_913_ = lean_string_dec_eq(v_str_902_, v___x_912_);
if (v___x_913_ == 0)
{
lean_dec_ref(v_arg_899_);
lean_del_object(v___x_896_);
lean_dec(v_uniq_894_);
lean_dec(v_name_893_);
lean_dec_ref(v_p_884_);
lean_del_object(v___x_882_);
lean_dec(v_arg_866_);
lean_dec_ref(v_P_864_);
goto v___jp_876_;
}
else
{
if (lean_obj_tag(v_us_901_) == 1)
{
lean_object* v_tail_914_; 
v_tail_914_ = lean_ctor_get(v_us_901_, 1);
lean_inc(v_tail_914_);
if (lean_obj_tag(v_tail_914_) == 1)
{
lean_object* v_tail_915_; 
v_tail_915_ = lean_ctor_get(v_tail_914_, 1);
if (lean_obj_tag(v_tail_915_) == 0)
{
lean_object* v_head_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_1010_; 
v_head_916_ = lean_ctor_get(v_tail_914_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_tail_914_);
if (v_isSharedCheck_1010_ == 0)
{
lean_object* v_unused_1011_; 
v_unused_1011_ = lean_ctor_get(v_tail_914_, 1);
lean_dec(v_unused_1011_);
v___x_918_ = v_tail_914_;
v_isShared_919_ = v_isSharedCheck_1010_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_head_916_);
lean_dec(v_tail_914_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_1010_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
lean_inc_ref(v_arg_900_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v_arg_900_);
v___x_921_ = v___x_882_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_arg_900_);
v___x_921_ = v_reuseFailAlloc_1009_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2));
v___x_923_ = lean_box(0);
v___x_924_ = l_Lean_Elab_Tactic_elabTermWithHoles(v_arg_866_, v___x_921_, v___x_922_, v___x_913_, v___x_923_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v_fst_926_; lean_object* v_snd_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_993_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref(v___x_924_);
v_fst_926_ = lean_ctor_get(v_a_925_, 0);
v_snd_927_ = lean_ctor_get(v_a_925_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v_a_925_);
if (v_isSharedCheck_993_ == 0)
{
v___x_929_ = v_a_925_;
v_isShared_930_ = v_isSharedCheck_993_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_snd_927_);
lean_inc(v_fst_926_);
lean_dec(v_a_925_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_993_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_Elab_Tactic_pushGoals___redArg(v_snd_927_, v_a_868_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_983_; 
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; 
v_unused_984_ = lean_ctor_get(v___x_931_, 0);
lean_dec(v_unused_984_);
v___x_933_ = v___x_931_;
v_isShared_934_ = v_isSharedCheck_983_;
goto v_resetjp_932_;
}
else
{
lean_dec(v___x_931_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_983_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_options_935_; lean_object* v_inheritedTraceOptions_936_; uint8_t v_hasTrace_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_options_935_ = lean_ctor_get(v_a_873_, 2);
v_inheritedTraceOptions_936_ = lean_ctor_get(v_a_873_, 13);
v_hasTrace_937_ = lean_ctor_get_uint8(v_options_935_, sizeof(void*)*1);
v___x_938_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1));
lean_inc_ref(v_us_901_);
v___x_939_ = l_Lean_mkConst(v___x_938_, v_us_901_);
lean_inc_n(v_fst_926_, 2);
lean_inc_ref(v_P_864_);
lean_inc_ref_n(v_arg_898_, 2);
lean_inc_ref(v_arg_899_);
lean_inc_ref(v_arg_900_);
v___x_940_ = l_Lean_mkApp5(v___x_939_, v_arg_900_, v_arg_899_, v_arg_898_, v_P_864_, v_fst_926_);
v___x_941_ = lean_unsigned_to_nat(1u);
v___x_942_ = lean_mk_empty_array_with_capacity(v___x_941_);
v___x_943_ = lean_array_push(v___x_942_, v_fst_926_);
v___x_944_ = l_Lean_Expr_beta(v_arg_898_, v___x_943_);
if (v_hasTrace_937_ == 0)
{
lean_dec(v_fst_926_);
lean_del_object(v___x_918_);
lean_dec(v_head_916_);
lean_dec_ref(v_arg_899_);
lean_dec_ref(v_p_884_);
lean_dec_ref(v_P_864_);
goto v___jp_945_;
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_957_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_958_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11);
v___x_959_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_936_, v_options_935_, v___x_958_);
if (v___x_959_ == 0)
{
lean_dec(v_fst_926_);
lean_del_object(v___x_918_);
lean_dec(v_head_916_);
lean_dec_ref(v_arg_899_);
lean_dec_ref(v_p_884_);
lean_dec_ref(v_P_864_);
goto v___jp_945_;
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_960_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3);
v___x_961_ = l_Lean_MessageData_ofExpr(v_p_884_);
if (v_isShared_919_ == 0)
{
lean_ctor_set_tag(v___x_918_, 7);
lean_ctor_set(v___x_918_, 1, v___x_961_);
lean_ctor_set(v___x_918_, 0, v___x_960_);
v___x_963_ = v___x_918_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v___x_961_);
v___x_963_ = v_reuseFailAlloc_982_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_964_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = l_Lean_MessageData_ofExpr(v_fst_926_);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
lean_inc_ref(v___x_944_);
v___x_970_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_head_916_, v_arg_899_, v_P_864_, v___x_944_);
v___x_971_ = l_Lean_MessageData_ofExpr(v___x_970_);
v___x_972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_969_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v___x_957_, v___x_972_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_dec_ref(v___x_973_);
goto v___jp_945_;
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec_ref(v___x_944_);
lean_dec_ref(v___x_940_);
lean_del_object(v___x_933_);
lean_del_object(v___x_929_);
lean_del_object(v___x_896_);
lean_dec(v_uniq_894_);
lean_dec(v_name_893_);
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
}
v___jp_945_:
{
lean_object* v___x_947_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 2, v___x_944_);
v___x_947_ = v___x_896_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_name_893_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_uniq_894_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v___x_944_);
v___x_947_ = v_reuseFailAlloc_956_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_948_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_947_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v___x_940_);
lean_ctor_set(v___x_929_, 0, v___x_948_);
v___x_950_ = v___x_929_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v___x_940_);
v___x_950_ = v_reuseFailAlloc_955_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_951_);
v___x_953_ = v___x_933_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_del_object(v___x_929_);
lean_dec(v_fst_926_);
lean_del_object(v___x_918_);
lean_dec(v_head_916_);
lean_dec_ref(v_arg_899_);
lean_del_object(v___x_896_);
lean_dec(v_uniq_894_);
lean_dec(v_name_893_);
lean_dec_ref(v_p_884_);
lean_dec_ref(v_P_864_);
v_a_985_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_931_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_931_);
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
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1008_; 
lean_del_object(v___x_918_);
lean_dec(v_head_916_);
lean_dec_ref(v_arg_899_);
lean_del_object(v___x_896_);
lean_dec(v_uniq_894_);
lean_dec(v_name_893_);
lean_dec_ref(v_p_884_);
lean_dec_ref(v_P_864_);
v_a_994_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_996_ = v___x_924_;
v_isShared_997_ = v_isSharedCheck_1008_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_924_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1008_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
uint8_t v___y_999_; uint8_t v___x_1006_; 
v___x_1006_ = l_Lean_Exception_isInterrupt(v_a_994_);
if (v___x_1006_ == 0)
{
uint8_t v___x_1007_; 
lean_inc(v_a_994_);
v___x_1007_ = l_Lean_Exception_isRuntime(v_a_994_);
v___y_999_ = v___x_1007_;
goto v___jp_998_;
}
else
{
v___y_999_ = v___x_1006_;
goto v___jp_998_;
}
v___jp_998_:
{
if (v___y_999_ == 0)
{
lean_object* v___x_1001_; 
lean_dec(v_a_994_);
if (v_isShared_997_ == 0)
{
lean_ctor_set_tag(v___x_996_, 0);
lean_ctor_set(v___x_996_, 0, v___x_923_);
v___x_1001_ = v___x_996_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_923_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
else
{
lean_object* v___x_1004_; 
if (v_isShared_997_ == 0)
{
v___x_1004_ = v___x_996_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_994_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
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
lean_dec_ref(v_tail_914_);
lean_dec_ref(v_arg_899_);
lean_del_object(v___x_896_);
lean_dec(v_uniq_894_);
lean_dec(v_name_893_);
lean_dec_ref(v_p_884_);
lean_del_object(v___x_882_);
lean_dec(v_arg_866_);
lean_dec_ref(v_P_864_);
goto v___jp_876_;
}
}
else
{
lean_dec(v_tail_914_);
lean_dec_ref(v_arg_899_);
lean_del_object(v___x_896_);
lean_dec(v_uniq_894_);
lean_dec(v_name_893_);
lean_dec_ref(v_p_884_);
lean_del_object(v___x_882_);
lean_dec(v_arg_866_);
lean_dec_ref(v_P_864_);
goto v___jp_876_;
}
}
else
{
lean_dec_ref(v_arg_899_);
lean_del_object(v___x_896_);
lean_dec(v_uniq_894_);
lean_dec(v_name_893_);
lean_dec_ref(v_p_884_);
lean_del_object(v___x_882_);
lean_dec(v_arg_866_);
lean_dec_ref(v_P_864_);
goto v___jp_876_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_p_884_);
lean_del_object(v___x_882_);
lean_dec(v_val_880_);
lean_dec(v_arg_866_);
lean_dec_ref(v_P_864_);
goto v___jp_876_;
}
}
else
{
lean_dec_ref(v_p_884_);
lean_del_object(v___x_882_);
lean_dec(v_val_880_);
lean_dec(v_arg_866_);
lean_dec_ref(v_P_864_);
goto v___jp_876_;
}
}
else
{
lean_dec_ref(v_p_884_);
lean_del_object(v___x_882_);
lean_dec(v_val_880_);
lean_dec(v_arg_866_);
lean_dec_ref(v_P_864_);
goto v___jp_876_;
}
}
else
{
lean_dec_ref(v_p_884_);
lean_del_object(v___x_882_);
lean_dec(v_val_880_);
lean_dec(v_arg_866_);
lean_dec_ref(v_P_864_);
goto v___jp_876_;
}
}
else
{
lean_dec_ref(v_p_884_);
lean_del_object(v___x_882_);
lean_dec(v_val_880_);
lean_dec(v_arg_866_);
lean_dec_ref(v_P_864_);
goto v___jp_876_;
}
}
else
{
lean_dec_ref(v_p_884_);
lean_del_object(v___x_882_);
lean_dec(v_val_880_);
lean_dec(v_arg_866_);
lean_dec_ref(v_P_864_);
goto v___jp_876_;
}
}
else
{
lean_dec_ref(v_p_884_);
lean_del_object(v___x_882_);
lean_dec(v_val_880_);
lean_dec(v_arg_866_);
lean_dec_ref(v_P_864_);
goto v___jp_876_;
}
}
else
{
lean_dec_ref(v_p_884_);
lean_del_object(v___x_882_);
lean_dec(v_val_880_);
lean_dec(v_arg_866_);
lean_dec_ref(v_P_864_);
goto v___jp_876_;
}
}
else
{
lean_dec_ref(v_p_884_);
lean_del_object(v___x_882_);
lean_dec(v_val_880_);
lean_dec(v_arg_866_);
lean_dec_ref(v_P_864_);
goto v___jp_876_;
}
}
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
lean_dec(v___x_879_);
lean_dec(v_arg_866_);
lean_dec_ref(v_P_864_);
v___x_1015_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6);
v___x_1016_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(v___x_1015_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
return v___x_1016_;
}
v___jp_876_:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_box(0);
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
return v___x_878_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___boxed(lean_object* v_P_1017_, lean_object* v_00_u03a8_1018_, lean_object* v_arg_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(v_P_1017_, v_00_u03a8_1018_, v_arg_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
return v_res_1029_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1030_ = lean_box(0);
v___x_1031_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set(v___x_1032_, 1, v___x_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg(){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0);
v___x_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___boxed(lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0(lean_object* v_00_u03b1_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___boxed(lean_object* v_00_u03b1_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0(v_00_u03b1_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(lean_object* v_msg_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___f_1071_; lean_object* v___x_6226__overap_1072_; lean_object* v___x_1073_; 
v___f_1071_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3___closed__0));
v___x_6226__overap_1072_ = lean_panic_fn_borrowed(v___f_1071_, v_msg_1061_);
lean_inc(v___y_1069_);
lean_inc_ref(v___y_1068_);
lean_inc(v___y_1067_);
lean_inc_ref(v___y_1066_);
lean_inc(v___y_1065_);
lean_inc_ref(v___y_1064_);
lean_inc(v___y_1063_);
lean_inc_ref(v___y_1062_);
v___x_1073_ = lean_apply_9(v___x_6226__overap_1072_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, lean_box(0));
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3___boxed(lean_object* v_msg_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(v_msg_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0(lean_object* v_x_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v___x_1095_; 
lean_inc(v___y_1089_);
lean_inc_ref(v___y_1088_);
lean_inc(v___y_1087_);
lean_inc_ref(v___y_1086_);
v___x_1095_ = lean_apply_9(v_x_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, lean_box(0));
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0___boxed(lean_object* v_x_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0(v_x_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(lean_object* v_mvarId_1107_, lean_object* v_x_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v___f_1118_; lean_object* v___x_1119_; 
lean_inc(v___y_1112_);
lean_inc_ref(v___y_1111_);
lean_inc(v___y_1110_);
lean_inc_ref(v___y_1109_);
v___f_1118_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1118_, 0, v_x_1108_);
lean_closure_set(v___f_1118_, 1, v___y_1109_);
lean_closure_set(v___f_1118_, 2, v___y_1110_);
lean_closure_set(v___f_1118_, 3, v___y_1111_);
lean_closure_set(v___f_1118_, 4, v___y_1112_);
v___x_1119_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1107_, v___f_1118_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
if (lean_obj_tag(v___x_1119_) == 0)
{
return v___x_1119_;
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___boxed(lean_object* v_mvarId_1128_, lean_object* v_x_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_mvarId_1128_, v_x_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4(lean_object* v_00_u03b1_1140_, lean_object* v_mvarId_1141_, lean_object* v_x_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_mvarId_1141_, v_x_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___boxed(lean_object* v_00_u03b1_1153_, lean_object* v_mvarId_1154_, lean_object* v_x_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4(v_00_u03b1_1153_, v_mvarId_1154_, v_x_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0(lean_object* v___x_1168_, lean_object* v___x_1169_, lean_object* v___x_1170_, lean_object* v___x_1171_, lean_object* v___x_1172_, lean_object* v___x_1173_, lean_object* v___x_1174_, lean_object* v_fst_1175_, lean_object* v_fst_1176_, lean_object* v___x_1177_, lean_object* v_snd_1178_, lean_object* v_snd_1179_, lean_object* v_hgoal_1180_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1181_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__0));
v___x_1182_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__1));
v___x_1183_ = l_Lean_Name_mkStr5(v___x_1168_, v___x_1169_, v___x_1170_, v___x_1181_, v___x_1182_);
v___x_1184_ = l_Lean_mkConst(v___x_1183_, v___x_1171_);
lean_inc_ref(v___x_1174_);
lean_inc_ref_n(v___x_1173_, 2);
lean_inc(v___x_1172_);
v___x_1185_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v___x_1172_, v___x_1173_, v___x_1174_, v_fst_1175_);
v___x_1186_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v___x_1172_, v___x_1173_, v___x_1174_, v_fst_1176_);
v___x_1187_ = l_Lean_mkApp6(v___x_1184_, v___x_1173_, v___x_1185_, v___x_1186_, v___x_1177_, v_snd_1178_, v_hgoal_1180_);
v___x_1188_ = lean_apply_1(v_snd_1179_, v___x_1187_);
return v___x_1188_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__0));
v___x_1191_ = l_Lean_stringToMessageData(v___x_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1(lean_object* v___x_1192_, lean_object* v___x_1193_, lean_object* v___x_1194_, lean_object* v___x_1195_, lean_object* v___x_1196_, lean_object* v_as_1197_, size_t v_sz_1198_, size_t v_i_1199_, lean_object* v_b_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_a_1211_; uint8_t v___x_1215_; 
v___x_1215_ = lean_usize_dec_lt(v_i_1199_, v_sz_1198_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; 
lean_dec_ref(v___x_1196_);
lean_dec_ref(v___x_1195_);
lean_dec_ref(v___x_1194_);
lean_dec(v___x_1193_);
lean_dec(v___x_1192_);
v___x_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1216_, 0, v_b_1200_);
return v___x_1216_;
}
else
{
lean_object* v_fst_1217_; lean_object* v_snd_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1272_; 
v_fst_1217_ = lean_ctor_get(v_b_1200_, 0);
v_snd_1218_ = lean_ctor_get(v_b_1200_, 1);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_b_1200_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1220_ = v_b_1200_;
v_isShared_1221_ = v_isSharedCheck_1272_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_snd_1218_);
lean_inc(v_fst_1217_);
lean_dec(v_b_1200_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1272_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v_a_1225_; lean_object* v___y_1227_; lean_object* v___x_1267_; 
v___x_1222_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_1223_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1224_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v_a_1225_ = lean_array_uget_borrowed(v_as_1197_, v_i_1199_);
lean_inc(v_a_1225_);
lean_inc(v_fst_1217_);
lean_inc_ref(v___x_1195_);
v___x_1267_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(v___x_1195_, v_fst_1217_, v_a_1225_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
if (lean_obj_tag(v_a_1268_) == 0)
{
lean_object* v___x_1269_; 
lean_dec_ref(v___x_1267_);
lean_inc(v_a_1225_);
lean_inc(v_fst_1217_);
lean_inc_ref(v___x_1195_);
v___x_1269_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(v___x_1195_, v_fst_1217_, v_a_1225_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
if (lean_obj_tag(v_a_1270_) == 0)
{
lean_object* v___x_1271_; 
lean_dec_ref(v___x_1269_);
lean_inc(v_a_1225_);
lean_inc(v_fst_1217_);
lean_inc_ref(v___x_1195_);
v___x_1271_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(v___x_1195_, v_fst_1217_, v_a_1225_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
v___y_1227_ = v___x_1271_;
goto v___jp_1226_;
}
else
{
lean_dec_ref(v_a_1270_);
v___y_1227_ = v___x_1269_;
goto v___jp_1226_;
}
}
else
{
v___y_1227_ = v___x_1269_;
goto v___jp_1226_;
}
}
else
{
lean_dec_ref(v_a_1268_);
v___y_1227_ = v___x_1267_;
goto v___jp_1226_;
}
}
else
{
v___y_1227_ = v___x_1267_;
goto v___jp_1226_;
}
v___jp_1226_:
{
if (lean_obj_tag(v___y_1227_) == 0)
{
lean_object* v_a_1228_; 
v_a_1228_ = lean_ctor_get(v___y_1227_, 0);
lean_inc(v_a_1228_);
lean_dec_ref(v___y_1227_);
if (lean_obj_tag(v_a_1228_) == 0)
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1229_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1);
lean_inc(v_fst_1217_);
v___x_1230_ = l_Lean_MessageData_ofExpr(v_fst_1217_);
v___x_1231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1229_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
v___x_1232_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_1233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1231_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
lean_inc(v_a_1225_);
v___x_1234_ = l_Lean_MessageData_ofSyntax(v_a_1225_);
v___x_1235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_1235_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v___x_1238_; 
lean_dec_ref(v___x_1236_);
if (v_isShared_1221_ == 0)
{
v___x_1238_ = v___x_1220_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_fst_1217_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_snd_1218_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
v_a_1211_ = v___x_1238_;
goto v___jp_1210_;
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
lean_dec(v_fst_1217_);
lean_dec_ref(v___x_1196_);
lean_dec_ref(v___x_1195_);
lean_dec_ref(v___x_1194_);
lean_dec(v___x_1193_);
lean_dec(v___x_1192_);
v_a_1240_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1236_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1236_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
else
{
lean_object* v_val_1248_; lean_object* v_fst_1249_; lean_object* v_snd_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1258_; 
lean_del_object(v___x_1220_);
v_val_1248_ = lean_ctor_get(v_a_1228_, 0);
lean_inc(v_val_1248_);
lean_dec_ref(v_a_1228_);
v_fst_1249_ = lean_ctor_get(v_val_1248_, 0);
v_snd_1250_ = lean_ctor_get(v_val_1248_, 1);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_val_1248_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1252_ = v_val_1248_;
v_isShared_1253_ = v_isSharedCheck_1258_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_snd_1250_);
lean_inc(v_fst_1249_);
lean_dec(v_val_1248_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1258_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___f_1254_; lean_object* v___x_1256_; 
lean_inc_ref(v___x_1196_);
lean_inc(v_fst_1249_);
lean_inc_ref(v___x_1195_);
lean_inc_ref(v___x_1194_);
lean_inc(v___x_1193_);
lean_inc(v___x_1192_);
v___f_1254_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0), 13, 12);
lean_closure_set(v___f_1254_, 0, v___x_1222_);
lean_closure_set(v___f_1254_, 1, v___x_1223_);
lean_closure_set(v___f_1254_, 2, v___x_1224_);
lean_closure_set(v___f_1254_, 3, v___x_1192_);
lean_closure_set(v___f_1254_, 4, v___x_1193_);
lean_closure_set(v___f_1254_, 5, v___x_1194_);
lean_closure_set(v___f_1254_, 6, v___x_1195_);
lean_closure_set(v___f_1254_, 7, v_fst_1217_);
lean_closure_set(v___f_1254_, 8, v_fst_1249_);
lean_closure_set(v___f_1254_, 9, v___x_1196_);
lean_closure_set(v___f_1254_, 10, v_snd_1250_);
lean_closure_set(v___f_1254_, 11, v_snd_1218_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 1, v___f_1254_);
v___x_1256_ = v___x_1252_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_fst_1249_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v___f_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
v_a_1211_ = v___x_1256_;
goto v___jp_1210_;
}
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
lean_dec(v_fst_1217_);
lean_dec_ref(v___x_1196_);
lean_dec_ref(v___x_1195_);
lean_dec_ref(v___x_1194_);
lean_dec(v___x_1193_);
lean_dec(v___x_1192_);
v_a_1259_ = lean_ctor_get(v___y_1227_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___y_1227_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___y_1227_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___y_1227_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
}
}
v___jp_1210_:
{
size_t v___x_1212_; size_t v___x_1213_; 
v___x_1212_ = ((size_t)1ULL);
v___x_1213_ = lean_usize_add(v_i_1199_, v___x_1212_);
v_i_1199_ = v___x_1213_;
v_b_1200_ = v_a_1211_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___boxed(lean_object** _args){
lean_object* v___x_1273_ = _args[0];
lean_object* v___x_1274_ = _args[1];
lean_object* v___x_1275_ = _args[2];
lean_object* v___x_1276_ = _args[3];
lean_object* v___x_1277_ = _args[4];
lean_object* v_as_1278_ = _args[5];
lean_object* v_sz_1279_ = _args[6];
lean_object* v_i_1280_ = _args[7];
lean_object* v_b_1281_ = _args[8];
lean_object* v___y_1282_ = _args[9];
lean_object* v___y_1283_ = _args[10];
lean_object* v___y_1284_ = _args[11];
lean_object* v___y_1285_ = _args[12];
lean_object* v___y_1286_ = _args[13];
lean_object* v___y_1287_ = _args[14];
lean_object* v___y_1288_ = _args[15];
lean_object* v___y_1289_ = _args[16];
lean_object* v___y_1290_ = _args[17];
_start:
{
size_t v_sz_boxed_1291_; size_t v_i_boxed_1292_; lean_object* v_res_1293_; 
v_sz_boxed_1291_ = lean_unbox_usize(v_sz_1279_);
lean_dec(v_sz_1279_);
v_i_boxed_1292_ = lean_unbox_usize(v_i_1280_);
lean_dec(v_i_1280_);
v_res_1293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1(v___x_1273_, v___x_1274_, v___x_1275_, v___x_1276_, v___x_1277_, v_as_1278_, v_sz_boxed_1291_, v_i_boxed_1292_, v_b_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec_ref(v_as_1278_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7___redArg(lean_object* v_x_1294_, lean_object* v_x_1295_, lean_object* v_x_1296_, lean_object* v_x_1297_){
_start:
{
lean_object* v_ks_1298_; lean_object* v_vs_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1323_; 
v_ks_1298_ = lean_ctor_get(v_x_1294_, 0);
v_vs_1299_ = lean_ctor_get(v_x_1294_, 1);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_x_1294_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1301_ = v_x_1294_;
v_isShared_1302_ = v_isSharedCheck_1323_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_vs_1299_);
lean_inc(v_ks_1298_);
lean_dec(v_x_1294_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1323_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = lean_array_get_size(v_ks_1298_);
v___x_1304_ = lean_nat_dec_lt(v_x_1295_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1308_; 
lean_dec(v_x_1295_);
v___x_1305_ = lean_array_push(v_ks_1298_, v_x_1296_);
v___x_1306_ = lean_array_push(v_vs_1299_, v_x_1297_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 1, v___x_1306_);
lean_ctor_set(v___x_1301_, 0, v___x_1305_);
v___x_1308_ = v___x_1301_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1305_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
else
{
lean_object* v_k_x27_1310_; uint8_t v___x_1311_; 
v_k_x27_1310_ = lean_array_fget_borrowed(v_ks_1298_, v_x_1295_);
v___x_1311_ = l_Lean_instBEqMVarId_beq(v_x_1296_, v_k_x27_1310_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1313_; 
if (v_isShared_1302_ == 0)
{
v___x_1313_ = v___x_1301_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_ks_1298_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_vs_1299_);
v___x_1313_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_unsigned_to_nat(1u);
v___x_1315_ = lean_nat_add(v_x_1295_, v___x_1314_);
lean_dec(v_x_1295_);
v_x_1294_ = v___x_1313_;
v_x_1295_ = v___x_1315_;
goto _start;
}
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1318_ = lean_array_fset(v_ks_1298_, v_x_1295_, v_x_1296_);
v___x_1319_ = lean_array_fset(v_vs_1299_, v_x_1295_, v_x_1297_);
lean_dec(v_x_1295_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 1, v___x_1319_);
lean_ctor_set(v___x_1301_, 0, v___x_1318_);
v___x_1321_ = v___x_1301_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1318_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6___redArg(lean_object* v_n_1324_, lean_object* v_k_1325_, lean_object* v_v_1326_){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7___redArg(v_n_1324_, v___x_1327_, v_k_1325_, v_v_1326_);
return v___x_1328_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0(void){
_start:
{
size_t v___x_1329_; size_t v___x_1330_; size_t v___x_1331_; 
v___x_1329_ = ((size_t)5ULL);
v___x_1330_ = ((size_t)1ULL);
v___x_1331_ = lean_usize_shift_left(v___x_1330_, v___x_1329_);
return v___x_1331_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_1332_; size_t v___x_1333_; size_t v___x_1334_; 
v___x_1332_ = ((size_t)1ULL);
v___x_1333_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0);
v___x_1334_ = lean_usize_sub(v___x_1333_, v___x_1332_);
return v___x_1334_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(lean_object* v_x_1336_, size_t v_x_1337_, size_t v_x_1338_, lean_object* v_x_1339_, lean_object* v_x_1340_){
_start:
{
if (lean_obj_tag(v_x_1336_) == 0)
{
lean_object* v_es_1341_; size_t v___x_1342_; size_t v___x_1343_; size_t v___x_1344_; size_t v___x_1345_; lean_object* v_j_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v_es_1341_ = lean_ctor_get(v_x_1336_, 0);
v___x_1342_ = ((size_t)5ULL);
v___x_1343_ = ((size_t)1ULL);
v___x_1344_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1345_ = lean_usize_land(v_x_1337_, v___x_1344_);
v_j_1346_ = lean_usize_to_nat(v___x_1345_);
v___x_1347_ = lean_array_get_size(v_es_1341_);
v___x_1348_ = lean_nat_dec_lt(v_j_1346_, v___x_1347_);
if (v___x_1348_ == 0)
{
lean_dec(v_j_1346_);
lean_dec(v_x_1340_);
lean_dec(v_x_1339_);
return v_x_1336_;
}
else
{
lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1385_; 
lean_inc_ref(v_es_1341_);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_x_1336_);
if (v_isSharedCheck_1385_ == 0)
{
lean_object* v_unused_1386_; 
v_unused_1386_ = lean_ctor_get(v_x_1336_, 0);
lean_dec(v_unused_1386_);
v___x_1350_ = v_x_1336_;
v_isShared_1351_ = v_isSharedCheck_1385_;
goto v_resetjp_1349_;
}
else
{
lean_dec(v_x_1336_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1385_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v_v_1352_; lean_object* v___x_1353_; lean_object* v_xs_x27_1354_; lean_object* v___y_1356_; 
v_v_1352_ = lean_array_fget(v_es_1341_, v_j_1346_);
v___x_1353_ = lean_box(0);
v_xs_x27_1354_ = lean_array_fset(v_es_1341_, v_j_1346_, v___x_1353_);
switch(lean_obj_tag(v_v_1352_))
{
case 0:
{
lean_object* v_key_1361_; lean_object* v_val_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1372_; 
v_key_1361_ = lean_ctor_get(v_v_1352_, 0);
v_val_1362_ = lean_ctor_get(v_v_1352_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_v_1352_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1364_ = v_v_1352_;
v_isShared_1365_ = v_isSharedCheck_1372_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_val_1362_);
lean_inc(v_key_1361_);
lean_dec(v_v_1352_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1372_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
uint8_t v___x_1366_; 
v___x_1366_ = l_Lean_instBEqMVarId_beq(v_x_1339_, v_key_1361_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_del_object(v___x_1364_);
v___x_1367_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1361_, v_val_1362_, v_x_1339_, v_x_1340_);
v___x_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
v___y_1356_ = v___x_1368_;
goto v___jp_1355_;
}
else
{
lean_object* v___x_1370_; 
lean_dec(v_val_1362_);
lean_dec(v_key_1361_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v_x_1340_);
lean_ctor_set(v___x_1364_, 0, v_x_1339_);
v___x_1370_ = v___x_1364_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_x_1339_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_x_1340_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
v___y_1356_ = v___x_1370_;
goto v___jp_1355_;
}
}
}
}
case 1:
{
lean_object* v_node_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1383_; 
v_node_1373_ = lean_ctor_get(v_v_1352_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_v_1352_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1375_ = v_v_1352_;
v_isShared_1376_ = v_isSharedCheck_1383_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_node_1373_);
lean_dec(v_v_1352_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1383_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
size_t v___x_1377_; size_t v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1377_ = lean_usize_shift_right(v_x_1337_, v___x_1342_);
v___x_1378_ = lean_usize_add(v_x_1338_, v___x_1343_);
v___x_1379_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_node_1373_, v___x_1377_, v___x_1378_, v_x_1339_, v_x_1340_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1379_);
v___x_1381_ = v___x_1375_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
v___y_1356_ = v___x_1381_;
goto v___jp_1355_;
}
}
}
default: 
{
lean_object* v___x_1384_; 
v___x_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1384_, 0, v_x_1339_);
lean_ctor_set(v___x_1384_, 1, v_x_1340_);
v___y_1356_ = v___x_1384_;
goto v___jp_1355_;
}
}
v___jp_1355_:
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = lean_array_fset(v_xs_x27_1354_, v_j_1346_, v___y_1356_);
lean_dec(v_j_1346_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1357_);
v___x_1359_ = v___x_1350_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
else
{
lean_object* v_ks_1387_; lean_object* v_vs_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1408_; 
v_ks_1387_ = lean_ctor_get(v_x_1336_, 0);
v_vs_1388_ = lean_ctor_get(v_x_1336_, 1);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_x_1336_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1390_ = v_x_1336_;
v_isShared_1391_ = v_isSharedCheck_1408_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_vs_1388_);
lean_inc(v_ks_1387_);
lean_dec(v_x_1336_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1408_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_ks_1387_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_vs_1388_);
v___x_1393_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v_newNode_1394_; uint8_t v___y_1396_; size_t v___x_1402_; uint8_t v___x_1403_; 
v_newNode_1394_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6___redArg(v___x_1393_, v_x_1339_, v_x_1340_);
v___x_1402_ = ((size_t)7ULL);
v___x_1403_ = lean_usize_dec_le(v___x_1402_, v_x_1338_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1404_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1394_);
v___x_1405_ = lean_unsigned_to_nat(4u);
v___x_1406_ = lean_nat_dec_lt(v___x_1404_, v___x_1405_);
lean_dec(v___x_1404_);
v___y_1396_ = v___x_1406_;
goto v___jp_1395_;
}
else
{
v___y_1396_ = v___x_1403_;
goto v___jp_1395_;
}
v___jp_1395_:
{
if (v___y_1396_ == 0)
{
lean_object* v_ks_1397_; lean_object* v_vs_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v_ks_1397_ = lean_ctor_get(v_newNode_1394_, 0);
lean_inc_ref(v_ks_1397_);
v_vs_1398_ = lean_ctor_get(v_newNode_1394_, 1);
lean_inc_ref(v_vs_1398_);
lean_dec_ref(v_newNode_1394_);
v___x_1399_ = lean_unsigned_to_nat(0u);
v___x_1400_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__2);
v___x_1401_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(v_x_1338_, v_ks_1397_, v_vs_1398_, v___x_1399_, v___x_1400_);
lean_dec_ref(v_vs_1398_);
lean_dec_ref(v_ks_1397_);
return v___x_1401_;
}
else
{
return v_newNode_1394_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(size_t v_depth_1409_, lean_object* v_keys_1410_, lean_object* v_vals_1411_, lean_object* v_i_1412_, lean_object* v_entries_1413_){
_start:
{
lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1414_ = lean_array_get_size(v_keys_1410_);
v___x_1415_ = lean_nat_dec_lt(v_i_1412_, v___x_1414_);
if (v___x_1415_ == 0)
{
lean_dec(v_i_1412_);
return v_entries_1413_;
}
else
{
lean_object* v_k_1416_; lean_object* v_v_1417_; uint64_t v___x_1418_; size_t v_h_1419_; size_t v___x_1420_; lean_object* v___x_1421_; size_t v___x_1422_; size_t v___x_1423_; size_t v___x_1424_; size_t v_h_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v_k_1416_ = lean_array_fget_borrowed(v_keys_1410_, v_i_1412_);
v_v_1417_ = lean_array_fget_borrowed(v_vals_1411_, v_i_1412_);
v___x_1418_ = l_Lean_instHashableMVarId_hash(v_k_1416_);
v_h_1419_ = lean_uint64_to_usize(v___x_1418_);
v___x_1420_ = ((size_t)5ULL);
v___x_1421_ = lean_unsigned_to_nat(1u);
v___x_1422_ = ((size_t)1ULL);
v___x_1423_ = lean_usize_sub(v_depth_1409_, v___x_1422_);
v___x_1424_ = lean_usize_mul(v___x_1420_, v___x_1423_);
v_h_1425_ = lean_usize_shift_right(v_h_1419_, v___x_1424_);
v___x_1426_ = lean_nat_add(v_i_1412_, v___x_1421_);
lean_dec(v_i_1412_);
lean_inc(v_v_1417_);
lean_inc(v_k_1416_);
v___x_1427_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_entries_1413_, v_h_1425_, v_depth_1409_, v_k_1416_, v_v_1417_);
v_i_1412_ = v___x_1426_;
v_entries_1413_ = v___x_1427_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_depth_1429_, lean_object* v_keys_1430_, lean_object* v_vals_1431_, lean_object* v_i_1432_, lean_object* v_entries_1433_){
_start:
{
size_t v_depth_boxed_1434_; lean_object* v_res_1435_; 
v_depth_boxed_1434_ = lean_unbox_usize(v_depth_1429_);
lean_dec(v_depth_1429_);
v_res_1435_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(v_depth_boxed_1434_, v_keys_1430_, v_vals_1431_, v_i_1432_, v_entries_1433_);
lean_dec_ref(v_vals_1431_);
lean_dec_ref(v_keys_1430_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_x_1436_, lean_object* v_x_1437_, lean_object* v_x_1438_, lean_object* v_x_1439_, lean_object* v_x_1440_){
_start:
{
size_t v_x_8568__boxed_1441_; size_t v_x_8569__boxed_1442_; lean_object* v_res_1443_; 
v_x_8568__boxed_1441_ = lean_unbox_usize(v_x_1437_);
lean_dec(v_x_1437_);
v_x_8569__boxed_1442_ = lean_unbox_usize(v_x_1438_);
lean_dec(v_x_1438_);
v_res_1443_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_x_1436_, v_x_8568__boxed_1441_, v_x_8569__boxed_1442_, v_x_1439_, v_x_1440_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2___redArg(lean_object* v_x_1444_, lean_object* v_x_1445_, lean_object* v_x_1446_){
_start:
{
uint64_t v___x_1447_; size_t v___x_1448_; size_t v___x_1449_; lean_object* v___x_1450_; 
v___x_1447_ = l_Lean_instHashableMVarId_hash(v_x_1445_);
v___x_1448_ = lean_uint64_to_usize(v___x_1447_);
v___x_1449_ = ((size_t)1ULL);
v___x_1450_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_x_1444_, v___x_1448_, v___x_1449_, v_x_1445_, v_x_1446_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(lean_object* v_mvarId_1451_, lean_object* v_val_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___x_1455_; lean_object* v_mctx_1456_; lean_object* v_cache_1457_; lean_object* v_zetaDeltaFVarIds_1458_; lean_object* v_postponed_1459_; lean_object* v_diag_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1487_; 
v___x_1455_ = lean_st_ref_take(v___y_1453_);
v_mctx_1456_ = lean_ctor_get(v___x_1455_, 0);
v_cache_1457_ = lean_ctor_get(v___x_1455_, 1);
v_zetaDeltaFVarIds_1458_ = lean_ctor_get(v___x_1455_, 2);
v_postponed_1459_ = lean_ctor_get(v___x_1455_, 3);
v_diag_1460_ = lean_ctor_get(v___x_1455_, 4);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1462_ = v___x_1455_;
v_isShared_1463_ = v_isSharedCheck_1487_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_diag_1460_);
lean_inc(v_postponed_1459_);
lean_inc(v_zetaDeltaFVarIds_1458_);
lean_inc(v_cache_1457_);
lean_inc(v_mctx_1456_);
lean_dec(v___x_1455_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1487_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v_depth_1464_; lean_object* v_levelAssignDepth_1465_; lean_object* v_mvarCounter_1466_; lean_object* v_lDepth_1467_; lean_object* v_decls_1468_; lean_object* v_userNames_1469_; lean_object* v_lAssignment_1470_; lean_object* v_eAssignment_1471_; lean_object* v_dAssignment_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1486_; 
v_depth_1464_ = lean_ctor_get(v_mctx_1456_, 0);
v_levelAssignDepth_1465_ = lean_ctor_get(v_mctx_1456_, 1);
v_mvarCounter_1466_ = lean_ctor_get(v_mctx_1456_, 2);
v_lDepth_1467_ = lean_ctor_get(v_mctx_1456_, 3);
v_decls_1468_ = lean_ctor_get(v_mctx_1456_, 4);
v_userNames_1469_ = lean_ctor_get(v_mctx_1456_, 5);
v_lAssignment_1470_ = lean_ctor_get(v_mctx_1456_, 6);
v_eAssignment_1471_ = lean_ctor_get(v_mctx_1456_, 7);
v_dAssignment_1472_ = lean_ctor_get(v_mctx_1456_, 8);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_mctx_1456_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1474_ = v_mctx_1456_;
v_isShared_1475_ = v_isSharedCheck_1486_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_dAssignment_1472_);
lean_inc(v_eAssignment_1471_);
lean_inc(v_lAssignment_1470_);
lean_inc(v_userNames_1469_);
lean_inc(v_decls_1468_);
lean_inc(v_lDepth_1467_);
lean_inc(v_mvarCounter_1466_);
lean_inc(v_levelAssignDepth_1465_);
lean_inc(v_depth_1464_);
lean_dec(v_mctx_1456_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1486_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; lean_object* v___x_1478_; 
v___x_1476_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2___redArg(v_eAssignment_1471_, v_mvarId_1451_, v_val_1452_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 7, v___x_1476_);
v___x_1478_ = v___x_1474_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_depth_1464_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_levelAssignDepth_1465_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_mvarCounter_1466_);
lean_ctor_set(v_reuseFailAlloc_1485_, 3, v_lDepth_1467_);
lean_ctor_set(v_reuseFailAlloc_1485_, 4, v_decls_1468_);
lean_ctor_set(v_reuseFailAlloc_1485_, 5, v_userNames_1469_);
lean_ctor_set(v_reuseFailAlloc_1485_, 6, v_lAssignment_1470_);
lean_ctor_set(v_reuseFailAlloc_1485_, 7, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1485_, 8, v_dAssignment_1472_);
v___x_1478_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1480_; 
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v___x_1478_);
v___x_1480_ = v___x_1462_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_cache_1457_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_zetaDeltaFVarIds_1458_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v_postponed_1459_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v_diag_1460_);
v___x_1480_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1481_ = lean_st_ref_set(v___y_1453_, v___x_1480_);
v___x_1482_ = lean_box(0);
v___x_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
return v___x_1483_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg___boxed(lean_object* v_mvarId_1488_, lean_object* v_val_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_mvarId_1488_, v_val_1489_, v___y_1490_);
lean_dec(v___y_1490_);
return v_res_1492_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1496_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__2));
v___x_1497_ = lean_unsigned_to_nat(33u);
v___x_1498_ = lean_unsigned_to_nat(105u);
v___x_1499_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__1));
v___x_1500_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15));
v___x_1501_ = l_mkPanicMessageWithDecl(v___x_1500_, v___x_1499_, v___x_1498_, v___x_1497_, v___x_1496_);
return v___x_1501_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__4));
v___x_1504_ = l_Lean_stringToMessageData(v___x_1503_);
return v___x_1504_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__6));
v___x_1507_ = l_Lean_stringToMessageData(v___x_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0(lean_object* v___x_1508_, lean_object* v_snd_1509_, lean_object* v_hyp_1510_, lean_object* v___x_1511_, lean_object* v_args_1512_, lean_object* v_fst_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
if (lean_obj_tag(v___x_1508_) == 1)
{
lean_object* v_val_1523_; lean_object* v_focusHyp_1524_; lean_object* v_restHyps_1525_; lean_object* v_proof_1526_; lean_object* v___x_1527_; 
v_val_1523_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_val_1523_);
lean_dec_ref(v___x_1508_);
v_focusHyp_1524_ = lean_ctor_get(v_val_1523_, 0);
lean_inc_ref_n(v_focusHyp_1524_, 2);
v_restHyps_1525_ = lean_ctor_get(v_val_1523_, 1);
lean_inc_ref(v_restHyps_1525_);
v_proof_1526_ = lean_ctor_get(v_val_1523_, 2);
lean_inc_ref(v_proof_1526_);
lean_dec(v_val_1523_);
v___x_1527_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_1524_);
if (lean_obj_tag(v___x_1527_) == 1)
{
lean_object* v_val_1528_; lean_object* v_u_1529_; lean_object* v_00_u03c3s_1530_; lean_object* v_hyps_1531_; lean_object* v_target_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1590_; 
v_val_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_val_1528_);
lean_dec_ref(v___x_1527_);
v_u_1529_ = lean_ctor_get(v_snd_1509_, 0);
v_00_u03c3s_1530_ = lean_ctor_get(v_snd_1509_, 1);
v_hyps_1531_ = lean_ctor_get(v_snd_1509_, 2);
v_target_1532_ = lean_ctor_get(v_snd_1509_, 3);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_snd_1509_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1534_ = v_snd_1509_;
v_isShared_1535_ = v_isSharedCheck_1590_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_target_1532_);
lean_inc(v_hyps_1531_);
lean_inc(v_00_u03c3s_1530_);
lean_inc(v_u_1529_);
lean_dec(v_snd_1509_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1590_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
uint8_t v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = 0;
lean_inc_ref(v_00_u03c3s_1530_);
v___x_1537_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_hyp_1510_, v_00_u03c3s_1530_, v_val_1528_, v___x_1536_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; size_t v_sz_1549_; size_t v___x_1550_; lean_object* v___x_1551_; 
lean_dec_ref(v___x_1537_);
v___x_1538_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_1539_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1540_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_1541_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1542_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__0));
v___x_1543_ = l_Lean_Name_mkStr6(v___x_1538_, v___x_1539_, v___x_1540_, v___x_1511_, v___x_1541_, v___x_1542_);
v___x_1544_ = lean_box(0);
lean_inc_n(v_u_1529_, 2);
v___x_1545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1545_, 0, v_u_1529_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
lean_inc_ref(v___x_1545_);
v___x_1546_ = l_Lean_mkConst(v___x_1543_, v___x_1545_);
lean_inc_ref_n(v_target_1532_, 2);
lean_inc_ref(v_focusHyp_1524_);
lean_inc_ref_n(v_restHyps_1525_, 2);
lean_inc_ref_n(v_00_u03c3s_1530_, 2);
v___x_1547_ = lean_alloc_closure((void*)(l_Lean_mkApp7), 8, 7);
lean_closure_set(v___x_1547_, 0, v___x_1546_);
lean_closure_set(v___x_1547_, 1, v_00_u03c3s_1530_);
lean_closure_set(v___x_1547_, 2, v_hyps_1531_);
lean_closure_set(v___x_1547_, 3, v_restHyps_1525_);
lean_closure_set(v___x_1547_, 4, v_focusHyp_1524_);
lean_closure_set(v___x_1547_, 5, v_target_1532_);
lean_closure_set(v___x_1547_, 6, v_proof_1526_);
v___x_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1548_, 0, v_focusHyp_1524_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v_sz_1549_ = lean_array_size(v_args_1512_);
v___x_1550_ = ((size_t)0ULL);
v___x_1551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1(v___x_1545_, v_u_1529_, v_00_u03c3s_1530_, v_restHyps_1525_, v_target_1532_, v_args_1512_, v_sz_1549_, v___x_1550_, v___x_1548_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v_fst_1553_; lean_object* v_snd_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1581_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref(v___x_1551_);
v_fst_1553_ = lean_ctor_get(v_a_1552_, 0);
v_snd_1554_ = lean_ctor_get(v_a_1552_, 1);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_a_1552_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1556_ = v_a_1552_;
v_isShared_1557_ = v_isSharedCheck_1581_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_snd_1554_);
lean_inc(v_fst_1553_);
lean_dec(v_a_1552_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1581_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; lean_object* v___x_1560_; 
lean_inc_ref(v_00_u03c3s_1530_);
lean_inc(v_u_1529_);
v___x_1558_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1529_, v_00_u03c3s_1530_, v_restHyps_1525_, v_fst_1553_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 2, v___x_1558_);
v___x_1560_ = v___x_1534_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_u_1529_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_00_u03c3s_1530_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1580_, 3, v_target_1532_);
v___x_1560_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1561_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1560_);
v___x_1562_ = lean_box(0);
v___x_1563_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1561_, v___x_1562_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc_n(v_a_1564_, 2);
lean_dec_ref(v___x_1563_);
v___x_1565_ = lean_apply_1(v_snd_1554_, v_a_1564_);
v___x_1566_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_fst_1513_, v___x_1565_, v___y_1519_);
lean_dec_ref(v___x_1566_);
v___x_1567_ = l_Lean_Expr_mvarId_x21(v_a_1564_);
lean_dec(v_a_1564_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set_tag(v___x_1556_, 1);
lean_ctor_set(v___x_1556_, 1, v___x_1544_);
lean_ctor_set(v___x_1556_, 0, v___x_1567_);
v___x_1569_ = v___x_1556_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v___x_1544_);
v___x_1569_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1569_, v___y_1515_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
return v___x_1570_;
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_del_object(v___x_1556_);
lean_dec(v_snd_1554_);
lean_dec(v_fst_1513_);
v_a_1572_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1563_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1563_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_del_object(v___x_1534_);
lean_dec_ref(v_target_1532_);
lean_dec_ref(v_00_u03c3s_1530_);
lean_dec(v_u_1529_);
lean_dec_ref(v_restHyps_1525_);
lean_dec(v_fst_1513_);
v_a_1582_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1551_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1551_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
else
{
lean_del_object(v___x_1534_);
lean_dec_ref(v_target_1532_);
lean_dec_ref(v_hyps_1531_);
lean_dec_ref(v_00_u03c3s_1530_);
lean_dec(v_u_1529_);
lean_dec_ref(v_proof_1526_);
lean_dec_ref(v_restHyps_1525_);
lean_dec_ref(v_focusHyp_1524_);
lean_dec(v_fst_1513_);
lean_dec_ref(v___x_1511_);
return v___x_1537_;
}
}
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_dec(v___x_1527_);
lean_dec_ref(v_proof_1526_);
lean_dec_ref(v_restHyps_1525_);
lean_dec_ref(v_focusHyp_1524_);
lean_dec(v_fst_1513_);
lean_dec_ref(v___x_1511_);
lean_dec(v_hyp_1510_);
lean_dec_ref(v_snd_1509_);
v___x_1591_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3);
v___x_1592_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(v___x_1591_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
return v___x_1592_;
}
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_dec(v_fst_1513_);
lean_dec_ref(v___x_1511_);
lean_dec_ref(v_snd_1509_);
lean_dec(v___x_1508_);
v___x_1593_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5);
v___x_1594_ = l_Lean_MessageData_ofSyntax(v_hyp_1510_);
v___x_1595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1593_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7);
v___x_1597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_1597_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
return v___x_1598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___boxed(lean_object* v___x_1599_, lean_object* v_snd_1600_, lean_object* v_hyp_1601_, lean_object* v___x_1602_, lean_object* v_args_1603_, lean_object* v_fst_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0(v___x_1599_, v_snd_1600_, v_hyp_1601_, v___x_1602_, v_args_1603_, v_fst_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec_ref(v_args_1603_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize(lean_object* v_x_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; 
v___x_1632_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1633_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2));
lean_inc(v_x_1622_);
v___x_1634_ = l_Lean_Syntax_isOfKind(v_x_1622_, v___x_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; 
lean_dec(v_x_1622_);
v___x_1635_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_1635_;
}
else
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1624_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v_fst_1638_; lean_object* v_snd_1639_; lean_object* v___x_1640_; lean_object* v_hyp_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v_args_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___y_1647_; lean_object* v___x_1648_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref(v___x_1636_);
v_fst_1638_ = lean_ctor_get(v_a_1637_, 0);
lean_inc_n(v_fst_1638_, 2);
v_snd_1639_ = lean_ctor_get(v_a_1637_, 1);
lean_inc_n(v_snd_1639_, 2);
lean_dec(v_a_1637_);
v___x_1640_ = lean_unsigned_to_nat(1u);
v_hyp_1641_ = l_Lean_Syntax_getArg(v_x_1622_, v___x_1640_);
v___x_1642_ = lean_unsigned_to_nat(2u);
v___x_1643_ = l_Lean_Syntax_getArg(v_x_1622_, v___x_1642_);
lean_dec(v_x_1622_);
v_args_1644_ = l_Lean_Syntax_getArgs(v___x_1643_);
lean_dec(v___x_1643_);
v___x_1645_ = l_Lean_TSyntax_getId(v_hyp_1641_);
v___x_1646_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_snd_1639_, v___x_1645_);
lean_dec(v___x_1645_);
v___y_1647_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___boxed), 15, 6);
lean_closure_set(v___y_1647_, 0, v___x_1646_);
lean_closure_set(v___y_1647_, 1, v_snd_1639_);
lean_closure_set(v___y_1647_, 2, v_hyp_1641_);
lean_closure_set(v___y_1647_, 3, v___x_1632_);
lean_closure_set(v___y_1647_, 4, v_args_1644_);
lean_closure_set(v___y_1647_, 5, v_fst_1638_);
v___x_1648_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_fst_1638_, v___y_1647_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
return v___x_1648_;
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v_x_1622_);
v_a_1649_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1636_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1636_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___boxed(lean_object* v_x_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize(v_x_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_);
lean_dec(v_a_1665_);
lean_dec_ref(v_a_1664_);
lean_dec(v_a_1663_);
lean_dec_ref(v_a_1662_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2(lean_object* v_mvarId_1668_, lean_object* v_val_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_mvarId_1668_, v_val_1669_, v___y_1675_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___boxed(lean_object* v_mvarId_1680_, lean_object* v_val_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2(v_mvarId_1680_, v_val_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2(lean_object* v_00_u03b2_1692_, lean_object* v_x_1693_, lean_object* v_x_1694_, lean_object* v_x_1695_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2___redArg(v_x_1693_, v_x_1694_, v_x_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_1697_, lean_object* v_x_1698_, size_t v_x_1699_, size_t v_x_1700_, lean_object* v_x_1701_, lean_object* v_x_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_x_1698_, v_x_1699_, v_x_1700_, v_x_1701_, v_x_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1704_, lean_object* v_x_1705_, lean_object* v_x_1706_, lean_object* v_x_1707_, lean_object* v_x_1708_, lean_object* v_x_1709_){
_start:
{
size_t v_x_9125__boxed_1710_; size_t v_x_9126__boxed_1711_; lean_object* v_res_1712_; 
v_x_9125__boxed_1710_ = lean_unbox_usize(v_x_1706_);
lean_dec(v_x_1706_);
v_x_9126__boxed_1711_ = lean_unbox_usize(v_x_1707_);
lean_dec(v_x_1707_);
v_res_1712_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5(v_00_u03b2_1704_, v_x_1705_, v_x_9125__boxed_1710_, v_x_9126__boxed_1711_, v_x_1708_, v_x_1709_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_1713_, lean_object* v_n_1714_, lean_object* v_k_1715_, lean_object* v_v_1716_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6___redArg(v_n_1714_, v_k_1715_, v_v_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7(lean_object* v_00_u03b2_1718_, size_t v_depth_1719_, lean_object* v_keys_1720_, lean_object* v_vals_1721_, lean_object* v_heq_1722_, lean_object* v_i_1723_, lean_object* v_entries_1724_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(v_depth_1719_, v_keys_1720_, v_vals_1721_, v_i_1723_, v_entries_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b2_1726_, lean_object* v_depth_1727_, lean_object* v_keys_1728_, lean_object* v_vals_1729_, lean_object* v_heq_1730_, lean_object* v_i_1731_, lean_object* v_entries_1732_){
_start:
{
size_t v_depth_boxed_1733_; lean_object* v_res_1734_; 
v_depth_boxed_1733_ = lean_unbox_usize(v_depth_1727_);
lean_dec(v_depth_1727_);
v_res_1734_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7(v_00_u03b2_1726_, v_depth_boxed_1733_, v_keys_1728_, v_vals_1729_, v_heq_1730_, v_i_1731_, v_entries_1732_);
lean_dec_ref(v_vals_1729_);
lean_dec_ref(v_keys_1728_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_1735_, lean_object* v_x_1736_, lean_object* v_x_1737_, lean_object* v_x_1738_, lean_object* v_x_1739_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7___redArg(v_x_1736_, v_x_1737_, v_x_1738_, v_x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1(){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1750_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1751_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2));
v___x_1752_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1));
v___x_1753_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___boxed), 10, 0);
v___x_1754_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1750_, v___x_1751_, v___x_1752_, v___x_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___boxed(lean_object* v_a_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1();
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(lean_object* v___y_1757_){
_start:
{
lean_object* v___x_1759_; lean_object* v_ngen_1760_; lean_object* v_namePrefix_1761_; lean_object* v_idx_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1791_; 
v___x_1759_ = lean_st_ref_get(v___y_1757_);
v_ngen_1760_ = lean_ctor_get(v___x_1759_, 2);
lean_inc_ref(v_ngen_1760_);
lean_dec(v___x_1759_);
v_namePrefix_1761_ = lean_ctor_get(v_ngen_1760_, 0);
v_idx_1762_ = lean_ctor_get(v_ngen_1760_, 1);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_ngen_1760_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1764_ = v_ngen_1760_;
v_isShared_1765_ = v_isSharedCheck_1791_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_idx_1762_);
lean_inc(v_namePrefix_1761_);
lean_dec(v_ngen_1760_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1791_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; lean_object* v_env_1767_; lean_object* v_nextMacroScope_1768_; lean_object* v_auxDeclNGen_1769_; lean_object* v_traceState_1770_; lean_object* v_cache_1771_; lean_object* v_messages_1772_; lean_object* v_infoState_1773_; lean_object* v_snapshotTasks_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1789_; 
v___x_1766_ = lean_st_ref_take(v___y_1757_);
v_env_1767_ = lean_ctor_get(v___x_1766_, 0);
v_nextMacroScope_1768_ = lean_ctor_get(v___x_1766_, 1);
v_auxDeclNGen_1769_ = lean_ctor_get(v___x_1766_, 3);
v_traceState_1770_ = lean_ctor_get(v___x_1766_, 4);
v_cache_1771_ = lean_ctor_get(v___x_1766_, 5);
v_messages_1772_ = lean_ctor_get(v___x_1766_, 6);
v_infoState_1773_ = lean_ctor_get(v___x_1766_, 7);
v_snapshotTasks_1774_ = lean_ctor_get(v___x_1766_, 8);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1789_ == 0)
{
lean_object* v_unused_1790_; 
v_unused_1790_ = lean_ctor_get(v___x_1766_, 2);
lean_dec(v_unused_1790_);
v___x_1776_ = v___x_1766_;
v_isShared_1777_ = v_isSharedCheck_1789_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_snapshotTasks_1774_);
lean_inc(v_infoState_1773_);
lean_inc(v_messages_1772_);
lean_inc(v_cache_1771_);
lean_inc(v_traceState_1770_);
lean_inc(v_auxDeclNGen_1769_);
lean_inc(v_nextMacroScope_1768_);
lean_inc(v_env_1767_);
lean_dec(v___x_1766_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1789_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v_r_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1782_; 
lean_inc(v_idx_1762_);
lean_inc(v_namePrefix_1761_);
v_r_1778_ = l_Lean_Name_num___override(v_namePrefix_1761_, v_idx_1762_);
v___x_1779_ = lean_unsigned_to_nat(1u);
v___x_1780_ = lean_nat_add(v_idx_1762_, v___x_1779_);
lean_dec(v_idx_1762_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 1, v___x_1780_);
v___x_1782_ = v___x_1764_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_namePrefix_1761_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v___x_1780_);
v___x_1782_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1784_; 
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 2, v___x_1782_);
v___x_1784_ = v___x_1776_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_env_1767_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_nextMacroScope_1768_);
lean_ctor_set(v_reuseFailAlloc_1787_, 2, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1787_, 3, v_auxDeclNGen_1769_);
lean_ctor_set(v_reuseFailAlloc_1787_, 4, v_traceState_1770_);
lean_ctor_set(v_reuseFailAlloc_1787_, 5, v_cache_1771_);
lean_ctor_set(v_reuseFailAlloc_1787_, 6, v_messages_1772_);
lean_ctor_set(v_reuseFailAlloc_1787_, 7, v_infoState_1773_);
lean_ctor_set(v_reuseFailAlloc_1787_, 8, v_snapshotTasks_1774_);
v___x_1784_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = lean_st_ref_set(v___y_1757_, v___x_1784_);
v___x_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1786_, 0, v_r_1778_);
return v___x_1786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg___boxed(lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(v___y_1792_);
lean_dec(v___y_1792_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0(lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(v___y_1802_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___boxed(lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0(v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(lean_object* v_e_1815_, lean_object* v___y_1816_){
_start:
{
uint8_t v___x_1818_; 
v___x_1818_ = l_Lean_Expr_hasMVar(v_e_1815_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; 
v___x_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1819_, 0, v_e_1815_);
return v___x_1819_;
}
else
{
lean_object* v___x_1820_; lean_object* v_mctx_1821_; lean_object* v___x_1822_; lean_object* v_fst_1823_; lean_object* v_snd_1824_; lean_object* v___x_1825_; lean_object* v_cache_1826_; lean_object* v_zetaDeltaFVarIds_1827_; lean_object* v_postponed_1828_; lean_object* v_diag_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1838_; 
v___x_1820_ = lean_st_ref_get(v___y_1816_);
v_mctx_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc_ref(v_mctx_1821_);
lean_dec(v___x_1820_);
v___x_1822_ = l_Lean_instantiateMVarsCore(v_mctx_1821_, v_e_1815_);
v_fst_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_fst_1823_);
v_snd_1824_ = lean_ctor_get(v___x_1822_, 1);
lean_inc(v_snd_1824_);
lean_dec_ref(v___x_1822_);
v___x_1825_ = lean_st_ref_take(v___y_1816_);
v_cache_1826_ = lean_ctor_get(v___x_1825_, 1);
v_zetaDeltaFVarIds_1827_ = lean_ctor_get(v___x_1825_, 2);
v_postponed_1828_ = lean_ctor_get(v___x_1825_, 3);
v_diag_1829_ = lean_ctor_get(v___x_1825_, 4);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1838_ == 0)
{
lean_object* v_unused_1839_; 
v_unused_1839_ = lean_ctor_get(v___x_1825_, 0);
lean_dec(v_unused_1839_);
v___x_1831_ = v___x_1825_;
v_isShared_1832_ = v_isSharedCheck_1838_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_diag_1829_);
lean_inc(v_postponed_1828_);
lean_inc(v_zetaDeltaFVarIds_1827_);
lean_inc(v_cache_1826_);
lean_dec(v___x_1825_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1838_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v_snd_1824_);
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_snd_1824_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_cache_1826_);
lean_ctor_set(v_reuseFailAlloc_1837_, 2, v_zetaDeltaFVarIds_1827_);
lean_ctor_set(v_reuseFailAlloc_1837_, 3, v_postponed_1828_);
lean_ctor_set(v_reuseFailAlloc_1837_, 4, v_diag_1829_);
v___x_1834_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = lean_st_ref_set(v___y_1816_, v___x_1834_);
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v_fst_1823_);
return v___x_1836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg___boxed(lean_object* v_e_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(v_e_1840_, v___y_1841_);
lean_dec(v___y_1841_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1(lean_object* v_e_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(v_e_1844_, v___y_1850_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___boxed(lean_object* v_e_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1(v_e_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2(lean_object* v___x_1866_, lean_object* v___x_1867_, lean_object* v___x_1868_, lean_object* v___x_1869_, lean_object* v___x_1870_, lean_object* v_as_1871_, size_t v_sz_1872_, size_t v_i_1873_, lean_object* v_b_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_a_1885_; uint8_t v___x_1889_; 
v___x_1889_ = lean_usize_dec_lt(v_i_1873_, v_sz_1872_);
if (v___x_1889_ == 0)
{
lean_object* v___x_1890_; 
lean_dec_ref(v___x_1870_);
lean_dec_ref(v___x_1869_);
lean_dec_ref(v___x_1868_);
lean_dec(v___x_1867_);
lean_dec(v___x_1866_);
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v_b_1874_);
return v___x_1890_;
}
else
{
lean_object* v_fst_1891_; lean_object* v_snd_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1946_; 
v_fst_1891_ = lean_ctor_get(v_b_1874_, 0);
v_snd_1892_ = lean_ctor_get(v_b_1874_, 1);
v_isSharedCheck_1946_ = !lean_is_exclusive(v_b_1874_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1894_ = v_b_1874_;
v_isShared_1895_ = v_isSharedCheck_1946_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_snd_1892_);
lean_inc(v_fst_1891_);
lean_dec(v_b_1874_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1946_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v_a_1899_; lean_object* v___y_1901_; lean_object* v___x_1941_; 
v___x_1896_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_1897_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_1898_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v_a_1899_ = lean_array_uget_borrowed(v_as_1871_, v_i_1873_);
lean_inc(v_a_1899_);
lean_inc(v_fst_1891_);
lean_inc_ref(v___x_1869_);
v___x_1941_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(v___x_1869_, v_fst_1891_, v_a_1899_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
if (lean_obj_tag(v_a_1942_) == 0)
{
lean_object* v___x_1943_; 
lean_dec_ref(v___x_1941_);
lean_inc(v_a_1899_);
lean_inc(v_fst_1891_);
lean_inc_ref(v___x_1869_);
v___x_1943_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(v___x_1869_, v_fst_1891_, v_a_1899_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
if (lean_obj_tag(v_a_1944_) == 0)
{
lean_object* v___x_1945_; 
lean_dec_ref(v___x_1943_);
lean_inc(v_a_1899_);
lean_inc(v_fst_1891_);
lean_inc_ref(v___x_1869_);
v___x_1945_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(v___x_1869_, v_fst_1891_, v_a_1899_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
v___y_1901_ = v___x_1945_;
goto v___jp_1900_;
}
else
{
lean_dec_ref(v_a_1944_);
v___y_1901_ = v___x_1943_;
goto v___jp_1900_;
}
}
else
{
v___y_1901_ = v___x_1943_;
goto v___jp_1900_;
}
}
else
{
lean_dec_ref(v_a_1942_);
v___y_1901_ = v___x_1941_;
goto v___jp_1900_;
}
}
else
{
v___y_1901_ = v___x_1941_;
goto v___jp_1900_;
}
v___jp_1900_:
{
if (lean_obj_tag(v___y_1901_) == 0)
{
lean_object* v_a_1902_; 
v_a_1902_ = lean_ctor_get(v___y_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref(v___y_1901_);
if (lean_obj_tag(v_a_1902_) == 0)
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1903_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1);
lean_inc(v_fst_1891_);
v___x_1904_ = l_Lean_MessageData_ofExpr(v_fst_1891_);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1905_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
lean_inc(v_a_1899_);
v___x_1908_ = l_Lean_MessageData_ofSyntax(v_a_1899_);
v___x_1909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_1909_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v___x_1912_; 
lean_dec_ref(v___x_1910_);
if (v_isShared_1895_ == 0)
{
v___x_1912_ = v___x_1894_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_fst_1891_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_snd_1892_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
v_a_1885_ = v___x_1912_;
goto v___jp_1884_;
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_del_object(v___x_1894_);
lean_dec(v_snd_1892_);
lean_dec(v_fst_1891_);
lean_dec_ref(v___x_1870_);
lean_dec_ref(v___x_1869_);
lean_dec_ref(v___x_1868_);
lean_dec(v___x_1867_);
lean_dec(v___x_1866_);
v_a_1914_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1910_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1910_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
else
{
lean_object* v_val_1922_; lean_object* v_fst_1923_; lean_object* v_snd_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1932_; 
lean_del_object(v___x_1894_);
v_val_1922_ = lean_ctor_get(v_a_1902_, 0);
lean_inc(v_val_1922_);
lean_dec_ref(v_a_1902_);
v_fst_1923_ = lean_ctor_get(v_val_1922_, 0);
v_snd_1924_ = lean_ctor_get(v_val_1922_, 1);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_val_1922_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1926_ = v_val_1922_;
v_isShared_1927_ = v_isSharedCheck_1932_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_snd_1924_);
lean_inc(v_fst_1923_);
lean_dec(v_val_1922_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1932_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___f_1928_; lean_object* v___x_1930_; 
lean_inc_ref(v___x_1870_);
lean_inc(v_fst_1923_);
lean_inc_ref(v___x_1869_);
lean_inc_ref(v___x_1868_);
lean_inc(v___x_1867_);
lean_inc(v___x_1866_);
v___f_1928_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0), 13, 12);
lean_closure_set(v___f_1928_, 0, v___x_1896_);
lean_closure_set(v___f_1928_, 1, v___x_1897_);
lean_closure_set(v___f_1928_, 2, v___x_1898_);
lean_closure_set(v___f_1928_, 3, v___x_1866_);
lean_closure_set(v___f_1928_, 4, v___x_1867_);
lean_closure_set(v___f_1928_, 5, v___x_1868_);
lean_closure_set(v___f_1928_, 6, v___x_1869_);
lean_closure_set(v___f_1928_, 7, v_fst_1891_);
lean_closure_set(v___f_1928_, 8, v_fst_1923_);
lean_closure_set(v___f_1928_, 9, v___x_1870_);
lean_closure_set(v___f_1928_, 10, v_snd_1924_);
lean_closure_set(v___f_1928_, 11, v_snd_1892_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 1, v___f_1928_);
v___x_1930_ = v___x_1926_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_fst_1923_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v___f_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
v_a_1885_ = v___x_1930_;
goto v___jp_1884_;
}
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_del_object(v___x_1894_);
lean_dec(v_snd_1892_);
lean_dec(v_fst_1891_);
lean_dec_ref(v___x_1870_);
lean_dec_ref(v___x_1869_);
lean_dec_ref(v___x_1868_);
lean_dec(v___x_1867_);
lean_dec(v___x_1866_);
v_a_1933_ = lean_ctor_get(v___y_1901_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___y_1901_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___y_1901_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___y_1901_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
}
v___jp_1884_:
{
size_t v___x_1886_; size_t v___x_1887_; 
v___x_1886_ = ((size_t)1ULL);
v___x_1887_ = lean_usize_add(v_i_1873_, v___x_1886_);
v_i_1873_ = v___x_1887_;
v_b_1874_ = v_a_1885_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2___boxed(lean_object** _args){
lean_object* v___x_1947_ = _args[0];
lean_object* v___x_1948_ = _args[1];
lean_object* v___x_1949_ = _args[2];
lean_object* v___x_1950_ = _args[3];
lean_object* v___x_1951_ = _args[4];
lean_object* v_as_1952_ = _args[5];
lean_object* v_sz_1953_ = _args[6];
lean_object* v_i_1954_ = _args[7];
lean_object* v_b_1955_ = _args[8];
lean_object* v___y_1956_ = _args[9];
lean_object* v___y_1957_ = _args[10];
lean_object* v___y_1958_ = _args[11];
lean_object* v___y_1959_ = _args[12];
lean_object* v___y_1960_ = _args[13];
lean_object* v___y_1961_ = _args[14];
lean_object* v___y_1962_ = _args[15];
lean_object* v___y_1963_ = _args[16];
lean_object* v___y_1964_ = _args[17];
_start:
{
size_t v_sz_boxed_1965_; size_t v_i_boxed_1966_; lean_object* v_res_1967_; 
v_sz_boxed_1965_ = lean_unbox_usize(v_sz_1953_);
lean_dec(v_sz_1953_);
v_i_boxed_1966_ = lean_unbox_usize(v_i_1954_);
lean_dec(v_i_1954_);
v_res_1967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2(v___x_1947_, v___x_1948_, v___x_1949_, v___x_1950_, v___x_1951_, v_as_1952_, v_sz_boxed_1965_, v_i_boxed_1966_, v_b_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec_ref(v_as_1952_);
return v_res_1967_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1975_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__3));
v___x_1976_ = lean_unsigned_to_nat(33u);
v___x_1977_ = lean_unsigned_to_nat(175u);
v___x_1978_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__2));
v___x_1979_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15));
v___x_1980_ = l_mkPanicMessageWithDecl(v___x_1979_, v___x_1978_, v___x_1977_, v___x_1976_, v___x_1975_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0(lean_object* v___x_1981_, lean_object* v___x_1982_, uint8_t v___x_1983_, lean_object* v_u_1984_, lean_object* v_00_u03c3s_1985_, lean_object* v___x_1986_, lean_object* v_hyp_1987_, lean_object* v_hyps_1988_, lean_object* v_target_1989_, lean_object* v_args_1990_, lean_object* v_fst_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_Elab_Tactic_elabTerm(v___x_1981_, v___x_1982_, v___x_1983_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2003_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc_n(v_a_2002_, 2);
lean_dec_ref(v___x_2001_);
lean_inc(v___y_1999_);
lean_inc_ref(v___y_1998_);
lean_inc(v___y_1997_);
lean_inc_ref(v___y_1996_);
v___x_2003_ = lean_infer_type(v_a_2002_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref(v___x_2003_);
v___x_2005_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0));
v___x_2006_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_2007_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1));
v___x_2008_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0));
v___x_2009_ = lean_box(0);
lean_inc(v_u_1984_);
v___x_2010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2010_, 0, v_u_1984_);
lean_ctor_set(v___x_2010_, 1, v___x_2009_);
lean_inc_ref(v___x_2010_);
v___x_2011_ = l_Lean_mkConst(v___x_2008_, v___x_2010_);
lean_inc_ref(v_00_u03c3s_1985_);
v___x_2012_ = l_Lean_Expr_app___override(v___x_2011_, v_00_u03c3s_1985_);
v___x_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
v___x_2014_ = 0;
v___x_2015_ = lean_box(0);
v___x_2016_ = l_Lean_Meta_mkFreshExprMVar(v___x_2013_, v___x_2014_, v___x_2015_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc_n(v_a_2017_, 2);
lean_dec_ref(v___x_2016_);
v___x_2018_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__5));
lean_inc_ref(v___x_1986_);
v___x_2019_ = l_Lean_Name_mkStr5(v___x_2005_, v___x_2006_, v___x_2007_, v___x_1986_, v___x_2018_);
lean_inc_ref(v___x_2010_);
v___x_2020_ = l_Lean_mkConst(v___x_2019_, v___x_2010_);
lean_inc_ref(v_00_u03c3s_1985_);
lean_inc(v_a_2004_);
v___x_2021_ = l_Lean_mkApp3(v___x_2020_, v_a_2004_, v_00_u03c3s_1985_, v_a_2017_);
v___x_2022_ = lean_box(0);
v___x_2023_ = l_Lean_Meta_synthInstance(v___x_2021_, v___x_2022_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2025_; lean_object* v_a_2026_; lean_object* v___x_2027_; lean_object* v_a_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; size_t v_sz_2038_; size_t v___x_2039_; lean_object* v___x_2040_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref(v___x_2023_);
v___x_2025_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(v___y_1999_);
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref(v___x_2025_);
v___x_2027_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(v_a_2017_, v___y_1997_);
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref(v___x_2027_);
v___x_2029_ = l_Lean_TSyntax_getId(v_hyp_1987_);
v___x_2030_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
lean_ctor_set(v___x_2030_, 1, v_a_2026_);
lean_ctor_set(v___x_2030_, 2, v_a_2028_);
v___x_2031_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_2030_);
v___x_2032_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_2033_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__1));
v___x_2034_ = l_Lean_Name_mkStr6(v___x_2005_, v___x_2006_, v___x_2007_, v___x_1986_, v___x_2032_, v___x_2033_);
lean_inc_ref(v___x_2010_);
v___x_2035_ = l_Lean_mkConst(v___x_2034_, v___x_2010_);
lean_inc_ref_n(v_target_1989_, 2);
lean_inc_ref_n(v_hyps_1988_, 2);
lean_inc_ref(v___x_2031_);
lean_inc_ref_n(v_00_u03c3s_1985_, 2);
v___x_2036_ = lean_alloc_closure((void*)(l_Lean_mkApp8), 9, 8);
lean_closure_set(v___x_2036_, 0, v___x_2035_);
lean_closure_set(v___x_2036_, 1, v_00_u03c3s_1985_);
lean_closure_set(v___x_2036_, 2, v_a_2004_);
lean_closure_set(v___x_2036_, 3, v___x_2031_);
lean_closure_set(v___x_2036_, 4, v_hyps_1988_);
lean_closure_set(v___x_2036_, 5, v_target_1989_);
lean_closure_set(v___x_2036_, 6, v_a_2024_);
lean_closure_set(v___x_2036_, 7, v_a_2002_);
v___x_2037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2031_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
v_sz_2038_ = lean_array_size(v_args_1990_);
v___x_2039_ = ((size_t)0ULL);
lean_inc(v_u_1984_);
v___x_2040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2(v___x_2010_, v_u_1984_, v_00_u03c3s_1985_, v_hyps_1988_, v_target_1989_, v_args_1990_, v_sz_2038_, v___x_2039_, v___x_2037_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v_fst_2042_; lean_object* v_snd_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2072_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref(v___x_2040_);
v_fst_2042_ = lean_ctor_get(v_a_2041_, 0);
v_snd_2043_ = lean_ctor_get(v_a_2041_, 1);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_a_2041_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2045_ = v_a_2041_;
v_isShared_2046_ = v_isSharedCheck_2072_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_snd_2043_);
lean_inc(v_fst_2042_);
lean_dec(v_a_2041_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2072_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; 
lean_inc(v_fst_2042_);
v___x_2047_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_fst_2042_);
if (lean_obj_tag(v___x_2047_) == 1)
{
lean_object* v_val_2048_; lean_object* v___x_2049_; 
v_val_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_val_2048_);
lean_dec_ref(v___x_2047_);
lean_inc_ref(v_00_u03c3s_1985_);
v___x_2049_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_hyp_1987_, v_00_u03c3s_1985_, v_val_2048_, v___x_1983_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
lean_dec_ref(v___x_2049_);
lean_inc_ref(v_00_u03c3s_1985_);
lean_inc(v_u_1984_);
v___x_2050_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1984_, v_00_u03c3s_1985_, v_hyps_1988_, v_fst_2042_);
v___x_2051_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2051_, 0, v_u_1984_);
lean_ctor_set(v___x_2051_, 1, v_00_u03c3s_1985_);
lean_ctor_set(v___x_2051_, 2, v___x_2050_);
lean_ctor_set(v___x_2051_, 3, v_target_1989_);
v___x_2052_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_2051_);
v___x_2053_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2052_, v___x_2015_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2059_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc_n(v_a_2054_, 2);
lean_dec_ref(v___x_2053_);
v___x_2055_ = lean_apply_1(v_snd_2043_, v_a_2054_);
v___x_2056_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_fst_1991_, v___x_2055_, v___y_1997_);
lean_dec_ref(v___x_2056_);
v___x_2057_ = l_Lean_Expr_mvarId_x21(v_a_2054_);
lean_dec(v_a_2054_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set_tag(v___x_2045_, 1);
lean_ctor_set(v___x_2045_, 1, v___x_2009_);
lean_ctor_set(v___x_2045_, 0, v___x_2057_);
v___x_2059_ = v___x_2045_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v___x_2009_);
v___x_2059_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2059_, v___y_1993_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
return v___x_2060_;
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_del_object(v___x_2045_);
lean_dec(v_snd_2043_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v_fst_1991_);
v_a_2062_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2053_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2053_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
else
{
lean_del_object(v___x_2045_);
lean_dec(v_snd_2043_);
lean_dec(v_fst_2042_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v_fst_1991_);
lean_dec_ref(v_target_1989_);
lean_dec_ref(v_hyps_1988_);
lean_dec_ref(v_00_u03c3s_1985_);
lean_dec(v_u_1984_);
return v___x_2049_;
}
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
lean_dec(v___x_2047_);
lean_del_object(v___x_2045_);
lean_dec(v_snd_2043_);
lean_dec(v_fst_2042_);
lean_dec(v_fst_1991_);
lean_dec_ref(v_target_1989_);
lean_dec_ref(v_hyps_1988_);
lean_dec(v_hyp_1987_);
lean_dec_ref(v_00_u03c3s_1985_);
lean_dec(v_u_1984_);
v___x_2070_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4, &l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4);
v___x_2071_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(v___x_2070_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
return v___x_2071_;
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v_fst_1991_);
lean_dec_ref(v_target_1989_);
lean_dec_ref(v_hyps_1988_);
lean_dec(v_hyp_1987_);
lean_dec_ref(v_00_u03c3s_1985_);
lean_dec(v_u_1984_);
v_a_2073_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2040_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2040_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec(v_a_2017_);
lean_dec_ref(v___x_2010_);
lean_dec(v_a_2004_);
lean_dec(v_a_2002_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v_fst_1991_);
lean_dec_ref(v_target_1989_);
lean_dec_ref(v_hyps_1988_);
lean_dec(v_hyp_1987_);
lean_dec_ref(v___x_1986_);
lean_dec_ref(v_00_u03c3s_1985_);
lean_dec(v_u_1984_);
v_a_2081_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2023_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2023_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v___x_2010_);
lean_dec(v_a_2004_);
lean_dec(v_a_2002_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v_fst_1991_);
lean_dec_ref(v_target_1989_);
lean_dec_ref(v_hyps_1988_);
lean_dec(v_hyp_1987_);
lean_dec_ref(v___x_1986_);
lean_dec_ref(v_00_u03c3s_1985_);
lean_dec(v_u_1984_);
v_a_2089_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2016_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2016_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec(v_a_2002_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v_fst_1991_);
lean_dec_ref(v_target_1989_);
lean_dec_ref(v_hyps_1988_);
lean_dec(v_hyp_1987_);
lean_dec_ref(v___x_1986_);
lean_dec_ref(v_00_u03c3s_1985_);
lean_dec(v_u_1984_);
v_a_2097_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2003_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2003_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v_fst_1991_);
lean_dec_ref(v_target_1989_);
lean_dec_ref(v_hyps_1988_);
lean_dec(v_hyp_1987_);
lean_dec_ref(v___x_1986_);
lean_dec_ref(v_00_u03c3s_1985_);
lean_dec(v_u_1984_);
v_a_2105_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2001_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2001_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___boxed(lean_object** _args){
lean_object* v___x_2113_ = _args[0];
lean_object* v___x_2114_ = _args[1];
lean_object* v___x_2115_ = _args[2];
lean_object* v_u_2116_ = _args[3];
lean_object* v_00_u03c3s_2117_ = _args[4];
lean_object* v___x_2118_ = _args[5];
lean_object* v_hyp_2119_ = _args[6];
lean_object* v_hyps_2120_ = _args[7];
lean_object* v_target_2121_ = _args[8];
lean_object* v_args_2122_ = _args[9];
lean_object* v_fst_2123_ = _args[10];
lean_object* v___y_2124_ = _args[11];
lean_object* v___y_2125_ = _args[12];
lean_object* v___y_2126_ = _args[13];
lean_object* v___y_2127_ = _args[14];
lean_object* v___y_2128_ = _args[15];
lean_object* v___y_2129_ = _args[16];
lean_object* v___y_2130_ = _args[17];
lean_object* v___y_2131_ = _args[18];
lean_object* v___y_2132_ = _args[19];
_start:
{
uint8_t v___x_10840__boxed_2133_; lean_object* v_res_2134_; 
v___x_10840__boxed_2133_ = lean_unbox(v___x_2115_);
v_res_2134_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0(v___x_2113_, v___x_2114_, v___x_10840__boxed_2133_, v_u_2116_, v_00_u03c3s_2117_, v___x_2118_, v_hyp_2119_, v_hyps_2120_, v_target_2121_, v_args_2122_, v_fst_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec_ref(v_args_2122_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure(lean_object* v_x_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; 
v___x_2158_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_));
v___x_2159_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1));
lean_inc(v_x_2148_);
v___x_2160_ = l_Lean_Syntax_isOfKind(v_x_2148_, v___x_2159_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; 
lean_dec(v_x_2148_);
v___x_2161_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_2161_;
}
else
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; 
v___x_2162_ = lean_unsigned_to_nat(1u);
v___x_2163_ = l_Lean_Syntax_getArg(v_x_2148_, v___x_2162_);
v___x_2164_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4));
lean_inc(v___x_2163_);
v___x_2165_ = l_Lean_Syntax_isOfKind(v___x_2163_, v___x_2164_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2166_; 
lean_dec(v___x_2163_);
lean_dec(v_x_2148_);
v___x_2166_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_2166_;
}
else
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2167_ = lean_unsigned_to_nat(0u);
v___x_2168_ = lean_unsigned_to_nat(2u);
v___x_2169_ = l_Lean_Syntax_getArg(v_x_2148_, v___x_2168_);
v___x_2170_ = l_Lean_Syntax_matchesNull(v___x_2169_, v___x_2167_);
if (v___x_2170_ == 0)
{
lean_object* v___x_2171_; 
lean_dec(v___x_2163_);
lean_dec(v_x_2148_);
v___x_2171_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
return v___x_2171_;
}
else
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_2150_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v_snd_2174_; lean_object* v_fst_2175_; lean_object* v_u_2176_; lean_object* v_00_u03c3s_2177_; lean_object* v_hyps_2178_; lean_object* v_target_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v_hyp_2183_; lean_object* v_args_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; lean_object* v___x_2187_; lean_object* v___f_2188_; lean_object* v___x_2189_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
lean_dec_ref(v___x_2172_);
v_snd_2174_ = lean_ctor_get(v_a_2173_, 1);
lean_inc(v_snd_2174_);
v_fst_2175_ = lean_ctor_get(v_a_2173_, 0);
lean_inc_n(v_fst_2175_, 2);
lean_dec(v_a_2173_);
v_u_2176_ = lean_ctor_get(v_snd_2174_, 0);
lean_inc(v_u_2176_);
v_00_u03c3s_2177_ = lean_ctor_get(v_snd_2174_, 1);
lean_inc_ref(v_00_u03c3s_2177_);
v_hyps_2178_ = lean_ctor_get(v_snd_2174_, 2);
lean_inc_ref(v_hyps_2178_);
v_target_2179_ = lean_ctor_get(v_snd_2174_, 3);
lean_inc_ref(v_target_2179_);
lean_dec(v_snd_2174_);
v___x_2180_ = l_Lean_Syntax_getArg(v___x_2163_, v___x_2167_);
v___x_2181_ = l_Lean_Syntax_getArg(v___x_2163_, v___x_2162_);
lean_dec(v___x_2163_);
v___x_2182_ = lean_unsigned_to_nat(4u);
v_hyp_2183_ = l_Lean_Syntax_getArg(v_x_2148_, v___x_2182_);
lean_dec(v_x_2148_);
v_args_2184_ = l_Lean_Syntax_getArgs(v___x_2181_);
lean_dec(v___x_2181_);
v___x_2185_ = lean_box(0);
v___x_2186_ = 0;
v___x_2187_ = lean_box(v___x_2186_);
v___f_2188_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___boxed), 20, 11);
lean_closure_set(v___f_2188_, 0, v___x_2180_);
lean_closure_set(v___f_2188_, 1, v___x_2185_);
lean_closure_set(v___f_2188_, 2, v___x_2187_);
lean_closure_set(v___f_2188_, 3, v_u_2176_);
lean_closure_set(v___f_2188_, 4, v_00_u03c3s_2177_);
lean_closure_set(v___f_2188_, 5, v___x_2158_);
lean_closure_set(v___f_2188_, 6, v_hyp_2183_);
lean_closure_set(v___f_2188_, 7, v_hyps_2178_);
lean_closure_set(v___f_2188_, 8, v_target_2179_);
lean_closure_set(v___f_2188_, 9, v_args_2184_);
lean_closure_set(v___f_2188_, 10, v_fst_2175_);
v___x_2189_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_fst_2175_, v___f_2188_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
return v___x_2189_;
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec(v___x_2163_);
lean_dec(v_x_2148_);
v_a_2190_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2172_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2172_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___boxed(lean_object* v_x_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure(v_x_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
lean_dec(v_a_2206_);
lean_dec_ref(v_a_2205_);
lean_dec(v_a_2204_);
lean_dec_ref(v_a_2203_);
lean_dec(v_a_2202_);
lean_dec_ref(v_a_2201_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1(){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2218_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2219_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1));
v___x_2220_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1));
v___x_2221_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___boxed), 10, 0);
v___x_2222_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2218_, v___x_2219_, v___x_2220_, v___x_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___boxed(lean_object* v_a_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1();
return v_res_2224_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Specialize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = l_Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1();
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
