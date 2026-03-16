// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.Normalize.IntToBitVec
// Imports: public import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_ForEachExprWhere_initCache;
lean_object* lean_st_mk_ref(lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_mod(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClearMany_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_intToBitVecExt;
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "System"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Platform"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "numBits"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(244, 7, 92, 194, 164, 177, 167, 52)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(128, 236, 129, 7, 244, 3, 115, 42)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(195, 13, 33, 186, 170, 198, 65, 128)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "symm"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(220, 149, 144, 59, 77, 93, 25, 217)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3(lean_object*, lean_object*, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__13(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "z"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 196, 150, 181, 147, 170, 254, 79)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "casesOn"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(250, 240, 184, 175, 50, 245, 157, 81)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "failed to create binder due to failure when reverting variable dependencies"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 110, .m_capacity = 110, .m_length = 109, .m_data = "Detected USize/ISize in the goal but no hypothesis about System.Platform.numBits, consider case splitting on "};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "numBits_eq"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(244, 7, 92, 194, 164, 177, 167, 52)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(128, 236, 129, 7, 244, 3, 115, 42)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(65, 163, 238, 100, 187, 225, 152, 164)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__4;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__5;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toBitVec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(156, 179, 78, 164, 17, 99, 115, 128)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ISize"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(91, 57, 122, 235, 182, 82, 28, 168)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_handleSize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_handleSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "intToBitVec"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(130, 217, 71, 86, 75, 235, 18, 78)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg(lean_object* v_e_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_6_; lean_object* v_relevantTerms_7_; lean_object* v_relevantHyps_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_21_; 
v___x_6_ = lean_st_ref_take(v_a_4_);
v_relevantTerms_7_ = lean_ctor_get(v___x_6_, 0);
v_relevantHyps_8_ = lean_ctor_get(v___x_6_, 1);
v_isSharedCheck_21_ = !lean_is_exclusive(v___x_6_);
if (v_isSharedCheck_21_ == 0)
{
v___x_10_ = v___x_6_;
v_isShared_11_ = v_isSharedCheck_21_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_relevantHyps_8_);
lean_inc(v_relevantTerms_7_);
lean_dec(v___x_6_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_21_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_17_; 
v___x_12_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___closed__0));
v___x_13_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___closed__1));
v___x_14_ = lean_box(0);
v___x_15_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_12_, v___x_13_, v_relevantTerms_7_, v_e_3_, v___x_14_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_15_);
v___x_17_ = v___x_10_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_15_);
lean_ctor_set(v_reuseFailAlloc_20_, 1, v_relevantHyps_8_);
v___x_17_ = v_reuseFailAlloc_20_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_st_ref_set(v_a_4_, v___x_17_);
v___x_19_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_19_, 0, v___x_14_);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___boxed(lean_object* v_e_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg(v_e_22_, v_a_23_);
lean_dec(v_a_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm(lean_object* v_e_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v___x_33_; lean_object* v_relevantTerms_34_; lean_object* v_relevantHyps_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_48_; 
v___x_33_ = lean_st_ref_take(v_a_27_);
v_relevantTerms_34_ = lean_ctor_get(v___x_33_, 0);
v_relevantHyps_35_ = lean_ctor_get(v___x_33_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_48_ == 0)
{
v___x_37_ = v___x_33_;
v_isShared_38_ = v_isSharedCheck_48_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_relevantHyps_35_);
lean_inc(v_relevantTerms_34_);
lean_dec(v___x_33_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_48_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_44_; 
v___x_39_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___closed__0));
v___x_40_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___closed__1));
v___x_41_ = lean_box(0);
v___x_42_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_39_, v___x_40_, v_relevantTerms_34_, v_e_26_, v___x_41_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 0, v___x_42_);
v___x_44_ = v___x_37_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_42_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_relevantHyps_35_);
v___x_44_ = v_reuseFailAlloc_47_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_st_ref_set(v_a_27_, v___x_44_);
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_41_);
return v___x_46_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___boxed(lean_object* v_e_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm(v_e_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg(lean_object* v_f_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_62_; lean_object* v_relevantTerms_63_; lean_object* v_relevantHyps_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_77_; 
v___x_62_ = lean_st_ref_take(v_a_60_);
v_relevantTerms_63_ = lean_ctor_get(v___x_62_, 0);
v_relevantHyps_64_ = lean_ctor_get(v___x_62_, 1);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_77_ == 0)
{
v___x_66_ = v___x_62_;
v_isShared_67_ = v_isSharedCheck_77_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_relevantHyps_64_);
lean_inc(v_relevantTerms_63_);
lean_dec(v___x_62_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_77_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_68_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___closed__0));
v___x_69_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___closed__1));
v___x_70_ = lean_box(0);
v___x_71_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_68_, v___x_69_, v_relevantHyps_64_, v_f_59_, v___x_70_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 1, v___x_71_);
v___x_73_ = v___x_66_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_relevantTerms_63_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v___x_71_);
v___x_73_ = v_reuseFailAlloc_76_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_st_ref_set(v_a_60_, v___x_73_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_70_);
return v___x_75_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___boxed(lean_object* v_f_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg(v_f_78_, v_a_79_);
lean_dec(v_a_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp(lean_object* v_f_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v___x_89_; lean_object* v_relevantTerms_90_; lean_object* v_relevantHyps_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_104_; 
v___x_89_ = lean_st_ref_take(v_a_83_);
v_relevantTerms_90_ = lean_ctor_get(v___x_89_, 0);
v_relevantHyps_91_ = lean_ctor_get(v___x_89_, 1);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_104_ == 0)
{
v___x_93_ = v___x_89_;
v_isShared_94_ = v_isSharedCheck_104_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_relevantHyps_91_);
lean_inc(v_relevantTerms_90_);
lean_dec(v___x_89_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_104_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_95_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___closed__0));
v___x_96_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___closed__1));
v___x_97_ = lean_box(0);
v___x_98_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_95_, v___x_96_, v_relevantHyps_91_, v_f_82_, v___x_97_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 1, v___x_98_);
v___x_100_ = v___x_93_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_relevantTerms_90_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___x_98_);
v___x_100_ = v_reuseFailAlloc_103_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_st_ref_set(v_a_83_, v___x_100_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_97_);
return v___x_102_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___boxed(lean_object* v_f_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp(v_f_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(lean_object* v_e_113_, lean_object* v___y_114_){
_start:
{
uint8_t v___x_116_; 
v___x_116_ = l_Lean_Expr_hasMVar(v_e_113_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; 
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v_e_113_);
return v___x_117_;
}
else
{
lean_object* v___x_118_; lean_object* v_mctx_119_; lean_object* v___x_120_; lean_object* v_fst_121_; lean_object* v_snd_122_; lean_object* v___x_123_; lean_object* v_cache_124_; lean_object* v_zetaDeltaFVarIds_125_; lean_object* v_postponed_126_; lean_object* v_diag_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_136_; 
v___x_118_ = lean_st_ref_get(v___y_114_);
v_mctx_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc_ref(v_mctx_119_);
lean_dec(v___x_118_);
v___x_120_ = l_Lean_instantiateMVarsCore(v_mctx_119_, v_e_113_);
v_fst_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_fst_121_);
v_snd_122_ = lean_ctor_get(v___x_120_, 1);
lean_inc(v_snd_122_);
lean_dec_ref(v___x_120_);
v___x_123_ = lean_st_ref_take(v___y_114_);
v_cache_124_ = lean_ctor_get(v___x_123_, 1);
v_zetaDeltaFVarIds_125_ = lean_ctor_get(v___x_123_, 2);
v_postponed_126_ = lean_ctor_get(v___x_123_, 3);
v_diag_127_ = lean_ctor_get(v___x_123_, 4);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v___x_123_, 0);
lean_dec(v_unused_137_);
v___x_129_ = v___x_123_;
v_isShared_130_ = v_isSharedCheck_136_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_diag_127_);
lean_inc(v_postponed_126_);
lean_inc(v_zetaDeltaFVarIds_125_);
lean_inc(v_cache_124_);
lean_dec(v___x_123_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_136_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 0, v_snd_122_);
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_snd_122_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_cache_124_);
lean_ctor_set(v_reuseFailAlloc_135_, 2, v_zetaDeltaFVarIds_125_);
lean_ctor_set(v_reuseFailAlloc_135_, 3, v_postponed_126_);
lean_ctor_set(v_reuseFailAlloc_135_, 4, v_diag_127_);
v___x_132_ = v_reuseFailAlloc_135_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_st_ref_set(v___y_114_, v___x_132_);
v___x_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_134_, 0, v_fst_121_);
return v___x_134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg___boxed(lean_object* v_e_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_e_138_, v___y_139_);
lean_dec(v___y_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0(lean_object* v_e_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_e_142_, v___y_144_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0___boxed(lean_object* v_e_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0(v_e_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(lean_object* v_mvarId_156_, lean_object* v_x_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_156_, v_x_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_163_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_163_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
else
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
v_a_172_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_179_ == 0)
{
v___x_174_ = v___x_163_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_163_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_172_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg___boxed(lean_object* v_mvarId_180_, lean_object* v_x_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_mvarId_180_, v_x_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2(lean_object* v_00_u03b1_188_, lean_object* v_mvarId_189_, lean_object* v_x_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_mvarId_189_, v_x_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2___boxed(lean_object* v_00_u03b1_197_, lean_object* v_mvarId_198_, lean_object* v_x_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2(v_00_u03b1_197_, v_mvarId_198_, v_x_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
return v_res_205_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = l_Lean_Level_ofNat(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_box(0);
v___x_231_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11);
v___x_232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_230_);
return v___x_232_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12);
v___x_234_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10));
v___x_235_ = l_Lean_mkConst(v___x_234_, v___x_233_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1(lean_object* v_as_236_, size_t v_sz_237_, size_t v_i_238_, lean_object* v_b_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = lean_usize_dec_lt(v_i_238_, v_sz_237_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; 
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v_b_239_);
return v___x_246_;
}
else
{
lean_object* v_a_247_; lean_object* v___x_248_; 
lean_dec_ref(v_b_239_);
v_a_247_ = lean_array_uget_borrowed(v_as_236_, v_i_238_);
lean_inc_ref(v___y_240_);
lean_inc(v_a_247_);
v___x_248_ = l_Lean_FVarId_getType___redArg(v_a_247_, v___y_240_, v___y_242_, v___y_243_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_250_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
lean_dec_ref(v___x_248_);
v___x_250_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_a_249_, v___y_241_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_252_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
lean_dec_ref(v___x_250_);
v___x_252_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_251_, v___y_241_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v_a_255_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
lean_dec_ref(v___x_252_);
v___x_259_ = lean_box(0);
v___x_260_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0));
v___x_261_ = l_Lean_Expr_cleanupAnnotations(v_a_253_);
v___x_262_ = l_Lean_Expr_isApp(v___x_261_);
if (v___x_262_ == 0)
{
lean_dec_ref(v___x_261_);
v_a_255_ = v___x_260_;
goto v___jp_254_;
}
else
{
lean_object* v_arg_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_arg_263_ = lean_ctor_get(v___x_261_, 1);
lean_inc_ref(v_arg_263_);
v___x_264_ = l_Lean_Expr_appFnCleanup___redArg(v___x_261_);
v___x_265_ = l_Lean_Expr_isApp(v___x_264_);
if (v___x_265_ == 0)
{
lean_dec_ref(v___x_264_);
lean_dec_ref(v_arg_263_);
v_a_255_ = v___x_260_;
goto v___jp_254_;
}
else
{
lean_object* v_arg_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_arg_266_ = lean_ctor_get(v___x_264_, 1);
lean_inc_ref(v_arg_266_);
v___x_267_ = l_Lean_Expr_appFnCleanup___redArg(v___x_264_);
v___x_268_ = l_Lean_Expr_isApp(v___x_267_);
if (v___x_268_ == 0)
{
lean_dec_ref(v___x_267_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_263_);
v_a_255_ = v___x_260_;
goto v___jp_254_;
}
else
{
lean_object* v_arg_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_arg_269_ = lean_ctor_get(v___x_267_, 1);
lean_inc_ref(v_arg_269_);
v___x_270_ = l_Lean_Expr_appFnCleanup___redArg(v___x_267_);
v___x_271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2));
v___x_272_ = l_Lean_Expr_isConstOf(v___x_270_, v___x_271_);
lean_dec_ref(v___x_270_);
if (v___x_272_ == 0)
{
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_263_);
v_a_255_ = v___x_260_;
goto v___jp_254_;
}
else
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6));
v___x_274_ = l_Lean_Expr_isConstOf(v_arg_266_, v___x_273_);
if (v___x_274_ == 0)
{
uint8_t v___x_275_; 
lean_dec_ref(v_arg_269_);
v___x_275_ = l_Lean_Expr_isConstOf(v_arg_263_, v___x_273_);
lean_dec_ref(v_arg_263_);
if (v___x_275_ == 0)
{
lean_dec_ref(v_arg_266_);
v_a_255_ = v___x_260_;
goto v___jp_254_;
}
else
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Meta_getNatValue_x3f(v_arg_266_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec_ref(v_arg_266_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_300_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_300_ == 0)
{
v___x_279_ = v___x_276_;
v_isShared_280_ = v_isSharedCheck_300_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_300_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
if (lean_obj_tag(v_a_277_) == 1)
{
lean_object* v_val_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_295_; 
v_val_281_ = lean_ctor_get(v_a_277_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v_a_277_);
if (v_isSharedCheck_295_ == 0)
{
v___x_283_ = v_a_277_;
v_isShared_284_ = v_isSharedCheck_295_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_val_281_);
lean_dec(v_a_277_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_295_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
lean_inc(v_a_247_);
v___x_285_ = l_Lean_mkFVar(v_a_247_);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v_val_281_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_286_);
v___x_288_ = v___x_283_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_286_);
v___x_288_ = v_reuseFailAlloc_294_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v___x_259_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_290_);
v___x_292_ = v___x_279_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
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
else
{
lean_object* v___x_296_; lean_object* v___x_298_; 
lean_dec(v_a_277_);
v___x_296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8));
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_296_);
v___x_298_ = v___x_279_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
else
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
v_a_301_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_276_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_276_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
}
else
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Meta_getNatValue_x3f(v_arg_263_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_335_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_335_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_335_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_335_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
if (lean_obj_tag(v_a_310_) == 1)
{
lean_object* v_val_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_330_; 
v_val_314_ = lean_ctor_get(v_a_310_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v_a_310_);
if (v_isSharedCheck_330_ == 0)
{
v___x_316_ = v_a_310_;
v_isShared_317_ = v_isSharedCheck_330_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_val_314_);
lean_dec(v_a_310_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_330_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_318_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13);
lean_inc(v_a_247_);
v___x_319_ = l_Lean_mkFVar(v_a_247_);
v___x_320_ = l_Lean_mkApp4(v___x_318_, v_arg_269_, v_arg_266_, v_arg_263_, v___x_319_);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v_val_314_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_321_);
v___x_323_ = v___x_316_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_329_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v___x_259_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_325_);
v___x_327_ = v___x_312_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
else
{
lean_object* v___x_331_; lean_object* v___x_333_; 
lean_dec(v_a_310_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_263_);
v___x_331_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8));
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_331_);
v___x_333_ = v___x_312_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_263_);
v_a_336_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_309_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_309_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
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
}
}
}
}
v___jp_254_:
{
size_t v___x_256_; size_t v___x_257_; 
v___x_256_ = ((size_t)1ULL);
v___x_257_ = lean_usize_add(v_i_238_, v___x_256_);
v_i_238_ = v___x_257_;
v_b_239_ = v_a_255_;
goto _start;
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
v_a_344_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_252_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_252_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
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
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
v_a_352_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_250_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_250_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
v_a_360_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_248_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_248_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___boxed(lean_object* v_as_368_, lean_object* v_sz_369_, lean_object* v_i_370_, lean_object* v_b_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
size_t v_sz_boxed_377_; size_t v_i_boxed_378_; lean_object* v_res_379_; 
v_sz_boxed_377_ = lean_unbox_usize(v_sz_369_);
lean_dec(v_sz_369_);
v_i_boxed_378_ = lean_unbox_usize(v_i_370_);
lean_dec(v_i_370_);
v_res_379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1(v_as_368_, v_sz_boxed_377_, v_i_boxed_378_, v_b_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
lean_dec_ref(v_as_368_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___lam__0(lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; 
lean_inc(v___y_383_);
lean_inc_ref(v___y_382_);
lean_inc(v___y_381_);
lean_inc_ref(v___y_380_);
v___x_385_ = l_Lean_Meta_getPropHyps(v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_387_; lean_object* v___x_388_; size_t v_sz_389_; size_t v___x_390_; lean_object* v___x_391_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref(v___x_385_);
v___x_387_ = lean_box(0);
v___x_388_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0));
v_sz_389_ = lean_array_size(v_a_386_);
v___x_390_ = ((size_t)0ULL);
v___x_391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1(v_a_386_, v_sz_389_, v___x_390_, v___x_388_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v_a_386_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_404_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_404_ == 0)
{
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_404_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_404_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v_fst_396_; 
v_fst_396_ = lean_ctor_get(v_a_392_, 0);
lean_inc(v_fst_396_);
lean_dec(v_a_392_);
if (lean_obj_tag(v_fst_396_) == 0)
{
lean_object* v___x_398_; 
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_387_);
v___x_398_ = v___x_394_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_387_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
else
{
lean_object* v_val_400_; lean_object* v___x_402_; 
v_val_400_ = lean_ctor_get(v_fst_396_, 0);
lean_inc(v_val_400_);
lean_dec_ref(v_fst_396_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v_val_400_);
v___x_402_ = v___x_394_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_val_400_);
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
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
v_a_405_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_391_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_391_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
v_a_413_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_385_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_385_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___lam__0___boxed(lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___lam__0(v___y_421_, v___y_422_, v___y_423_, v___y_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq(lean_object* v_goal_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v___f_434_; lean_object* v___x_435_; 
v___f_434_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___closed__0));
v___x_435_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_goal_428_, v___f_434_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___boxed(lean_object* v_goal_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq(v_goal_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0(lean_object* v_x_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = lean_apply_6(v_x_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, lean_box(0));
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0___boxed(lean_object* v_x_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0(v_x_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(lean_object* v_mvarId_459_, lean_object* v_x_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___f_467_; lean_object* v___x_468_; 
v___f_467_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_467_, 0, v_x_460_);
lean_closure_set(v___f_467_, 1, v___y_461_);
v___x_468_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_459_, v___f_467_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
if (lean_obj_tag(v___x_468_) == 0)
{
return v___x_468_;
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___boxed(lean_object* v_mvarId_477_, lean_object* v_x_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_mvarId_477_, v_x_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14(lean_object* v_00_u03b1_486_, lean_object* v_mvarId_487_, lean_object* v_x_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_mvarId_487_, v_x_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___boxed(lean_object* v_00_u03b1_496_, lean_object* v_mvarId_497_, lean_object* v_x_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14(v_00_u03b1_496_, v_mvarId_497_, v_x_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(lean_object* v_a_506_, lean_object* v_x_507_){
_start:
{
if (lean_obj_tag(v_x_507_) == 0)
{
lean_object* v___x_508_; 
v___x_508_ = lean_box(0);
return v___x_508_;
}
else
{
lean_object* v_key_509_; lean_object* v_value_510_; lean_object* v_tail_511_; uint8_t v___x_512_; 
v_key_509_ = lean_ctor_get(v_x_507_, 0);
v_value_510_ = lean_ctor_get(v_x_507_, 1);
v_tail_511_ = lean_ctor_get(v_x_507_, 2);
v___x_512_ = lean_expr_eqv(v_key_509_, v_a_506_);
if (v___x_512_ == 0)
{
v_x_507_ = v_tail_511_;
goto _start;
}
else
{
lean_object* v___x_514_; 
lean_inc(v_value_510_);
v___x_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_514_, 0, v_value_510_);
return v___x_514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg___boxed(lean_object* v_a_515_, lean_object* v_x_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(v_a_515_, v_x_516_);
lean_dec(v_x_516_);
lean_dec_ref(v_a_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(lean_object* v_m_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_buckets_520_; lean_object* v___x_521_; uint64_t v___x_522_; uint64_t v___x_523_; uint64_t v___x_524_; uint64_t v_fold_525_; uint64_t v___x_526_; uint64_t v___x_527_; uint64_t v___x_528_; size_t v___x_529_; size_t v___x_530_; size_t v___x_531_; size_t v___x_532_; size_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_buckets_520_ = lean_ctor_get(v_m_518_, 1);
v___x_521_ = lean_array_get_size(v_buckets_520_);
v___x_522_ = l_Lean_Expr_hash(v_a_519_);
v___x_523_ = 32ULL;
v___x_524_ = lean_uint64_shift_right(v___x_522_, v___x_523_);
v_fold_525_ = lean_uint64_xor(v___x_522_, v___x_524_);
v___x_526_ = 16ULL;
v___x_527_ = lean_uint64_shift_right(v_fold_525_, v___x_526_);
v___x_528_ = lean_uint64_xor(v_fold_525_, v___x_527_);
v___x_529_ = lean_uint64_to_usize(v___x_528_);
v___x_530_ = lean_usize_of_nat(v___x_521_);
v___x_531_ = ((size_t)1ULL);
v___x_532_ = lean_usize_sub(v___x_530_, v___x_531_);
v___x_533_ = lean_usize_land(v___x_529_, v___x_532_);
v___x_534_ = lean_array_uget_borrowed(v_buckets_520_, v___x_533_);
v___x_535_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(v_a_519_, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3___redArg___boxed(lean_object* v_m_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(v_m_536_, v_a_537_);
lean_dec_ref(v_a_537_);
lean_dec_ref(v_m_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__0(lean_object* v_fst_539_, lean_object* v___y_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(v_fst_539_, v___y_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__0___boxed(lean_object* v_fst_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__0(v_fst_542_, v___y_543_);
lean_dec_ref(v___y_543_);
lean_dec(v_fst_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(lean_object* v_a_545_, lean_object* v_b_546_, lean_object* v_x_547_){
_start:
{
if (lean_obj_tag(v_x_547_) == 0)
{
lean_dec(v_b_546_);
lean_dec_ref(v_a_545_);
return v_x_547_;
}
else
{
lean_object* v_key_548_; lean_object* v_value_549_; lean_object* v_tail_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_562_; 
v_key_548_ = lean_ctor_get(v_x_547_, 0);
v_value_549_ = lean_ctor_get(v_x_547_, 1);
v_tail_550_ = lean_ctor_get(v_x_547_, 2);
v_isSharedCheck_562_ = !lean_is_exclusive(v_x_547_);
if (v_isSharedCheck_562_ == 0)
{
v___x_552_ = v_x_547_;
v_isShared_553_ = v_isSharedCheck_562_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_tail_550_);
lean_inc(v_value_549_);
lean_inc(v_key_548_);
lean_dec(v_x_547_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_562_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
uint8_t v___x_554_; 
v___x_554_ = lean_expr_eqv(v_key_548_, v_a_545_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_555_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(v_a_545_, v_b_546_, v_tail_550_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 2, v___x_555_);
v___x_557_ = v___x_552_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_key_548_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_value_549_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
else
{
lean_object* v___x_560_; 
lean_dec(v_value_549_);
lean_dec(v_key_548_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v_b_546_);
lean_ctor_set(v___x_552_, 0, v_a_545_);
v___x_560_ = v___x_552_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_545_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_b_546_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_tail_550_);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20___redArg(lean_object* v_x_563_, lean_object* v_x_564_){
_start:
{
if (lean_obj_tag(v_x_564_) == 0)
{
return v_x_563_;
}
else
{
lean_object* v_key_565_; lean_object* v_value_566_; lean_object* v_tail_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_590_; 
v_key_565_ = lean_ctor_get(v_x_564_, 0);
v_value_566_ = lean_ctor_get(v_x_564_, 1);
v_tail_567_ = lean_ctor_get(v_x_564_, 2);
v_isSharedCheck_590_ = !lean_is_exclusive(v_x_564_);
if (v_isSharedCheck_590_ == 0)
{
v___x_569_ = v_x_564_;
v_isShared_570_ = v_isSharedCheck_590_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_tail_567_);
lean_inc(v_value_566_);
lean_inc(v_key_565_);
lean_dec(v_x_564_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_590_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; uint64_t v___x_572_; uint64_t v___x_573_; uint64_t v___x_574_; uint64_t v_fold_575_; uint64_t v___x_576_; uint64_t v___x_577_; uint64_t v___x_578_; size_t v___x_579_; size_t v___x_580_; size_t v___x_581_; size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_571_ = lean_array_get_size(v_x_563_);
v___x_572_ = l_Lean_Expr_hash(v_key_565_);
v___x_573_ = 32ULL;
v___x_574_ = lean_uint64_shift_right(v___x_572_, v___x_573_);
v_fold_575_ = lean_uint64_xor(v___x_572_, v___x_574_);
v___x_576_ = 16ULL;
v___x_577_ = lean_uint64_shift_right(v_fold_575_, v___x_576_);
v___x_578_ = lean_uint64_xor(v_fold_575_, v___x_577_);
v___x_579_ = lean_uint64_to_usize(v___x_578_);
v___x_580_ = lean_usize_of_nat(v___x_571_);
v___x_581_ = ((size_t)1ULL);
v___x_582_ = lean_usize_sub(v___x_580_, v___x_581_);
v___x_583_ = lean_usize_land(v___x_579_, v___x_582_);
v___x_584_ = lean_array_uget_borrowed(v_x_563_, v___x_583_);
lean_inc(v___x_584_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 2, v___x_584_);
v___x_586_ = v___x_569_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_key_565_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_value_566_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v___x_584_);
v___x_586_ = v_reuseFailAlloc_589_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; 
v___x_587_ = lean_array_uset(v_x_563_, v___x_583_, v___x_586_);
v_x_563_ = v___x_587_;
v_x_564_ = v_tail_567_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3___redArg(lean_object* v_i_591_, lean_object* v_source_592_, lean_object* v_target_593_){
_start:
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = lean_array_get_size(v_source_592_);
v___x_595_ = lean_nat_dec_lt(v_i_591_, v___x_594_);
if (v___x_595_ == 0)
{
lean_dec_ref(v_source_592_);
lean_dec(v_i_591_);
return v_target_593_;
}
else
{
lean_object* v_es_596_; lean_object* v___x_597_; lean_object* v_source_598_; lean_object* v_target_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v_es_596_ = lean_array_fget(v_source_592_, v_i_591_);
v___x_597_ = lean_box(0);
v_source_598_ = lean_array_fset(v_source_592_, v_i_591_, v___x_597_);
v_target_599_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20___redArg(v_target_593_, v_es_596_);
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = lean_nat_add(v_i_591_, v___x_600_);
lean_dec(v_i_591_);
v_i_591_ = v___x_601_;
v_source_592_ = v_source_598_;
v_target_593_ = v_target_599_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(lean_object* v_data_603_){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v_nbuckets_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_604_ = lean_array_get_size(v_data_603_);
v___x_605_ = lean_unsigned_to_nat(2u);
v_nbuckets_606_ = lean_nat_mul(v___x_604_, v___x_605_);
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_box(0);
v___x_609_ = lean_mk_array(v_nbuckets_606_, v___x_608_);
v___x_610_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3___redArg(v___x_607_, v_data_603_, v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(lean_object* v_a_611_, lean_object* v_x_612_){
_start:
{
if (lean_obj_tag(v_x_612_) == 0)
{
uint8_t v___x_613_; 
v___x_613_ = 0;
return v___x_613_;
}
else
{
lean_object* v_key_614_; lean_object* v_tail_615_; uint8_t v___x_616_; 
v_key_614_ = lean_ctor_get(v_x_612_, 0);
v_tail_615_ = lean_ctor_get(v_x_612_, 2);
v___x_616_ = lean_expr_eqv(v_key_614_, v_a_611_);
if (v___x_616_ == 0)
{
v_x_612_ = v_tail_615_;
goto _start;
}
else
{
return v___x_616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg___boxed(lean_object* v_a_618_, lean_object* v_x_619_){
_start:
{
uint8_t v_res_620_; lean_object* v_r_621_; 
v_res_620_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_618_, v_x_619_);
lean_dec(v_x_619_);
lean_dec_ref(v_a_618_);
v_r_621_ = lean_box(v_res_620_);
return v_r_621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(lean_object* v_m_622_, lean_object* v_a_623_, lean_object* v_b_624_){
_start:
{
lean_object* v_size_625_; lean_object* v_buckets_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_669_; 
v_size_625_ = lean_ctor_get(v_m_622_, 0);
v_buckets_626_ = lean_ctor_get(v_m_622_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v_m_622_);
if (v_isSharedCheck_669_ == 0)
{
v___x_628_ = v_m_622_;
v_isShared_629_ = v_isSharedCheck_669_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_buckets_626_);
lean_inc(v_size_625_);
lean_dec(v_m_622_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_669_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; uint64_t v___x_631_; uint64_t v___x_632_; uint64_t v___x_633_; uint64_t v_fold_634_; uint64_t v___x_635_; uint64_t v___x_636_; uint64_t v___x_637_; size_t v___x_638_; size_t v___x_639_; size_t v___x_640_; size_t v___x_641_; size_t v___x_642_; lean_object* v_bkt_643_; uint8_t v___x_644_; 
v___x_630_ = lean_array_get_size(v_buckets_626_);
v___x_631_ = l_Lean_Expr_hash(v_a_623_);
v___x_632_ = 32ULL;
v___x_633_ = lean_uint64_shift_right(v___x_631_, v___x_632_);
v_fold_634_ = lean_uint64_xor(v___x_631_, v___x_633_);
v___x_635_ = 16ULL;
v___x_636_ = lean_uint64_shift_right(v_fold_634_, v___x_635_);
v___x_637_ = lean_uint64_xor(v_fold_634_, v___x_636_);
v___x_638_ = lean_uint64_to_usize(v___x_637_);
v___x_639_ = lean_usize_of_nat(v___x_630_);
v___x_640_ = ((size_t)1ULL);
v___x_641_ = lean_usize_sub(v___x_639_, v___x_640_);
v___x_642_ = lean_usize_land(v___x_638_, v___x_641_);
v_bkt_643_ = lean_array_uget_borrowed(v_buckets_626_, v___x_642_);
v___x_644_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_623_, v_bkt_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v_size_x27_646_; lean_object* v___x_647_; lean_object* v_buckets_x27_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_645_ = lean_unsigned_to_nat(1u);
v_size_x27_646_ = lean_nat_add(v_size_625_, v___x_645_);
lean_dec(v_size_625_);
lean_inc(v_bkt_643_);
v___x_647_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_647_, 0, v_a_623_);
lean_ctor_set(v___x_647_, 1, v_b_624_);
lean_ctor_set(v___x_647_, 2, v_bkt_643_);
v_buckets_x27_648_ = lean_array_uset(v_buckets_626_, v___x_642_, v___x_647_);
v___x_649_ = lean_unsigned_to_nat(4u);
v___x_650_ = lean_nat_mul(v_size_x27_646_, v___x_649_);
v___x_651_ = lean_unsigned_to_nat(3u);
v___x_652_ = lean_nat_div(v___x_650_, v___x_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_array_get_size(v_buckets_x27_648_);
v___x_654_ = lean_nat_dec_le(v___x_652_, v___x_653_);
lean_dec(v___x_652_);
if (v___x_654_ == 0)
{
lean_object* v_val_655_; lean_object* v___x_657_; 
v_val_655_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(v_buckets_x27_648_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v_val_655_);
lean_ctor_set(v___x_628_, 0, v_size_x27_646_);
v___x_657_ = v___x_628_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_size_x27_646_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_val_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
else
{
lean_object* v___x_660_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v_buckets_x27_648_);
lean_ctor_set(v___x_628_, 0, v_size_x27_646_);
v___x_660_ = v___x_628_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_size_x27_646_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_buckets_x27_648_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
else
{
lean_object* v___x_662_; lean_object* v_buckets_x27_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
lean_inc(v_bkt_643_);
v___x_662_ = lean_box(0);
v_buckets_x27_663_ = lean_array_uset(v_buckets_626_, v___x_642_, v___x_662_);
v___x_664_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(v_a_623_, v_b_624_, v_bkt_643_);
v___x_665_ = lean_array_uset(v_buckets_x27_663_, v___x_642_, v___x_664_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v___x_665_);
v___x_667_ = v___x_628_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_size_625_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_665_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(lean_object* v_as_670_, size_t v_sz_671_, size_t v_i_672_, lean_object* v_b_673_){
_start:
{
uint8_t v___x_675_; 
v___x_675_ = lean_usize_dec_lt(v_i_672_, v_sz_671_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; 
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v_b_673_);
return v___x_676_;
}
else
{
lean_object* v_snd_677_; lean_object* v_fst_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_711_; 
v_snd_677_ = lean_ctor_get(v_b_673_, 1);
v_fst_678_ = lean_ctor_get(v_b_673_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v_b_673_);
if (v_isSharedCheck_711_ == 0)
{
v___x_680_ = v_b_673_;
v_isShared_681_ = v_isSharedCheck_711_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_snd_677_);
lean_inc(v_fst_678_);
lean_dec(v_b_673_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_711_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_array_682_; lean_object* v_start_683_; lean_object* v_stop_684_; uint8_t v___x_685_; 
v_array_682_ = lean_ctor_get(v_snd_677_, 0);
v_start_683_ = lean_ctor_get(v_snd_677_, 1);
v_stop_684_ = lean_ctor_get(v_snd_677_, 2);
v___x_685_ = lean_nat_dec_lt(v_start_683_, v_stop_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_687_; 
if (v_isShared_681_ == 0)
{
v___x_687_ = v___x_680_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_fst_678_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_snd_677_);
v___x_687_ = v_reuseFailAlloc_689_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_688_; 
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
}
else
{
lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_707_; 
lean_inc(v_stop_684_);
lean_inc(v_start_683_);
lean_inc_ref(v_array_682_);
v_isSharedCheck_707_ = !lean_is_exclusive(v_snd_677_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; lean_object* v_unused_709_; lean_object* v_unused_710_; 
v_unused_708_ = lean_ctor_get(v_snd_677_, 2);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_snd_677_, 1);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v_snd_677_, 0);
lean_dec(v_unused_710_);
v___x_691_ = v_snd_677_;
v_isShared_692_ = v_isSharedCheck_707_;
goto v_resetjp_690_;
}
else
{
lean_dec(v_snd_677_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_707_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v_a_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v_a_693_ = lean_array_uget_borrowed(v_as_670_, v_i_672_);
v___x_694_ = lean_array_fget(v_array_682_, v_start_683_);
v___x_695_ = lean_unsigned_to_nat(1u);
v___x_696_ = lean_nat_add(v_start_683_, v___x_695_);
lean_dec(v_start_683_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v___x_696_);
v___x_698_ = v___x_691_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_array_682_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_706_, 2, v_stop_684_);
v___x_698_ = v_reuseFailAlloc_706_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; lean_object* v___x_701_; 
lean_inc(v_a_693_);
v___x_699_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(v_fst_678_, v_a_693_, v___x_694_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v___x_698_);
lean_ctor_set(v___x_680_, 0, v___x_699_);
v___x_701_ = v___x_680_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_698_);
v___x_701_ = v_reuseFailAlloc_705_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
size_t v___x_702_; size_t v___x_703_; 
v___x_702_ = ((size_t)1ULL);
v___x_703_ = lean_usize_add(v_i_672_, v___x_702_);
v_i_672_ = v___x_703_;
v_b_673_ = v___x_701_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2___redArg___boxed(lean_object* v_as_712_, lean_object* v_sz_713_, lean_object* v_i_714_, lean_object* v_b_715_, lean_object* v___y_716_){
_start:
{
size_t v_sz_boxed_717_; size_t v_i_boxed_718_; lean_object* v_res_719_; 
v_sz_boxed_717_ = lean_unbox_usize(v_sz_713_);
lean_dec(v_sz_713_);
v_i_boxed_718_ = lean_unbox_usize(v_i_714_);
lean_dec(v_i_714_);
v_res_719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(v_as_712_, v_sz_boxed_717_, v_i_boxed_718_, v_b_715_);
lean_dec_ref(v_as_712_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__1(lean_object* v___x_720_, lean_object* v___x_721_, lean_object* v_z_722_, lean_object* v___y_723_, size_t v___x_724_, lean_object* v_a_725_, uint8_t v___x_726_, lean_object* v_args_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; size_t v_sz_750_; lean_object* v___x_751_; 
v___x_734_ = lean_array_get_size(v_args_727_);
v___x_735_ = lean_nat_add(v___x_734_, v___x_720_);
v___x_736_ = lean_unsigned_to_nat(0u);
v___x_737_ = lean_unsigned_to_nat(4u);
v___x_738_ = lean_nat_mul(v___x_735_, v___x_737_);
lean_dec(v___x_735_);
v___x_739_ = lean_unsigned_to_nat(3u);
v___x_740_ = lean_nat_div(v___x_738_, v___x_739_);
lean_dec(v___x_738_);
v___x_741_ = l_Nat_nextPowerOfTwo(v___x_740_);
lean_dec(v___x_740_);
v___x_742_ = lean_box(0);
v___x_743_ = lean_mk_array(v___x_741_, v___x_742_);
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_736_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6));
v___x_746_ = l_Lean_mkConst(v___x_745_, v___x_721_);
v___x_747_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(v___x_744_, v___x_746_, v_z_722_);
lean_inc_ref(v_args_727_);
v___x_748_ = l_Array_toSubarray___redArg(v_args_727_, v___x_736_, v___x_734_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v_sz_750_ = lean_array_size(v___y_723_);
v___x_751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(v___y_723_, v_sz_750_, v___x_724_, v___x_749_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v_fst_753_; lean_object* v___f_754_; lean_object* v___x_755_; uint8_t v___x_756_; uint8_t v___x_757_; lean_object* v___x_758_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref(v___x_751_);
v_fst_753_ = lean_ctor_get(v_a_752_, 0);
lean_inc(v_fst_753_);
lean_dec(v_a_752_);
v___f_754_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__0___boxed), 2, 1);
lean_closure_set(v___f_754_, 0, v_fst_753_);
v___x_755_ = lean_replace_expr(v___f_754_, v_a_725_);
lean_dec_ref(v___f_754_);
v___x_756_ = 0;
v___x_757_ = 1;
v___x_758_ = l_Lean_Meta_mkForallFVars(v_args_727_, v___x_755_, v___x_756_, v___x_726_, v___x_726_, v___x_757_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec_ref(v_args_727_);
return v___x_758_;
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec_ref(v_args_727_);
v_a_759_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_751_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_751_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__1___boxed(lean_object* v___x_767_, lean_object* v___x_768_, lean_object* v_z_769_, lean_object* v___y_770_, lean_object* v___x_771_, lean_object* v_a_772_, lean_object* v___x_773_, lean_object* v_args_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
size_t v___x_21828__boxed_781_; uint8_t v___x_21830__boxed_782_; lean_object* v_res_783_; 
v___x_21828__boxed_781_ = lean_unbox_usize(v___x_771_);
lean_dec(v___x_771_);
v___x_21830__boxed_782_ = lean_unbox(v___x_773_);
v_res_783_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__1(v___x_767_, v___x_768_, v_z_769_, v___y_770_, v___x_21828__boxed_781_, v_a_772_, v___x_21830__boxed_782_, v_args_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v_a_772_);
lean_dec_ref(v___y_770_);
lean_dec(v___x_767_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4(lean_object* v___x_787_, size_t v_sz_788_, size_t v_i_789_, lean_object* v_bs_790_){
_start:
{
uint8_t v___x_791_; 
v___x_791_ = lean_usize_dec_lt(v_i_789_, v_sz_788_);
if (v___x_791_ == 0)
{
lean_dec_ref(v___x_787_);
return v_bs_790_;
}
else
{
lean_object* v___x_792_; lean_object* v_bs_x27_793_; lean_object* v___x_794_; lean_object* v___x_795_; size_t v___x_796_; size_t v___x_797_; lean_object* v___x_798_; 
v___x_792_ = lean_unsigned_to_nat(0u);
v_bs_x27_793_ = lean_array_uset(v_bs_790_, v_i_789_, v___x_792_);
v___x_794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4___closed__1));
lean_inc_ref(v___x_787_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
lean_ctor_set(v___x_795_, 1, v___x_787_);
v___x_796_ = ((size_t)1ULL);
v___x_797_ = lean_usize_add(v_i_789_, v___x_796_);
v___x_798_ = lean_array_uset(v_bs_x27_793_, v_i_789_, v___x_795_);
v_i_789_ = v___x_797_;
v_bs_790_ = v___x_798_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4___boxed(lean_object* v___x_800_, lean_object* v_sz_801_, lean_object* v_i_802_, lean_object* v_bs_803_){
_start:
{
size_t v_sz_boxed_804_; size_t v_i_boxed_805_; lean_object* v_res_806_; 
v_sz_boxed_804_ = lean_unbox_usize(v_sz_801_);
lean_dec(v_sz_801_);
v_i_boxed_805_ = lean_unbox_usize(v_i_802_);
lean_dec(v_i_802_);
v_res_806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4(v___x_800_, v_sz_boxed_804_, v_i_boxed_805_, v_bs_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0(lean_object* v_snd_807_, lean_object* v_x_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v_snd_807_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0___boxed(lean_object* v_snd_816_, lean_object* v_x_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0(v_snd_816_, v_x_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v_x_817_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9(size_t v_sz_825_, size_t v_i_826_, lean_object* v_bs_827_){
_start:
{
uint8_t v___x_828_; 
v___x_828_ = lean_usize_dec_lt(v_i_826_, v_sz_825_);
if (v___x_828_ == 0)
{
return v_bs_827_;
}
else
{
lean_object* v_v_829_; lean_object* v_fst_830_; lean_object* v_snd_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_845_; 
v_v_829_ = lean_array_uget(v_bs_827_, v_i_826_);
v_fst_830_ = lean_ctor_get(v_v_829_, 0);
v_snd_831_ = lean_ctor_get(v_v_829_, 1);
v_isSharedCheck_845_ = !lean_is_exclusive(v_v_829_);
if (v_isSharedCheck_845_ == 0)
{
v___x_833_ = v_v_829_;
v_isShared_834_ = v_isSharedCheck_845_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_snd_831_);
lean_inc(v_fst_830_);
lean_dec(v_v_829_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_845_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v_bs_x27_836_; lean_object* v___f_837_; lean_object* v___x_839_; 
v___x_835_ = lean_unsigned_to_nat(0u);
v_bs_x27_836_ = lean_array_uset(v_bs_827_, v_i_826_, v___x_835_);
v___f_837_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0___boxed), 8, 1);
lean_closure_set(v___f_837_, 0, v_snd_831_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v___f_837_);
v___x_839_ = v___x_833_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_fst_830_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___f_837_);
v___x_839_ = v_reuseFailAlloc_844_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
size_t v___x_840_; size_t v___x_841_; lean_object* v___x_842_; 
v___x_840_ = ((size_t)1ULL);
v___x_841_ = lean_usize_add(v_i_826_, v___x_840_);
v___x_842_ = lean_array_uset(v_bs_x27_836_, v_i_826_, v___x_839_);
v_i_826_ = v___x_841_;
v_bs_827_ = v___x_842_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___boxed(lean_object* v_sz_846_, lean_object* v_i_847_, lean_object* v_bs_848_){
_start:
{
size_t v_sz_boxed_849_; size_t v_i_boxed_850_; lean_object* v_res_851_; 
v_sz_boxed_849_ = lean_unbox_usize(v_sz_846_);
lean_dec(v_sz_846_);
v_i_boxed_850_ = lean_unbox_usize(v_i_847_);
lean_dec(v_i_847_);
v_res_851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9(v_sz_boxed_849_, v_i_boxed_850_, v_bs_848_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___lam__0(lean_object* v___x_852_, lean_object* v_a_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; lean_object* v___x_21416__overap_861_; lean_object* v___x_862_; 
v___x_860_ = l_Lean_instInhabitedExpr;
v___x_21416__overap_861_ = l_instInhabitedOfMonad___redArg(v___x_852_, v___x_860_);
v___x_862_ = lean_apply_6(v___x_21416__overap_861_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, lean_box(0));
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___lam__0___boxed(lean_object* v___x_863_, lean_object* v_a_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___lam__0(v___x_863_, v_a_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec_ref(v_a_864_);
return v_res_871_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_872_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__0);
v___x_874_ = l_ReaderT_instMonad___redArg(v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg___lam__0___boxed(lean_object* v_acc_879_, lean_object* v_declInfos_880_, lean_object* v_k_881_, lean_object* v_kind_882_, lean_object* v_inst_883_, lean_object* v___y_884_, lean_object* v_b_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
uint8_t v_kind_boxed_891_; lean_object* v_res_892_; 
v_kind_boxed_891_ = lean_unbox(v_kind_882_);
v_res_892_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg___lam__0(v_acc_879_, v_declInfos_880_, v_k_881_, v_kind_boxed_891_, v_inst_883_, v___y_884_, v_b_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg(lean_object* v_acc_893_, lean_object* v_declInfos_894_, lean_object* v_k_895_, uint8_t v_kind_896_, lean_object* v_inst_897_, lean_object* v_name_898_, uint8_t v_bi_899_, lean_object* v_type_900_, uint8_t v_kind_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; lean_object* v___f_909_; lean_object* v___x_910_; 
v___x_908_ = lean_box(v_kind_896_);
v___f_909_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_909_, 0, v_acc_893_);
lean_closure_set(v___f_909_, 1, v_declInfos_894_);
lean_closure_set(v___f_909_, 2, v_k_895_);
lean_closure_set(v___f_909_, 3, v___x_908_);
lean_closure_set(v___f_909_, 4, v_inst_897_);
lean_closure_set(v___f_909_, 5, v___y_902_);
v___x_910_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_898_, v_bi_899_, v_type_900_, v___f_909_, v_kind_901_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_910_) == 0)
{
return v___x_910_;
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_910_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg(lean_object* v_declInfos_919_, lean_object* v_k_920_, uint8_t v_kind_921_, lean_object* v_inst_922_, lean_object* v_acc_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v___x_930_; lean_object* v_toApplicative_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_1017_; 
v___x_930_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__1);
v_toApplicative_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_1017_ == 0)
{
lean_object* v_unused_1018_; 
v_unused_1018_ = lean_ctor_get(v___x_930_, 1);
lean_dec(v_unused_1018_);
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_1017_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_toApplicative_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_1017_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_toFunctor_935_; lean_object* v_toSeq_936_; lean_object* v_toSeqLeft_937_; lean_object* v_toSeqRight_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_1015_; 
v_toFunctor_935_ = lean_ctor_get(v_toApplicative_931_, 0);
v_toSeq_936_ = lean_ctor_get(v_toApplicative_931_, 2);
v_toSeqLeft_937_ = lean_ctor_get(v_toApplicative_931_, 3);
v_toSeqRight_938_ = lean_ctor_get(v_toApplicative_931_, 4);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_toApplicative_931_);
if (v_isSharedCheck_1015_ == 0)
{
lean_object* v_unused_1016_; 
v_unused_1016_ = lean_ctor_get(v_toApplicative_931_, 1);
lean_dec(v_unused_1016_);
v___x_940_ = v_toApplicative_931_;
v_isShared_941_ = v_isSharedCheck_1015_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_toSeqRight_938_);
lean_inc(v_toSeqLeft_937_);
lean_inc(v_toSeq_936_);
lean_inc(v_toFunctor_935_);
lean_dec(v_toApplicative_931_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_1015_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___f_942_; lean_object* v___f_943_; lean_object* v___f_944_; lean_object* v___f_945_; lean_object* v___x_946_; lean_object* v___f_947_; lean_object* v___f_948_; lean_object* v___f_949_; lean_object* v___x_951_; 
v___f_942_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__2));
v___f_943_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__3));
lean_inc_ref(v_toFunctor_935_);
v___f_944_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_944_, 0, v_toFunctor_935_);
v___f_945_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_945_, 0, v_toFunctor_935_);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v___f_944_);
lean_ctor_set(v___x_946_, 1, v___f_945_);
v___f_947_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_947_, 0, v_toSeqRight_938_);
v___f_948_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_948_, 0, v_toSeqLeft_937_);
v___f_949_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_949_, 0, v_toSeq_936_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 4, v___f_947_);
lean_ctor_set(v___x_940_, 3, v___f_948_);
lean_ctor_set(v___x_940_, 2, v___f_949_);
lean_ctor_set(v___x_940_, 1, v___f_942_);
lean_ctor_set(v___x_940_, 0, v___x_946_);
v___x_951_ = v___x_940_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v___f_942_);
lean_ctor_set(v_reuseFailAlloc_1014_, 2, v___f_949_);
lean_ctor_set(v_reuseFailAlloc_1014_, 3, v___f_948_);
lean_ctor_set(v_reuseFailAlloc_1014_, 4, v___f_947_);
v___x_951_ = v_reuseFailAlloc_1014_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_953_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v___f_943_);
lean_ctor_set(v___x_933_, 0, v___x_951_);
v___x_953_ = v___x_933_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v___f_943_);
v___x_953_ = v_reuseFailAlloc_1013_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_954_; lean_object* v_toApplicative_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_1011_; 
v___x_954_ = l_ReaderT_instMonad___redArg(v___x_953_);
v_toApplicative_955_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; 
v_unused_1012_ = lean_ctor_get(v___x_954_, 1);
lean_dec(v_unused_1012_);
v___x_957_ = v___x_954_;
v_isShared_958_ = v_isSharedCheck_1011_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_toApplicative_955_);
lean_dec(v___x_954_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_1011_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_toFunctor_959_; lean_object* v_toSeq_960_; lean_object* v_toSeqLeft_961_; lean_object* v_toSeqRight_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_1009_; 
v_toFunctor_959_ = lean_ctor_get(v_toApplicative_955_, 0);
v_toSeq_960_ = lean_ctor_get(v_toApplicative_955_, 2);
v_toSeqLeft_961_ = lean_ctor_get(v_toApplicative_955_, 3);
v_toSeqRight_962_ = lean_ctor_get(v_toApplicative_955_, 4);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_toApplicative_955_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; 
v_unused_1010_ = lean_ctor_get(v_toApplicative_955_, 1);
lean_dec(v_unused_1010_);
v___x_964_ = v_toApplicative_955_;
v_isShared_965_ = v_isSharedCheck_1009_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_toSeqRight_962_);
lean_inc(v_toSeqLeft_961_);
lean_inc(v_toSeq_960_);
lean_inc(v_toFunctor_959_);
lean_dec(v_toApplicative_955_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_1009_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___f_966_; lean_object* v___f_967_; lean_object* v___f_968_; lean_object* v___f_969_; lean_object* v___x_970_; lean_object* v___f_971_; lean_object* v___f_972_; lean_object* v___f_973_; lean_object* v___x_975_; 
v___f_966_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__4));
v___f_967_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__5));
lean_inc_ref(v_toFunctor_959_);
v___f_968_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_968_, 0, v_toFunctor_959_);
v___f_969_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_969_, 0, v_toFunctor_959_);
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v___f_968_);
lean_ctor_set(v___x_970_, 1, v___f_969_);
v___f_971_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_971_, 0, v_toSeqRight_962_);
v___f_972_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_972_, 0, v_toSeqLeft_961_);
v___f_973_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_973_, 0, v_toSeq_960_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 4, v___f_971_);
lean_ctor_set(v___x_964_, 3, v___f_972_);
lean_ctor_set(v___x_964_, 2, v___f_973_);
lean_ctor_set(v___x_964_, 1, v___f_966_);
lean_ctor_set(v___x_964_, 0, v___x_970_);
v___x_975_ = v___x_964_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v___f_966_);
lean_ctor_set(v_reuseFailAlloc_1008_, 2, v___f_973_);
lean_ctor_set(v_reuseFailAlloc_1008_, 3, v___f_972_);
lean_ctor_set(v_reuseFailAlloc_1008_, 4, v___f_971_);
v___x_975_ = v_reuseFailAlloc_1008_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_977_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v___f_967_);
lean_ctor_set(v___x_957_, 0, v___x_975_);
v___x_977_ = v___x_957_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v___f_967_);
v___x_977_ = v_reuseFailAlloc_1007_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_978_ = l_ReaderT_instMonad___redArg(v___x_977_);
v___x_979_ = lean_array_get_size(v_acc_923_);
v___x_980_ = lean_array_get_size(v_declInfos_919_);
v___x_981_ = lean_nat_dec_lt(v___x_979_, v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; 
lean_dec_ref(v___x_978_);
lean_dec(v_inst_922_);
lean_dec_ref(v_declInfos_919_);
v___x_982_ = lean_apply_7(v_k_920_, v_acc_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, lean_box(0));
return v___x_982_;
}
else
{
lean_object* v___f_983_; lean_object* v___x_984_; uint8_t v___x_985_; lean_object* v___f_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v_snd_991_; lean_object* v_fst_992_; lean_object* v_fst_993_; lean_object* v_snd_994_; lean_object* v___x_995_; 
v___f_983_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_983_, 0, v___x_978_);
v___x_984_ = lean_box(0);
v___x_985_ = 0;
v___f_986_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_986_, 0, v___f_983_);
v___x_987_ = lean_box(v___x_985_);
v___x_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v___f_986_);
v___x_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_984_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = lean_array_get_borrowed(v___x_989_, v_declInfos_919_, v___x_979_);
v_snd_991_ = lean_ctor_get(v___x_990_, 1);
v_fst_992_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_fst_992_);
v_fst_993_ = lean_ctor_get(v_snd_991_, 0);
v_snd_994_ = lean_ctor_get(v_snd_991_, 1);
lean_inc(v_snd_994_);
lean_inc(v___y_928_);
lean_inc_ref(v___y_927_);
lean_inc(v___y_926_);
lean_inc_ref(v___y_925_);
lean_inc(v___y_924_);
lean_inc_ref(v_acc_923_);
v___x_995_ = lean_apply_7(v_snd_994_, v_acc_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, lean_box(0));
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; uint8_t v___x_997_; lean_object* v___x_998_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref(v___x_995_);
v___x_997_ = lean_unbox(v_fst_993_);
v___x_998_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg(v_acc_923_, v_declInfos_919_, v_k_920_, v_kind_921_, v_inst_922_, v_fst_992_, v___x_997_, v_a_996_, v_kind_921_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
return v___x_998_;
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec(v_fst_992_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v_acc_923_);
lean_dec(v_inst_922_);
lean_dec_ref(v_k_920_);
lean_dec_ref(v_declInfos_919_);
v_a_999_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_995_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_995_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg___lam__0(lean_object* v_acc_1019_, lean_object* v_declInfos_1020_, lean_object* v_k_1021_, uint8_t v_kind_1022_, lean_object* v_inst_1023_, lean_object* v___y_1024_, lean_object* v_b_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_array_push(v_acc_1019_, v_b_1025_);
v___x_1032_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg(v_declInfos_1020_, v_k_1021_, v_kind_1022_, v_inst_1023_, v___x_1031_, v___y_1024_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg___boxed(lean_object* v_acc_1033_, lean_object* v_declInfos_1034_, lean_object* v_k_1035_, lean_object* v_kind_1036_, lean_object* v_inst_1037_, lean_object* v_name_1038_, lean_object* v_bi_1039_, lean_object* v_type_1040_, lean_object* v_kind_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
uint8_t v_kind_boxed_1048_; uint8_t v_bi_boxed_1049_; uint8_t v_kind_boxed_1050_; lean_object* v_res_1051_; 
v_kind_boxed_1048_ = lean_unbox(v_kind_1036_);
v_bi_boxed_1049_ = lean_unbox(v_bi_1039_);
v_kind_boxed_1050_ = lean_unbox(v_kind_1041_);
v_res_1051_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg(v_acc_1033_, v_declInfos_1034_, v_k_1035_, v_kind_boxed_1048_, v_inst_1037_, v_name_1038_, v_bi_boxed_1049_, v_type_1040_, v_kind_boxed_1050_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___boxed(lean_object* v_declInfos_1052_, lean_object* v_k_1053_, lean_object* v_kind_1054_, lean_object* v_inst_1055_, lean_object* v_acc_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
uint8_t v_kind_boxed_1063_; lean_object* v_res_1064_; 
v_kind_boxed_1063_ = lean_unbox(v_kind_1054_);
v_res_1064_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg(v_declInfos_1052_, v_k_1053_, v_kind_boxed_1063_, v_inst_1055_, v_acc_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg(lean_object* v_inst_1067_, lean_object* v_declInfos_1068_, lean_object* v_k_1069_, uint8_t v_kind_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg___closed__0));
v___x_1078_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg(v_declInfos_1068_, v_k_1069_, v_kind_1070_, v_inst_1067_, v___x_1077_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg___boxed(lean_object* v_inst_1079_, lean_object* v_declInfos_1080_, lean_object* v_k_1081_, lean_object* v_kind_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
uint8_t v_kind_boxed_1089_; lean_object* v_res_1090_; 
v_kind_boxed_1089_ = lean_unbox(v_kind_1082_);
v_res_1090_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg(v_inst_1079_, v_declInfos_1080_, v_k_1081_, v_kind_boxed_1089_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(size_t v_sz_1091_, size_t v_i_1092_, lean_object* v_bs_1093_){
_start:
{
uint8_t v___x_1094_; 
v___x_1094_ = lean_usize_dec_lt(v_i_1092_, v_sz_1091_);
if (v___x_1094_ == 0)
{
return v_bs_1093_;
}
else
{
lean_object* v_v_1095_; lean_object* v_fst_1096_; lean_object* v_snd_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1113_; 
v_v_1095_ = lean_array_uget(v_bs_1093_, v_i_1092_);
v_fst_1096_ = lean_ctor_get(v_v_1095_, 0);
v_snd_1097_ = lean_ctor_get(v_v_1095_, 1);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_v_1095_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1099_ = v_v_1095_;
v_isShared_1100_ = v_isSharedCheck_1113_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_snd_1097_);
lean_inc(v_fst_1096_);
lean_dec(v_v_1095_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1113_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1101_; lean_object* v_bs_x27_1102_; uint8_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1101_ = lean_unsigned_to_nat(0u);
v_bs_x27_1102_ = lean_array_uset(v_bs_1093_, v_i_1092_, v___x_1101_);
v___x_1103_ = 0;
v___x_1104_ = lean_box(v___x_1103_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1104_);
v___x_1106_ = v___x_1099_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_snd_1097_);
v___x_1106_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1107_; size_t v___x_1108_; size_t v___x_1109_; lean_object* v___x_1110_; 
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v_fst_1096_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = ((size_t)1ULL);
v___x_1109_ = lean_usize_add(v_i_1092_, v___x_1108_);
v___x_1110_ = lean_array_uset(v_bs_x27_1102_, v_i_1092_, v___x_1107_);
v_i_1092_ = v___x_1109_;
v_bs_1093_ = v___x_1110_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13___boxed(lean_object* v_sz_1114_, lean_object* v_i_1115_, lean_object* v_bs_1116_){
_start:
{
size_t v_sz_boxed_1117_; size_t v_i_boxed_1118_; lean_object* v_res_1119_; 
v_sz_boxed_1117_ = lean_unbox_usize(v_sz_1114_);
lean_dec(v_sz_1114_);
v_i_boxed_1118_ = lean_unbox_usize(v_i_1115_);
lean_dec(v_i_1115_);
v_res_1119_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(v_sz_boxed_1117_, v_i_boxed_1118_, v_bs_1116_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___redArg(lean_object* v_inst_1120_, lean_object* v_declInfos_1121_, lean_object* v_k_1122_, uint8_t v_kind_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
size_t v_sz_1130_; size_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v_sz_1130_ = lean_array_size(v_declInfos_1121_);
v___x_1131_ = ((size_t)0ULL);
v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(v_sz_1130_, v___x_1131_, v_declInfos_1121_);
v___x_1133_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg(v_inst_1120_, v___x_1132_, v_k_1122_, v_kind_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___redArg___boxed(lean_object* v_inst_1134_, lean_object* v_declInfos_1135_, lean_object* v_k_1136_, lean_object* v_kind_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
uint8_t v_kind_boxed_1144_; lean_object* v_res_1145_; 
v_kind_boxed_1144_ = lean_unbox(v_kind_1137_);
v_res_1145_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___redArg(v_inst_1134_, v_declInfos_1135_, v_k_1136_, v_kind_boxed_1144_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5___redArg(lean_object* v_inst_1146_, lean_object* v_declInfos_1147_, lean_object* v_k_1148_, uint8_t v_kind_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
size_t v_sz_1156_; size_t v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_sz_1156_ = lean_array_size(v_declInfos_1147_);
v___x_1157_ = ((size_t)0ULL);
v___x_1158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9(v_sz_1156_, v___x_1157_, v_declInfos_1147_);
v___x_1159_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___redArg(v_inst_1146_, v___x_1158_, v_k_1148_, v_kind_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5___redArg___boxed(lean_object* v_inst_1160_, lean_object* v_declInfos_1161_, lean_object* v_k_1162_, lean_object* v_kind_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
uint8_t v_kind_boxed_1170_; lean_object* v_res_1171_; 
v_kind_boxed_1170_ = lean_unbox(v_kind_1163_);
v_res_1171_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5___redArg(v_inst_1160_, v_declInfos_1161_, v_k_1162_, v_kind_boxed_1170_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2(lean_object* v___x_1175_, lean_object* v_z_1176_, lean_object* v___y_1177_, size_t v___x_1178_, lean_object* v___x_1179_, lean_object* v___f_1180_, lean_object* v___x_1181_, uint8_t v___x_1182_, lean_object* v_other_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; size_t v_sz_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; lean_object* v___x_1196_; 
v___x_1190_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1));
v___x_1191_ = l_Lean_mkConst(v___x_1190_, v___x_1175_);
lean_inc_ref(v_z_1176_);
v___x_1192_ = l_Lean_Expr_app___override(v___x_1191_, v_z_1176_);
v_sz_1193_ = lean_array_size(v___y_1177_);
v___x_1194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4(v___x_1192_, v_sz_1193_, v___x_1178_, v___y_1177_);
v___x_1195_ = 0;
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
lean_inc(v___y_1186_);
lean_inc_ref(v___y_1185_);
v___x_1196_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5___redArg(v___x_1179_, v___x_1194_, v___f_1180_, v___x_1195_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; uint8_t v___x_1204_; lean_object* v___x_1205_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref(v___x_1196_);
lean_inc_ref(v_z_1176_);
v___x_1198_ = l_Lean_Expr_replaceFVar(v_a_1197_, v_z_1176_, v___x_1181_);
v___x_1199_ = lean_unsigned_to_nat(2u);
v___x_1200_ = lean_mk_empty_array_with_capacity(v___x_1199_);
v___x_1201_ = lean_array_push(v___x_1200_, v_z_1176_);
v___x_1202_ = lean_array_push(v___x_1201_, v_other_1183_);
v___x_1203_ = 0;
v___x_1204_ = 1;
v___x_1205_ = l_Lean_Meta_mkLambdaFVars(v___x_1202_, v_a_1197_, v___x_1203_, v___x_1182_, v___x_1203_, v___x_1182_, v___x_1204_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec_ref(v___x_1202_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1214_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v_a_1206_);
lean_ctor_set(v___x_1210_, 1, v___x_1198_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1210_);
v___x_1212_ = v___x_1208_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec_ref(v___x_1198_);
v_a_1215_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1205_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1205_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec_ref(v_other_1183_);
lean_dec_ref(v_z_1176_);
v_a_1223_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1196_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1196_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___boxed(lean_object* v___x_1231_, lean_object* v_z_1232_, lean_object* v___y_1233_, lean_object* v___x_1234_, lean_object* v___x_1235_, lean_object* v___f_1236_, lean_object* v___x_1237_, lean_object* v___x_1238_, lean_object* v_other_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
size_t v___x_22435__boxed_1246_; uint8_t v___x_22439__boxed_1247_; lean_object* v_res_1248_; 
v___x_22435__boxed_1246_ = lean_unbox_usize(v___x_1234_);
lean_dec(v___x_1234_);
v___x_22439__boxed_1247_ = lean_unbox(v___x_1238_);
v_res_1248_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2(v___x_1231_, v_z_1232_, v___y_1233_, v___x_22435__boxed_1246_, v___x_1235_, v___f_1236_, v___x_1237_, v___x_22439__boxed_1247_, v_other_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec_ref(v___x_1237_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0(lean_object* v_k_1249_, lean_object* v___y_1250_, lean_object* v_b_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_apply_7(v_k_1249_, v_b_1251_, v___y_1250_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, lean_box(0));
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0___boxed(lean_object* v_k_1258_, lean_object* v___y_1259_, lean_object* v_b_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0(v_k_1258_, v___y_1259_, v_b_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(lean_object* v_name_1267_, uint8_t v_bi_1268_, lean_object* v_type_1269_, lean_object* v_k_1270_, uint8_t v_kind_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___f_1278_; lean_object* v___x_1279_; 
v___f_1278_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1278_, 0, v_k_1270_);
lean_closure_set(v___f_1278_, 1, v___y_1272_);
v___x_1279_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1267_, v_bi_1268_, v_type_1269_, v___f_1278_, v_kind_1271_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
if (lean_obj_tag(v___x_1279_) == 0)
{
return v___x_1279_;
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___boxed(lean_object* v_name_1288_, lean_object* v_bi_1289_, lean_object* v_type_1290_, lean_object* v_k_1291_, lean_object* v_kind_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
uint8_t v_bi_boxed_1299_; uint8_t v_kind_boxed_1300_; lean_object* v_res_1301_; 
v_bi_boxed_1299_ = lean_unbox(v_bi_1289_);
v_kind_boxed_1300_ = lean_unbox(v_kind_1292_);
v_res_1301_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(v_name_1288_, v_bi_boxed_1299_, v_type_1290_, v_k_1291_, v_kind_boxed_1300_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(lean_object* v_name_1302_, lean_object* v_type_1303_, lean_object* v_k_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
uint8_t v___x_1311_; uint8_t v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = 0;
v___x_1312_ = 0;
v___x_1313_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(v_name_1302_, v___x_1311_, v_type_1303_, v_k_1304_, v___x_1312_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg___boxed(lean_object* v_name_1314_, lean_object* v_type_1315_, lean_object* v_k_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v_name_1314_, v_type_1315_, v_k_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3(lean_object* v___x_1327_, lean_object* v___y_1328_, size_t v___x_1329_, lean_object* v_a_1330_, uint8_t v___x_1331_, lean_object* v_fst_1332_, lean_object* v___x_1333_, lean_object* v___x_1334_, lean_object* v_z_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___f_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___f_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1342_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2));
v___x_1343_ = lean_unsigned_to_nat(1u);
v___x_1344_ = lean_box_usize(v___x_1329_);
v___x_1345_ = lean_box(v___x_1331_);
lean_inc_ref(v___y_1328_);
lean_inc_ref(v_z_1335_);
lean_inc(v___x_1327_);
v___f_1346_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1346_, 0, v___x_1343_);
lean_closure_set(v___f_1346_, 1, v___x_1327_);
lean_closure_set(v___f_1346_, 2, v_z_1335_);
lean_closure_set(v___f_1346_, 3, v___y_1328_);
lean_closure_set(v___f_1346_, 4, v___x_1344_);
lean_closure_set(v___f_1346_, 5, v_a_1330_);
lean_closure_set(v___f_1346_, 6, v___x_1345_);
v___x_1347_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11);
lean_inc(v___x_1327_);
v___x_1348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
lean_ctor_set(v___x_1348_, 1, v___x_1327_);
v___x_1349_ = l_Lean_mkConst(v___x_1342_, v___x_1348_);
v___x_1350_ = l_Lean_mkNatLit(v_fst_1332_);
v___x_1351_ = lean_box_usize(v___x_1329_);
v___x_1352_ = lean_box(v___x_1331_);
lean_inc_ref(v___x_1350_);
lean_inc_ref(v_z_1335_);
v___f_1353_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___boxed), 15, 8);
lean_closure_set(v___f_1353_, 0, v___x_1327_);
lean_closure_set(v___f_1353_, 1, v_z_1335_);
lean_closure_set(v___f_1353_, 2, v___y_1328_);
lean_closure_set(v___f_1353_, 3, v___x_1351_);
lean_closure_set(v___f_1353_, 4, v___x_1333_);
lean_closure_set(v___f_1353_, 5, v___f_1346_);
lean_closure_set(v___f_1353_, 6, v___x_1350_);
lean_closure_set(v___f_1353_, 7, v___x_1352_);
v___x_1354_ = l_Lean_mkApp3(v___x_1349_, v___x_1334_, v___x_1350_, v_z_1335_);
v___x_1355_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1));
v___x_1356_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v___x_1355_, v___x_1354_, v___f_1353_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___boxed(lean_object* v___x_1357_, lean_object* v___y_1358_, lean_object* v___x_1359_, lean_object* v_a_1360_, lean_object* v___x_1361_, lean_object* v_fst_1362_, lean_object* v___x_1363_, lean_object* v___x_1364_, lean_object* v_z_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
size_t v___x_22651__boxed_1372_; uint8_t v___x_22653__boxed_1373_; lean_object* v_res_1374_; 
v___x_22651__boxed_1372_ = lean_unbox_usize(v___x_1359_);
lean_dec(v___x_1359_);
v___x_22653__boxed_1373_ = lean_unbox(v___x_1361_);
v_res_1374_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3(v___x_1357_, v___y_1358_, v___x_22651__boxed_1372_, v_a_1360_, v___x_22653__boxed_1373_, v_fst_1362_, v___x_1363_, v___x_1364_, v_z_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__10(lean_object* v_x_1375_, lean_object* v_x_1376_){
_start:
{
if (lean_obj_tag(v_x_1376_) == 0)
{
return v_x_1375_;
}
else
{
lean_object* v_key_1377_; lean_object* v_tail_1378_; lean_object* v___x_1379_; 
v_key_1377_ = lean_ctor_get(v_x_1376_, 0);
lean_inc(v_key_1377_);
v_tail_1378_ = lean_ctor_get(v_x_1376_, 2);
lean_inc(v_tail_1378_);
lean_dec_ref(v_x_1376_);
v___x_1379_ = lean_array_push(v_x_1375_, v_key_1377_);
v_x_1375_ = v___x_1379_;
v_x_1376_ = v_tail_1378_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__11(lean_object* v_as_1381_, size_t v_i_1382_, size_t v_stop_1383_, lean_object* v_b_1384_){
_start:
{
uint8_t v___x_1385_; 
v___x_1385_ = lean_usize_dec_eq(v_i_1382_, v_stop_1383_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; size_t v___x_1388_; size_t v___x_1389_; 
v___x_1386_ = lean_array_uget_borrowed(v_as_1381_, v_i_1382_);
lean_inc(v___x_1386_);
v___x_1387_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__10(v_b_1384_, v___x_1386_);
v___x_1388_ = ((size_t)1ULL);
v___x_1389_ = lean_usize_add(v_i_1382_, v___x_1388_);
v_i_1382_ = v___x_1389_;
v_b_1384_ = v___x_1387_;
goto _start;
}
else
{
return v_b_1384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__11___boxed(lean_object* v_as_1391_, lean_object* v_i_1392_, lean_object* v_stop_1393_, lean_object* v_b_1394_){
_start:
{
size_t v_i_boxed_1395_; size_t v_stop_boxed_1396_; lean_object* v_res_1397_; 
v_i_boxed_1395_ = lean_unbox_usize(v_i_1392_);
lean_dec(v_i_1392_);
v_stop_boxed_1396_ = lean_unbox_usize(v_stop_1393_);
lean_dec(v_stop_1393_);
v_res_1397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__11(v_as_1391_, v_i_boxed_1395_, v_stop_boxed_1396_, v_b_1394_);
lean_dec_ref(v_as_1391_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__8(size_t v_sz_1398_, size_t v_i_1399_, lean_object* v_bs_1400_){
_start:
{
uint8_t v___x_1401_; 
v___x_1401_ = lean_usize_dec_lt(v_i_1399_, v_sz_1398_);
if (v___x_1401_ == 0)
{
return v_bs_1400_;
}
else
{
lean_object* v_v_1402_; lean_object* v___x_1403_; lean_object* v_bs_x27_1404_; lean_object* v___x_1405_; size_t v___x_1406_; size_t v___x_1407_; lean_object* v___x_1408_; 
v_v_1402_ = lean_array_uget(v_bs_1400_, v_i_1399_);
v___x_1403_ = lean_unsigned_to_nat(0u);
v_bs_x27_1404_ = lean_array_uset(v_bs_1400_, v_i_1399_, v___x_1403_);
v___x_1405_ = l_Lean_Expr_fvarId_x21(v_v_1402_);
lean_dec(v_v_1402_);
v___x_1406_ = ((size_t)1ULL);
v___x_1407_ = lean_usize_add(v_i_1399_, v___x_1406_);
v___x_1408_ = lean_array_uset(v_bs_x27_1404_, v_i_1399_, v___x_1405_);
v_i_1399_ = v___x_1407_;
v_bs_1400_ = v___x_1408_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__8___boxed(lean_object* v_sz_1410_, lean_object* v_i_1411_, lean_object* v_bs_1412_){
_start:
{
size_t v_sz_boxed_1413_; size_t v_i_boxed_1414_; lean_object* v_res_1415_; 
v_sz_boxed_1413_ = lean_unbox_usize(v_sz_1410_);
lean_dec(v_sz_1410_);
v_i_boxed_1414_ = lean_unbox_usize(v_i_1411_);
lean_dec(v_i_1411_);
v_res_1415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__8(v_sz_boxed_1413_, v_i_boxed_1414_, v_bs_1412_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__12(lean_object* v_x_1416_, lean_object* v_x_1417_){
_start:
{
if (lean_obj_tag(v_x_1417_) == 0)
{
return v_x_1416_;
}
else
{
lean_object* v_key_1418_; lean_object* v_tail_1419_; lean_object* v___x_1420_; 
v_key_1418_ = lean_ctor_get(v_x_1417_, 0);
lean_inc(v_key_1418_);
v_tail_1419_ = lean_ctor_get(v_x_1417_, 2);
lean_inc(v_tail_1419_);
lean_dec_ref(v_x_1417_);
v___x_1420_ = lean_array_push(v_x_1416_, v_key_1418_);
v_x_1416_ = v___x_1420_;
v_x_1417_ = v_tail_1419_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__13(lean_object* v_as_1422_, size_t v_i_1423_, size_t v_stop_1424_, lean_object* v_b_1425_){
_start:
{
uint8_t v___x_1426_; 
v___x_1426_ = lean_usize_dec_eq(v_i_1423_, v_stop_1424_);
if (v___x_1426_ == 0)
{
lean_object* v___x_1427_; lean_object* v___x_1428_; size_t v___x_1429_; size_t v___x_1430_; 
v___x_1427_ = lean_array_uget_borrowed(v_as_1422_, v_i_1423_);
lean_inc(v___x_1427_);
v___x_1428_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__12(v_b_1425_, v___x_1427_);
v___x_1429_ = ((size_t)1ULL);
v___x_1430_ = lean_usize_add(v_i_1423_, v___x_1429_);
v_i_1423_ = v___x_1430_;
v_b_1425_ = v___x_1428_;
goto _start;
}
else
{
return v_b_1425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__13___boxed(lean_object* v_as_1432_, lean_object* v_i_1433_, lean_object* v_stop_1434_, lean_object* v_b_1435_){
_start:
{
size_t v_i_boxed_1436_; size_t v_stop_boxed_1437_; lean_object* v_res_1438_; 
v_i_boxed_1436_ = lean_unbox_usize(v_i_1433_);
lean_dec(v_i_1433_);
v_stop_boxed_1437_ = lean_unbox_usize(v_stop_1434_);
lean_dec(v_stop_1434_);
v_res_1438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__13(v_as_1432_, v_i_boxed_1436_, v_stop_boxed_1437_, v_b_1435_);
lean_dec_ref(v_as_1432_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32___redArg(lean_object* v_x_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_){
_start:
{
lean_object* v_ks_1443_; lean_object* v_vs_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1468_; 
v_ks_1443_ = lean_ctor_get(v_x_1439_, 0);
v_vs_1444_ = lean_ctor_get(v_x_1439_, 1);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_x_1439_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1446_ = v_x_1439_;
v_isShared_1447_ = v_isSharedCheck_1468_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_vs_1444_);
lean_inc(v_ks_1443_);
lean_dec(v_x_1439_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1468_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1448_ = lean_array_get_size(v_ks_1443_);
v___x_1449_ = lean_nat_dec_lt(v_x_1440_, v___x_1448_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1453_; 
lean_dec(v_x_1440_);
v___x_1450_ = lean_array_push(v_ks_1443_, v_x_1441_);
v___x_1451_ = lean_array_push(v_vs_1444_, v_x_1442_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 1, v___x_1451_);
lean_ctor_set(v___x_1446_, 0, v___x_1450_);
v___x_1453_ = v___x_1446_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
else
{
lean_object* v_k_x27_1455_; uint8_t v___x_1456_; 
v_k_x27_1455_ = lean_array_fget_borrowed(v_ks_1443_, v_x_1440_);
v___x_1456_ = l_Lean_instBEqMVarId_beq(v_x_1441_, v_k_x27_1455_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1458_; 
if (v_isShared_1447_ == 0)
{
v___x_1458_ = v___x_1446_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_ks_1443_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_vs_1444_);
v___x_1458_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_unsigned_to_nat(1u);
v___x_1460_ = lean_nat_add(v_x_1440_, v___x_1459_);
lean_dec(v_x_1440_);
v_x_1439_ = v___x_1458_;
v_x_1440_ = v___x_1460_;
goto _start;
}
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1463_ = lean_array_fset(v_ks_1443_, v_x_1440_, v_x_1441_);
v___x_1464_ = lean_array_fset(v_vs_1444_, v_x_1440_, v_x_1442_);
lean_dec(v_x_1440_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 1, v___x_1464_);
lean_ctor_set(v___x_1446_, 0, v___x_1463_);
v___x_1466_ = v___x_1446_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30___redArg(lean_object* v_n_1469_, lean_object* v_k_1470_, lean_object* v_v_1471_){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = lean_unsigned_to_nat(0u);
v___x_1473_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32___redArg(v_n_1469_, v___x_1472_, v_k_1470_, v_v_1471_);
return v___x_1473_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0(void){
_start:
{
size_t v___x_1474_; size_t v___x_1475_; size_t v___x_1476_; 
v___x_1474_ = ((size_t)5ULL);
v___x_1475_ = ((size_t)1ULL);
v___x_1476_ = lean_usize_shift_left(v___x_1475_, v___x_1474_);
return v___x_1476_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1(void){
_start:
{
size_t v___x_1477_; size_t v___x_1478_; size_t v___x_1479_; 
v___x_1477_ = ((size_t)1ULL);
v___x_1478_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0);
v___x_1479_ = lean_usize_sub(v___x_1478_, v___x_1477_);
return v___x_1479_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(lean_object* v_x_1481_, size_t v_x_1482_, size_t v_x_1483_, lean_object* v_x_1484_, lean_object* v_x_1485_){
_start:
{
if (lean_obj_tag(v_x_1481_) == 0)
{
lean_object* v_es_1486_; size_t v___x_1487_; size_t v___x_1488_; size_t v___x_1489_; size_t v___x_1490_; lean_object* v_j_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; 
v_es_1486_ = lean_ctor_get(v_x_1481_, 0);
v___x_1487_ = ((size_t)5ULL);
v___x_1488_ = ((size_t)1ULL);
v___x_1489_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1);
v___x_1490_ = lean_usize_land(v_x_1482_, v___x_1489_);
v_j_1491_ = lean_usize_to_nat(v___x_1490_);
v___x_1492_ = lean_array_get_size(v_es_1486_);
v___x_1493_ = lean_nat_dec_lt(v_j_1491_, v___x_1492_);
if (v___x_1493_ == 0)
{
lean_dec(v_j_1491_);
lean_dec(v_x_1485_);
lean_dec(v_x_1484_);
return v_x_1481_;
}
else
{
lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1530_; 
lean_inc_ref(v_es_1486_);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_x_1481_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; 
v_unused_1531_ = lean_ctor_get(v_x_1481_, 0);
lean_dec(v_unused_1531_);
v___x_1495_ = v_x_1481_;
v_isShared_1496_ = v_isSharedCheck_1530_;
goto v_resetjp_1494_;
}
else
{
lean_dec(v_x_1481_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1530_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v_v_1497_; lean_object* v___x_1498_; lean_object* v_xs_x27_1499_; lean_object* v___y_1501_; 
v_v_1497_ = lean_array_fget(v_es_1486_, v_j_1491_);
v___x_1498_ = lean_box(0);
v_xs_x27_1499_ = lean_array_fset(v_es_1486_, v_j_1491_, v___x_1498_);
switch(lean_obj_tag(v_v_1497_))
{
case 0:
{
lean_object* v_key_1506_; lean_object* v_val_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1517_; 
v_key_1506_ = lean_ctor_get(v_v_1497_, 0);
v_val_1507_ = lean_ctor_get(v_v_1497_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_v_1497_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1509_ = v_v_1497_;
v_isShared_1510_ = v_isSharedCheck_1517_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_val_1507_);
lean_inc(v_key_1506_);
lean_dec(v_v_1497_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1517_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
uint8_t v___x_1511_; 
v___x_1511_ = l_Lean_instBEqMVarId_beq(v_x_1484_, v_key_1506_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_del_object(v___x_1509_);
v___x_1512_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1506_, v_val_1507_, v_x_1484_, v_x_1485_);
v___x_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
v___y_1501_ = v___x_1513_;
goto v___jp_1500_;
}
else
{
lean_object* v___x_1515_; 
lean_dec(v_val_1507_);
lean_dec(v_key_1506_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 1, v_x_1485_);
lean_ctor_set(v___x_1509_, 0, v_x_1484_);
v___x_1515_ = v___x_1509_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_x_1484_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_x_1485_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
v___y_1501_ = v___x_1515_;
goto v___jp_1500_;
}
}
}
}
case 1:
{
lean_object* v_node_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1528_; 
v_node_1518_ = lean_ctor_get(v_v_1497_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_v_1497_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1520_ = v_v_1497_;
v_isShared_1521_ = v_isSharedCheck_1528_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_node_1518_);
lean_dec(v_v_1497_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1528_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
size_t v___x_1522_; size_t v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1522_ = lean_usize_shift_right(v_x_1482_, v___x_1487_);
v___x_1523_ = lean_usize_add(v_x_1483_, v___x_1488_);
v___x_1524_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_node_1518_, v___x_1522_, v___x_1523_, v_x_1484_, v_x_1485_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1524_);
v___x_1526_ = v___x_1520_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
v___y_1501_ = v___x_1526_;
goto v___jp_1500_;
}
}
}
default: 
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v_x_1484_);
lean_ctor_set(v___x_1529_, 1, v_x_1485_);
v___y_1501_ = v___x_1529_;
goto v___jp_1500_;
}
}
v___jp_1500_:
{
lean_object* v___x_1502_; lean_object* v___x_1504_; 
v___x_1502_ = lean_array_fset(v_xs_x27_1499_, v_j_1491_, v___y_1501_);
lean_dec(v_j_1491_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v___x_1502_);
v___x_1504_ = v___x_1495_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
else
{
lean_object* v_ks_1532_; lean_object* v_vs_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1553_; 
v_ks_1532_ = lean_ctor_get(v_x_1481_, 0);
v_vs_1533_ = lean_ctor_get(v_x_1481_, 1);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_x_1481_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1535_ = v_x_1481_;
v_isShared_1536_ = v_isSharedCheck_1553_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_vs_1533_);
lean_inc(v_ks_1532_);
lean_dec(v_x_1481_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1553_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_ks_1532_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_vs_1533_);
v___x_1538_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v_newNode_1539_; uint8_t v___y_1541_; size_t v___x_1547_; uint8_t v___x_1548_; 
v_newNode_1539_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30___redArg(v___x_1538_, v_x_1484_, v_x_1485_);
v___x_1547_ = ((size_t)7ULL);
v___x_1548_ = lean_usize_dec_le(v___x_1547_, v_x_1483_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
v___x_1549_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1539_);
v___x_1550_ = lean_unsigned_to_nat(4u);
v___x_1551_ = lean_nat_dec_lt(v___x_1549_, v___x_1550_);
lean_dec(v___x_1549_);
v___y_1541_ = v___x_1551_;
goto v___jp_1540_;
}
else
{
v___y_1541_ = v___x_1548_;
goto v___jp_1540_;
}
v___jp_1540_:
{
if (v___y_1541_ == 0)
{
lean_object* v_ks_1542_; lean_object* v_vs_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v_ks_1542_ = lean_ctor_get(v_newNode_1539_, 0);
lean_inc_ref(v_ks_1542_);
v_vs_1543_ = lean_ctor_get(v_newNode_1539_, 1);
lean_inc_ref(v_vs_1543_);
lean_dec_ref(v_newNode_1539_);
v___x_1544_ = lean_unsigned_to_nat(0u);
v___x_1545_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2);
v___x_1546_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(v_x_1483_, v_ks_1542_, v_vs_1543_, v___x_1544_, v___x_1545_);
lean_dec_ref(v_vs_1543_);
lean_dec_ref(v_ks_1542_);
return v___x_1546_;
}
else
{
return v_newNode_1539_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(size_t v_depth_1554_, lean_object* v_keys_1555_, lean_object* v_vals_1556_, lean_object* v_i_1557_, lean_object* v_entries_1558_){
_start:
{
lean_object* v___x_1559_; uint8_t v___x_1560_; 
v___x_1559_ = lean_array_get_size(v_keys_1555_);
v___x_1560_ = lean_nat_dec_lt(v_i_1557_, v___x_1559_);
if (v___x_1560_ == 0)
{
lean_dec(v_i_1557_);
return v_entries_1558_;
}
else
{
lean_object* v_k_1561_; lean_object* v_v_1562_; uint64_t v___x_1563_; size_t v_h_1564_; size_t v___x_1565_; lean_object* v___x_1566_; size_t v___x_1567_; size_t v___x_1568_; size_t v___x_1569_; size_t v_h_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_k_1561_ = lean_array_fget_borrowed(v_keys_1555_, v_i_1557_);
v_v_1562_ = lean_array_fget_borrowed(v_vals_1556_, v_i_1557_);
v___x_1563_ = l_Lean_instHashableMVarId_hash(v_k_1561_);
v_h_1564_ = lean_uint64_to_usize(v___x_1563_);
v___x_1565_ = ((size_t)5ULL);
v___x_1566_ = lean_unsigned_to_nat(1u);
v___x_1567_ = ((size_t)1ULL);
v___x_1568_ = lean_usize_sub(v_depth_1554_, v___x_1567_);
v___x_1569_ = lean_usize_mul(v___x_1565_, v___x_1568_);
v_h_1570_ = lean_usize_shift_right(v_h_1564_, v___x_1569_);
v___x_1571_ = lean_nat_add(v_i_1557_, v___x_1566_);
lean_dec(v_i_1557_);
lean_inc(v_v_1562_);
lean_inc(v_k_1561_);
v___x_1572_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_entries_1558_, v_h_1570_, v_depth_1554_, v_k_1561_, v_v_1562_);
v_i_1557_ = v___x_1571_;
v_entries_1558_ = v___x_1572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg___boxed(lean_object* v_depth_1574_, lean_object* v_keys_1575_, lean_object* v_vals_1576_, lean_object* v_i_1577_, lean_object* v_entries_1578_){
_start:
{
size_t v_depth_boxed_1579_; lean_object* v_res_1580_; 
v_depth_boxed_1579_ = lean_unbox_usize(v_depth_1574_);
lean_dec(v_depth_1574_);
v_res_1580_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(v_depth_boxed_1579_, v_keys_1575_, v_vals_1576_, v_i_1577_, v_entries_1578_);
lean_dec_ref(v_vals_1576_);
lean_dec_ref(v_keys_1575_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___boxed(lean_object* v_x_1581_, lean_object* v_x_1582_, lean_object* v_x_1583_, lean_object* v_x_1584_, lean_object* v_x_1585_){
_start:
{
size_t v_x_22877__boxed_1586_; size_t v_x_22878__boxed_1587_; lean_object* v_res_1588_; 
v_x_22877__boxed_1586_ = lean_unbox_usize(v_x_1582_);
lean_dec(v_x_1582_);
v_x_22878__boxed_1587_ = lean_unbox_usize(v_x_1583_);
lean_dec(v_x_1583_);
v_res_1588_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_x_1581_, v_x_22877__boxed_1586_, v_x_22878__boxed_1587_, v_x_1584_, v_x_1585_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(lean_object* v_x_1589_, lean_object* v_x_1590_, lean_object* v_x_1591_){
_start:
{
uint64_t v___x_1592_; size_t v___x_1593_; size_t v___x_1594_; lean_object* v___x_1595_; 
v___x_1592_ = l_Lean_instHashableMVarId_hash(v_x_1590_);
v___x_1593_ = lean_uint64_to_usize(v___x_1592_);
v___x_1594_ = ((size_t)1ULL);
v___x_1595_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_x_1589_, v___x_1593_, v___x_1594_, v_x_1590_, v_x_1591_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(lean_object* v_mvarId_1596_, lean_object* v_val_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v___x_1600_; lean_object* v_mctx_1601_; lean_object* v_cache_1602_; lean_object* v_zetaDeltaFVarIds_1603_; lean_object* v_postponed_1604_; lean_object* v_diag_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1632_; 
v___x_1600_ = lean_st_ref_take(v___y_1598_);
v_mctx_1601_ = lean_ctor_get(v___x_1600_, 0);
v_cache_1602_ = lean_ctor_get(v___x_1600_, 1);
v_zetaDeltaFVarIds_1603_ = lean_ctor_get(v___x_1600_, 2);
v_postponed_1604_ = lean_ctor_get(v___x_1600_, 3);
v_diag_1605_ = lean_ctor_get(v___x_1600_, 4);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1607_ = v___x_1600_;
v_isShared_1608_ = v_isSharedCheck_1632_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_diag_1605_);
lean_inc(v_postponed_1604_);
lean_inc(v_zetaDeltaFVarIds_1603_);
lean_inc(v_cache_1602_);
lean_inc(v_mctx_1601_);
lean_dec(v___x_1600_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1632_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v_depth_1609_; lean_object* v_levelAssignDepth_1610_; lean_object* v_mvarCounter_1611_; lean_object* v_lDepth_1612_; lean_object* v_decls_1613_; lean_object* v_userNames_1614_; lean_object* v_lAssignment_1615_; lean_object* v_eAssignment_1616_; lean_object* v_dAssignment_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1631_; 
v_depth_1609_ = lean_ctor_get(v_mctx_1601_, 0);
v_levelAssignDepth_1610_ = lean_ctor_get(v_mctx_1601_, 1);
v_mvarCounter_1611_ = lean_ctor_get(v_mctx_1601_, 2);
v_lDepth_1612_ = lean_ctor_get(v_mctx_1601_, 3);
v_decls_1613_ = lean_ctor_get(v_mctx_1601_, 4);
v_userNames_1614_ = lean_ctor_get(v_mctx_1601_, 5);
v_lAssignment_1615_ = lean_ctor_get(v_mctx_1601_, 6);
v_eAssignment_1616_ = lean_ctor_get(v_mctx_1601_, 7);
v_dAssignment_1617_ = lean_ctor_get(v_mctx_1601_, 8);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_mctx_1601_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1619_ = v_mctx_1601_;
v_isShared_1620_ = v_isSharedCheck_1631_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_dAssignment_1617_);
lean_inc(v_eAssignment_1616_);
lean_inc(v_lAssignment_1615_);
lean_inc(v_userNames_1614_);
lean_inc(v_decls_1613_);
lean_inc(v_lDepth_1612_);
lean_inc(v_mvarCounter_1611_);
lean_inc(v_levelAssignDepth_1610_);
lean_inc(v_depth_1609_);
lean_dec(v_mctx_1601_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1631_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1621_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(v_eAssignment_1616_, v_mvarId_1596_, v_val_1597_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 7, v___x_1621_);
v___x_1623_ = v___x_1619_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_depth_1609_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_levelAssignDepth_1610_);
lean_ctor_set(v_reuseFailAlloc_1630_, 2, v_mvarCounter_1611_);
lean_ctor_set(v_reuseFailAlloc_1630_, 3, v_lDepth_1612_);
lean_ctor_set(v_reuseFailAlloc_1630_, 4, v_decls_1613_);
lean_ctor_set(v_reuseFailAlloc_1630_, 5, v_userNames_1614_);
lean_ctor_set(v_reuseFailAlloc_1630_, 6, v_lAssignment_1615_);
lean_ctor_set(v_reuseFailAlloc_1630_, 7, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1630_, 8, v_dAssignment_1617_);
v___x_1623_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1625_; 
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v___x_1623_);
v___x_1625_ = v___x_1607_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_cache_1602_);
lean_ctor_set(v_reuseFailAlloc_1629_, 2, v_zetaDeltaFVarIds_1603_);
lean_ctor_set(v_reuseFailAlloc_1629_, 3, v_postponed_1604_);
lean_ctor_set(v_reuseFailAlloc_1629_, 4, v_diag_1605_);
v___x_1625_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1626_ = lean_st_ref_set(v___y_1598_, v___x_1625_);
v___x_1627_ = lean_box(0);
v___x_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
return v___x_1628_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___redArg___boxed(lean_object* v_mvarId_1633_, lean_object* v_val_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(v_mvarId_1633_, v_val_1634_, v___y_1635_);
lean_dec(v___y_1635_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(lean_object* v_msgData_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v___x_1644_; lean_object* v_env_1645_; lean_object* v___x_1646_; lean_object* v_mctx_1647_; lean_object* v_lctx_1648_; lean_object* v_options_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1644_ = lean_st_ref_get(v___y_1642_);
v_env_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc_ref(v_env_1645_);
lean_dec(v___x_1644_);
v___x_1646_ = lean_st_ref_get(v___y_1640_);
v_mctx_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc_ref(v_mctx_1647_);
lean_dec(v___x_1646_);
v_lctx_1648_ = lean_ctor_get(v___y_1639_, 2);
v_options_1649_ = lean_ctor_get(v___y_1641_, 2);
lean_inc_ref(v_options_1649_);
lean_inc_ref(v_lctx_1648_);
v___x_1650_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1650_, 0, v_env_1645_);
lean_ctor_set(v___x_1650_, 1, v_mctx_1647_);
lean_ctor_set(v___x_1650_, 2, v_lctx_1648_);
lean_ctor_set(v___x_1650_, 3, v_options_1649_);
v___x_1651_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
lean_ctor_set(v___x_1651_, 1, v_msgData_1638_);
v___x_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17___boxed(lean_object* v_msgData_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(v_msgData_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(lean_object* v_msg_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_ref_1666_; lean_object* v___x_1667_; lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1676_; 
v_ref_1666_ = lean_ctor_get(v___y_1663_, 5);
v___x_1667_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(v_msg_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1676_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1676_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v___x_1674_; 
lean_inc(v_ref_1666_);
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v_ref_1666_);
lean_ctor_set(v___x_1672_, 1, v_a_1668_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set_tag(v___x_1670_, 1);
lean_ctor_set(v___x_1670_, 0, v___x_1672_);
v___x_1674_ = v___x_1670_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___redArg___boxed(lean_object* v_msg_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(v_msg_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__1(size_t v_sz_1684_, size_t v_i_1685_, lean_object* v_bs_1686_){
_start:
{
uint8_t v___x_1687_; 
v___x_1687_ = lean_usize_dec_lt(v_i_1685_, v_sz_1684_);
if (v___x_1687_ == 0)
{
return v_bs_1686_;
}
else
{
lean_object* v_v_1688_; lean_object* v___x_1689_; lean_object* v_bs_x27_1690_; lean_object* v___x_1691_; size_t v___x_1692_; size_t v___x_1693_; lean_object* v___x_1694_; 
v_v_1688_ = lean_array_uget(v_bs_1686_, v_i_1685_);
v___x_1689_ = lean_unsigned_to_nat(0u);
v_bs_x27_1690_ = lean_array_uset(v_bs_1686_, v_i_1685_, v___x_1689_);
v___x_1691_ = l_Lean_mkFVar(v_v_1688_);
v___x_1692_ = ((size_t)1ULL);
v___x_1693_ = lean_usize_add(v_i_1685_, v___x_1692_);
v___x_1694_ = lean_array_uset(v_bs_x27_1690_, v_i_1685_, v___x_1691_);
v_i_1685_ = v___x_1693_;
v_bs_1686_ = v___x_1694_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__1___boxed(lean_object* v_sz_1696_, lean_object* v_i_1697_, lean_object* v_bs_1698_){
_start:
{
size_t v_sz_boxed_1699_; size_t v_i_boxed_1700_; lean_object* v_res_1701_; 
v_sz_boxed_1699_ = lean_unbox_usize(v_sz_1696_);
lean_dec(v_sz_1696_);
v_i_boxed_1700_ = lean_unbox_usize(v_i_1697_);
lean_dec(v_i_1697_);
v_res_1701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__1(v_sz_boxed_1699_, v_i_boxed_1700_, v_bs_1698_);
return v_res_1701_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1708_ = lean_box(0);
v___x_1709_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3));
v___x_1710_ = l_Lean_mkConst(v___x_1709_, v___x_1708_);
return v___x_1710_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = lean_unsigned_to_nat(0u);
v___x_1716_ = l_Lean_Level_ofNat(v___x_1715_);
return v___x_1716_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8(void){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12);
v___x_1718_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7);
v___x_1719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
lean_ctor_set(v___x_1719_, 1, v___x_1717_);
return v___x_1719_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9(void){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1720_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8);
v___x_1721_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6));
v___x_1722_ = l_Lean_mkConst(v___x_1721_, v___x_1720_);
return v___x_1722_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10(void){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1723_ = lean_box(0);
v___x_1724_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6));
v___x_1725_ = l_Lean_mkConst(v___x_1724_, v___x_1723_);
return v___x_1725_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11(void){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1726_ = lean_box(0);
v___x_1727_ = lean_unsigned_to_nat(16u);
v___x_1728_ = lean_mk_array(v___x_1727_, v___x_1726_);
return v___x_1728_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12(void){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1729_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11);
v___x_1730_ = lean_unsigned_to_nat(0u);
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
lean_ctor_set(v___x_1731_, 1, v___x_1729_);
return v___x_1731_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14(void){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13));
v___x_1734_ = l_Lean_stringToMessageData(v___x_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4(lean_object* v_fst_1735_, lean_object* v___x_1736_, lean_object* v_snd_1737_, lean_object* v_goal_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
uint8_t v___y_1746_; size_t v___y_1747_; lean_object* v___y_1748_; size_t v___y_1749_; lean_object* v___y_1750_; lean_object* v_a_1751_; size_t v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___x_1941_; lean_object* v___y_1943_; lean_object* v_relevantHyps_1960_; lean_object* v_size_1961_; lean_object* v_buckets_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
v___x_1941_ = lean_st_ref_get(v___y_1739_);
v_relevantHyps_1960_ = lean_ctor_get(v___x_1941_, 1);
lean_inc_ref(v_relevantHyps_1960_);
lean_dec(v___x_1941_);
v_size_1961_ = lean_ctor_get(v_relevantHyps_1960_, 0);
lean_inc(v_size_1961_);
v_buckets_1962_ = lean_ctor_get(v_relevantHyps_1960_, 1);
lean_inc_ref(v_buckets_1962_);
lean_dec_ref(v_relevantHyps_1960_);
v___x_1963_ = lean_mk_empty_array_with_capacity(v_size_1961_);
lean_dec(v_size_1961_);
v___x_1964_ = lean_unsigned_to_nat(0u);
v___x_1965_ = lean_array_get_size(v_buckets_1962_);
v___x_1966_ = lean_nat_dec_lt(v___x_1964_, v___x_1965_);
if (v___x_1966_ == 0)
{
lean_dec_ref(v_buckets_1962_);
v___y_1943_ = v___x_1963_;
goto v___jp_1942_;
}
else
{
uint8_t v___x_1967_; 
v___x_1967_ = lean_nat_dec_le(v___x_1965_, v___x_1965_);
if (v___x_1967_ == 0)
{
if (v___x_1966_ == 0)
{
lean_dec_ref(v_buckets_1962_);
v___y_1943_ = v___x_1963_;
goto v___jp_1942_;
}
else
{
size_t v___x_1968_; size_t v___x_1969_; lean_object* v___x_1970_; 
v___x_1968_ = ((size_t)0ULL);
v___x_1969_ = lean_usize_of_nat(v___x_1965_);
v___x_1970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__13(v_buckets_1962_, v___x_1968_, v___x_1969_, v___x_1963_);
lean_dec_ref(v_buckets_1962_);
v___y_1943_ = v___x_1970_;
goto v___jp_1942_;
}
}
else
{
size_t v___x_1971_; size_t v___x_1972_; lean_object* v___x_1973_; 
v___x_1971_ = ((size_t)0ULL);
v___x_1972_ = lean_usize_of_nat(v___x_1965_);
v___x_1973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__13(v_buckets_1962_, v___x_1971_, v___x_1972_, v___x_1963_);
lean_dec_ref(v_buckets_1962_);
v___y_1943_ = v___x_1973_;
goto v___jp_1942_;
}
}
v___jp_1745_:
{
lean_object* v_fst_1752_; lean_object* v_snd_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v_fst_1752_ = lean_ctor_get(v_a_1751_, 0);
lean_inc(v_fst_1752_);
v_snd_1753_ = lean_ctor_get(v_a_1751_, 1);
lean_inc(v_snd_1753_);
lean_dec_ref(v_a_1751_);
v___x_1754_ = l_Lean_Expr_getAppFn(v_fst_1752_);
lean_dec(v_fst_1752_);
v___x_1755_ = l_Lean_Expr_mvarId_x21(v___x_1754_);
lean_dec_ref(v___x_1754_);
v___x_1756_ = l_Lean_MVarId_getType(v___x_1755_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___f_1763_; lean_object* v___x_1764_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref(v___x_1756_);
v___x_1758_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1));
v___x_1759_ = lean_box(0);
v___x_1760_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4);
v___x_1761_ = lean_box_usize(v___y_1747_);
v___x_1762_ = lean_box(v___y_1746_);
lean_inc(v_fst_1735_);
v___f_1763_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___boxed), 15, 8);
lean_closure_set(v___f_1763_, 0, v___x_1759_);
lean_closure_set(v___f_1763_, 1, v___y_1748_);
lean_closure_set(v___f_1763_, 2, v___x_1761_);
lean_closure_set(v___f_1763_, 3, v_a_1757_);
lean_closure_set(v___f_1763_, 4, v___x_1762_);
lean_closure_set(v___f_1763_, 5, v_fst_1735_);
lean_closure_set(v___f_1763_, 6, v___x_1736_);
lean_closure_set(v___f_1763_, 7, v___x_1760_);
lean_inc(v___y_1743_);
lean_inc_ref(v___y_1742_);
lean_inc(v___y_1741_);
lean_inc_ref(v___y_1740_);
v___x_1764_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v___x_1758_, v___x_1760_, v___f_1763_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v_fst_1766_; lean_object* v_snd_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref(v___x_1764_);
v_fst_1766_ = lean_ctor_get(v_a_1765_, 0);
lean_inc(v_fst_1766_);
v_snd_1767_ = lean_ctor_get(v_a_1765_, 1);
lean_inc(v_snd_1767_);
lean_dec(v_a_1765_);
v___x_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1768_, 0, v_snd_1767_);
v___x_1769_ = 0;
v___x_1770_ = lean_box(0);
lean_inc_ref(v___y_1740_);
v___x_1771_ = l_Lean_Meta_mkFreshExprMVar(v___x_1768_, v___x_1769_, v___x_1770_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; size_t v_sz_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
lean_dec_ref(v___x_1771_);
v___x_1773_ = l_Lean_Expr_mvarId_x21(v_a_1772_);
lean_dec(v_a_1772_);
v___x_1774_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9);
v___x_1775_ = l_Lean_mkNatLit(v_fst_1735_);
v___x_1776_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10);
lean_inc(v___x_1773_);
v___x_1777_ = l_Lean_mkMVar(v___x_1773_);
v___x_1778_ = l_Lean_mkApp6(v___x_1774_, v___x_1760_, v___x_1775_, v_fst_1766_, v___x_1776_, v_snd_1737_, v___x_1777_);
lean_inc_ref(v___y_1750_);
v___x_1779_ = l_Array_append___redArg(v___y_1750_, v_snd_1753_);
v___x_1780_ = l_Lean_mkAppN(v___x_1778_, v___x_1779_);
lean_dec_ref(v___x_1779_);
v___x_1781_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(v_goal_1738_, v___x_1780_, v___y_1741_);
lean_dec_ref(v___x_1781_);
v_sz_1782_ = lean_array_size(v_snd_1753_);
lean_inc(v_snd_1753_);
v___x_1783_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__8(v_sz_1782_, v___y_1749_, v_snd_1753_);
lean_inc(v___y_1743_);
lean_inc_ref(v___y_1742_);
lean_inc(v___y_1741_);
lean_inc_ref(v___y_1740_);
v___x_1784_ = l_Lean_MVarId_tryClearMany_x27(v___x_1773_, v___x_1783_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v_fst_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; lean_object* v___x_1791_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref(v___x_1784_);
v_fst_1786_ = lean_ctor_get(v_a_1785_, 0);
lean_inc(v_fst_1786_);
lean_dec(v_a_1785_);
v___x_1787_ = lean_array_get_size(v___y_1750_);
lean_dec_ref(v___y_1750_);
v___x_1788_ = lean_array_get_size(v_snd_1753_);
lean_dec(v_snd_1753_);
v___x_1789_ = lean_nat_add(v___x_1787_, v___x_1788_);
v___x_1790_ = 0;
v___x_1791_ = l_Lean_Meta_introNCore(v_fst_1786_, v___x_1789_, v___x_1759_, v___x_1790_, v___x_1790_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1800_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1794_ = v___x_1791_;
v_isShared_1795_ = v_isSharedCheck_1800_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1791_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1800_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v_snd_1796_; lean_object* v___x_1798_; 
v_snd_1796_ = lean_ctor_get(v_a_1792_, 1);
lean_inc(v_snd_1796_);
lean_dec(v_a_1792_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v_snd_1796_);
v___x_1798_ = v___x_1794_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_snd_1796_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
v_a_1801_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1791_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1791_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec(v_snd_1753_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
v_a_1809_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1784_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1784_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_dec(v_fst_1766_);
lean_dec(v_snd_1753_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v_goal_1738_);
lean_dec_ref(v_snd_1737_);
lean_dec(v_fst_1735_);
v_a_1817_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1771_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1771_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
lean_dec(v_snd_1753_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v_goal_1738_);
lean_dec_ref(v_snd_1737_);
lean_dec(v_fst_1735_);
v_a_1825_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1764_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1764_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_dec(v_snd_1753_);
lean_dec_ref(v___y_1750_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec(v_goal_1738_);
lean_dec_ref(v_snd_1737_);
lean_dec_ref(v___x_1736_);
lean_dec(v_fst_1735_);
v_a_1833_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1756_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1756_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
v___jp_1841_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v_lctx_1848_; lean_object* v_mctx_1849_; lean_object* v_ngen_1850_; lean_object* v_quotContext_1851_; lean_object* v_nextMacroScope_1852_; uint8_t v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1845_ = lean_st_ref_get(v___y_1741_);
v___x_1846_ = lean_st_ref_get(v___y_1743_);
v___x_1847_ = lean_st_ref_get(v___y_1743_);
v_lctx_1848_ = lean_ctor_get(v___y_1740_, 2);
v_mctx_1849_ = lean_ctor_get(v___x_1845_, 0);
lean_inc_ref(v_mctx_1849_);
lean_dec(v___x_1845_);
v_ngen_1850_ = lean_ctor_get(v___x_1846_, 2);
lean_inc_ref(v_ngen_1850_);
lean_dec(v___x_1846_);
v_quotContext_1851_ = lean_ctor_get(v___y_1742_, 10);
v_nextMacroScope_1852_ = lean_ctor_get(v___x_1847_, 1);
lean_inc(v_nextMacroScope_1852_);
lean_dec(v___x_1847_);
v___x_1853_ = 1;
lean_inc_ref(v_lctx_1848_);
lean_inc(v_quotContext_1851_);
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v_quotContext_1851_);
lean_ctor_set(v___x_1854_, 1, v_lctx_1848_);
v___x_1855_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12);
v___x_1856_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1856_, 0, v_mctx_1849_);
lean_ctor_set(v___x_1856_, 1, v_nextMacroScope_1852_);
lean_ctor_set(v___x_1856_, 2, v_ngen_1850_);
lean_ctor_set(v___x_1856_, 3, v___x_1855_);
lean_inc(v_goal_1738_);
v___x_1857_ = l_Lean_MetavarContext_revert(v___y_1843_, v_goal_1738_, v___x_1853_, v___x_1854_, v___x_1856_);
lean_dec_ref(v___x_1854_);
lean_dec_ref(v___y_1843_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v_a_1859_; lean_object* v___x_1860_; lean_object* v_mctx_1861_; lean_object* v_nextMacroScope_1862_; lean_object* v_ngen_1863_; lean_object* v_cache_1864_; lean_object* v_zetaDeltaFVarIds_1865_; lean_object* v_postponed_1866_; lean_object* v_diag_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1893_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_a_1858_);
v_a_1859_ = lean_ctor_get(v___x_1857_, 1);
lean_inc(v_a_1859_);
lean_dec_ref(v___x_1857_);
v___x_1860_ = lean_st_ref_take(v___y_1741_);
v_mctx_1861_ = lean_ctor_get(v_a_1859_, 0);
lean_inc_ref(v_mctx_1861_);
v_nextMacroScope_1862_ = lean_ctor_get(v_a_1859_, 1);
lean_inc(v_nextMacroScope_1862_);
v_ngen_1863_ = lean_ctor_get(v_a_1859_, 2);
lean_inc_ref(v_ngen_1863_);
lean_dec(v_a_1859_);
v_cache_1864_ = lean_ctor_get(v___x_1860_, 1);
v_zetaDeltaFVarIds_1865_ = lean_ctor_get(v___x_1860_, 2);
v_postponed_1866_ = lean_ctor_get(v___x_1860_, 3);
v_diag_1867_ = lean_ctor_get(v___x_1860_, 4);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; 
v_unused_1894_ = lean_ctor_get(v___x_1860_, 0);
lean_dec(v_unused_1894_);
v___x_1869_ = v___x_1860_;
v_isShared_1870_ = v_isSharedCheck_1893_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_diag_1867_);
lean_inc(v_postponed_1866_);
lean_inc(v_zetaDeltaFVarIds_1865_);
lean_inc(v_cache_1864_);
lean_dec(v___x_1860_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1893_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v_mctx_1861_);
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_mctx_1861_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_cache_1864_);
lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_zetaDeltaFVarIds_1865_);
lean_ctor_set(v_reuseFailAlloc_1892_, 3, v_postponed_1866_);
lean_ctor_set(v_reuseFailAlloc_1892_, 4, v_diag_1867_);
v___x_1872_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v_env_1875_; lean_object* v_auxDeclNGen_1876_; lean_object* v_traceState_1877_; lean_object* v_cache_1878_; lean_object* v_messages_1879_; lean_object* v_infoState_1880_; lean_object* v_snapshotTasks_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1889_; 
v___x_1873_ = lean_st_ref_set(v___y_1741_, v___x_1872_);
v___x_1874_ = lean_st_ref_take(v___y_1743_);
v_env_1875_ = lean_ctor_get(v___x_1874_, 0);
v_auxDeclNGen_1876_ = lean_ctor_get(v___x_1874_, 3);
v_traceState_1877_ = lean_ctor_get(v___x_1874_, 4);
v_cache_1878_ = lean_ctor_get(v___x_1874_, 5);
v_messages_1879_ = lean_ctor_get(v___x_1874_, 6);
v_infoState_1880_ = lean_ctor_get(v___x_1874_, 7);
v_snapshotTasks_1881_ = lean_ctor_get(v___x_1874_, 8);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1889_ == 0)
{
lean_object* v_unused_1890_; lean_object* v_unused_1891_; 
v_unused_1890_ = lean_ctor_get(v___x_1874_, 2);
lean_dec(v_unused_1890_);
v_unused_1891_ = lean_ctor_get(v___x_1874_, 1);
lean_dec(v_unused_1891_);
v___x_1883_ = v___x_1874_;
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_snapshotTasks_1881_);
lean_inc(v_infoState_1880_);
lean_inc(v_messages_1879_);
lean_inc(v_cache_1878_);
lean_inc(v_traceState_1877_);
lean_inc(v_auxDeclNGen_1876_);
lean_inc(v_env_1875_);
lean_dec(v___x_1874_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 2, v_ngen_1863_);
lean_ctor_set(v___x_1883_, 1, v_nextMacroScope_1862_);
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_env_1875_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_nextMacroScope_1862_);
lean_ctor_set(v_reuseFailAlloc_1888_, 2, v_ngen_1863_);
lean_ctor_set(v_reuseFailAlloc_1888_, 3, v_auxDeclNGen_1876_);
lean_ctor_set(v_reuseFailAlloc_1888_, 4, v_traceState_1877_);
lean_ctor_set(v_reuseFailAlloc_1888_, 5, v_cache_1878_);
lean_ctor_set(v_reuseFailAlloc_1888_, 6, v_messages_1879_);
lean_ctor_set(v_reuseFailAlloc_1888_, 7, v_infoState_1880_);
lean_ctor_set(v_reuseFailAlloc_1888_, 8, v_snapshotTasks_1881_);
v___x_1886_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1887_; 
v___x_1887_ = lean_st_ref_set(v___y_1743_, v___x_1886_);
lean_inc_ref(v___y_1844_);
v___y_1746_ = v___x_1853_;
v___y_1747_ = v___y_1842_;
v___y_1748_ = v___y_1844_;
v___y_1749_ = v___y_1842_;
v___y_1750_ = v___y_1844_;
v_a_1751_ = v_a_1858_;
goto v___jp_1745_;
}
}
}
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1896_; lean_object* v_mctx_1897_; lean_object* v_nextMacroScope_1898_; lean_object* v_ngen_1899_; lean_object* v_cache_1900_; lean_object* v_zetaDeltaFVarIds_1901_; lean_object* v_postponed_1902_; lean_object* v_diag_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1939_; 
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1739_);
lean_dec(v_goal_1738_);
lean_dec_ref(v_snd_1737_);
lean_dec_ref(v___x_1736_);
lean_dec(v_fst_1735_);
v_a_1895_ = lean_ctor_get(v___x_1857_, 1);
lean_inc(v_a_1895_);
lean_dec_ref(v___x_1857_);
v___x_1896_ = lean_st_ref_take(v___y_1741_);
v_mctx_1897_ = lean_ctor_get(v_a_1895_, 0);
lean_inc_ref(v_mctx_1897_);
v_nextMacroScope_1898_ = lean_ctor_get(v_a_1895_, 1);
lean_inc(v_nextMacroScope_1898_);
v_ngen_1899_ = lean_ctor_get(v_a_1895_, 2);
lean_inc_ref(v_ngen_1899_);
lean_dec(v_a_1895_);
v_cache_1900_ = lean_ctor_get(v___x_1896_, 1);
v_zetaDeltaFVarIds_1901_ = lean_ctor_get(v___x_1896_, 2);
v_postponed_1902_ = lean_ctor_get(v___x_1896_, 3);
v_diag_1903_ = lean_ctor_get(v___x_1896_, 4);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; 
v_unused_1940_ = lean_ctor_get(v___x_1896_, 0);
lean_dec(v_unused_1940_);
v___x_1905_ = v___x_1896_;
v_isShared_1906_ = v_isSharedCheck_1939_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_diag_1903_);
lean_inc(v_postponed_1902_);
lean_inc(v_zetaDeltaFVarIds_1901_);
lean_inc(v_cache_1900_);
lean_dec(v___x_1896_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1939_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 0, v_mctx_1897_);
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_mctx_1897_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_cache_1900_);
lean_ctor_set(v_reuseFailAlloc_1938_, 2, v_zetaDeltaFVarIds_1901_);
lean_ctor_set(v_reuseFailAlloc_1938_, 3, v_postponed_1902_);
lean_ctor_set(v_reuseFailAlloc_1938_, 4, v_diag_1903_);
v___x_1908_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v_env_1911_; lean_object* v_auxDeclNGen_1912_; lean_object* v_traceState_1913_; lean_object* v_cache_1914_; lean_object* v_messages_1915_; lean_object* v_infoState_1916_; lean_object* v_snapshotTasks_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1935_; 
v___x_1909_ = lean_st_ref_set(v___y_1741_, v___x_1908_);
v___x_1910_ = lean_st_ref_take(v___y_1743_);
v_env_1911_ = lean_ctor_get(v___x_1910_, 0);
v_auxDeclNGen_1912_ = lean_ctor_get(v___x_1910_, 3);
v_traceState_1913_ = lean_ctor_get(v___x_1910_, 4);
v_cache_1914_ = lean_ctor_get(v___x_1910_, 5);
v_messages_1915_ = lean_ctor_get(v___x_1910_, 6);
v_infoState_1916_ = lean_ctor_get(v___x_1910_, 7);
v_snapshotTasks_1917_ = lean_ctor_get(v___x_1910_, 8);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1935_ == 0)
{
lean_object* v_unused_1936_; lean_object* v_unused_1937_; 
v_unused_1936_ = lean_ctor_get(v___x_1910_, 2);
lean_dec(v_unused_1936_);
v_unused_1937_ = lean_ctor_get(v___x_1910_, 1);
lean_dec(v_unused_1937_);
v___x_1919_ = v___x_1910_;
v_isShared_1920_ = v_isSharedCheck_1935_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_snapshotTasks_1917_);
lean_inc(v_infoState_1916_);
lean_inc(v_messages_1915_);
lean_inc(v_cache_1914_);
lean_inc(v_traceState_1913_);
lean_inc(v_auxDeclNGen_1912_);
lean_inc(v_env_1911_);
lean_dec(v___x_1910_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1935_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 2, v_ngen_1899_);
lean_ctor_set(v___x_1919_, 1, v_nextMacroScope_1898_);
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_env_1911_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_nextMacroScope_1898_);
lean_ctor_set(v_reuseFailAlloc_1934_, 2, v_ngen_1899_);
lean_ctor_set(v_reuseFailAlloc_1934_, 3, v_auxDeclNGen_1912_);
lean_ctor_set(v_reuseFailAlloc_1934_, 4, v_traceState_1913_);
lean_ctor_set(v_reuseFailAlloc_1934_, 5, v_cache_1914_);
lean_ctor_set(v_reuseFailAlloc_1934_, 6, v_messages_1915_);
lean_ctor_set(v_reuseFailAlloc_1934_, 7, v_infoState_1916_);
lean_ctor_set(v_reuseFailAlloc_1934_, 8, v_snapshotTasks_1917_);
v___x_1922_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
v___x_1923_ = lean_st_ref_set(v___y_1743_, v___x_1922_);
v___x_1924_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14);
v___x_1925_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(v___x_1924_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
}
}
}
v___jp_1942_:
{
lean_object* v___x_1944_; lean_object* v_relevantTerms_1945_; lean_object* v_size_1946_; lean_object* v_buckets_1947_; size_t v_sz_1948_; size_t v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; 
v___x_1944_ = lean_st_ref_get(v___y_1739_);
v_relevantTerms_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc_ref(v_relevantTerms_1945_);
lean_dec(v___x_1944_);
v_size_1946_ = lean_ctor_get(v_relevantTerms_1945_, 0);
lean_inc(v_size_1946_);
v_buckets_1947_ = lean_ctor_get(v_relevantTerms_1945_, 1);
lean_inc_ref(v_buckets_1947_);
lean_dec_ref(v_relevantTerms_1945_);
v_sz_1948_ = lean_array_size(v___y_1943_);
v___x_1949_ = ((size_t)0ULL);
v___x_1950_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__1(v_sz_1948_, v___x_1949_, v___y_1943_);
v___x_1951_ = lean_mk_empty_array_with_capacity(v_size_1946_);
lean_dec(v_size_1946_);
v___x_1952_ = lean_unsigned_to_nat(0u);
v___x_1953_ = lean_array_get_size(v_buckets_1947_);
v___x_1954_ = lean_nat_dec_lt(v___x_1952_, v___x_1953_);
if (v___x_1954_ == 0)
{
lean_dec_ref(v_buckets_1947_);
v___y_1842_ = v___x_1949_;
v___y_1843_ = v___x_1950_;
v___y_1844_ = v___x_1951_;
goto v___jp_1841_;
}
else
{
uint8_t v___x_1955_; 
v___x_1955_ = lean_nat_dec_le(v___x_1953_, v___x_1953_);
if (v___x_1955_ == 0)
{
if (v___x_1954_ == 0)
{
lean_dec_ref(v_buckets_1947_);
v___y_1842_ = v___x_1949_;
v___y_1843_ = v___x_1950_;
v___y_1844_ = v___x_1951_;
goto v___jp_1841_;
}
else
{
size_t v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = lean_usize_of_nat(v___x_1953_);
v___x_1957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__11(v_buckets_1947_, v___x_1949_, v___x_1956_, v___x_1951_);
lean_dec_ref(v_buckets_1947_);
v___y_1842_ = v___x_1949_;
v___y_1843_ = v___x_1950_;
v___y_1844_ = v___x_1957_;
goto v___jp_1841_;
}
}
else
{
size_t v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = lean_usize_of_nat(v___x_1953_);
v___x_1959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__11(v_buckets_1947_, v___x_1949_, v___x_1958_, v___x_1951_);
lean_dec_ref(v_buckets_1947_);
v___y_1842_ = v___x_1949_;
v___y_1843_ = v___x_1950_;
v___y_1844_ = v___x_1959_;
goto v___jp_1841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___boxed(lean_object* v_fst_1974_, lean_object* v___x_1975_, lean_object* v_snd_1976_, lean_object* v_goal_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4(v_fst_1974_, v___x_1975_, v_snd_1976_, v_goal_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
return v_res_1984_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34(lean_object* v_opts_1985_, lean_object* v_opt_1986_){
_start:
{
lean_object* v_name_1987_; lean_object* v_defValue_1988_; lean_object* v_map_1989_; lean_object* v___x_1990_; 
v_name_1987_ = lean_ctor_get(v_opt_1986_, 0);
v_defValue_1988_ = lean_ctor_get(v_opt_1986_, 1);
v_map_1989_ = lean_ctor_get(v_opts_1985_, 0);
v___x_1990_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1989_, v_name_1987_);
if (lean_obj_tag(v___x_1990_) == 0)
{
uint8_t v___x_1991_; 
v___x_1991_ = lean_unbox(v_defValue_1988_);
return v___x_1991_;
}
else
{
lean_object* v_val_1992_; 
v_val_1992_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_val_1992_);
lean_dec_ref(v___x_1990_);
if (lean_obj_tag(v_val_1992_) == 1)
{
uint8_t v_v_1993_; 
v_v_1993_ = lean_ctor_get_uint8(v_val_1992_, 0);
lean_dec_ref(v_val_1992_);
return v_v_1993_;
}
else
{
uint8_t v___x_1994_; 
lean_dec(v_val_1992_);
v___x_1994_ = lean_unbox(v_defValue_1988_);
return v___x_1994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34___boxed(lean_object* v_opts_1995_, lean_object* v_opt_1996_){
_start:
{
uint8_t v_res_1997_; lean_object* v_r_1998_; 
v_res_1997_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34(v_opts_1995_, v_opt_1996_);
lean_dec_ref(v_opt_1996_);
lean_dec_ref(v_opts_1995_);
v_r_1998_ = lean_box(v_res_1997_);
return v_r_1998_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0(uint8_t v___y_2007_, uint8_t v_suppressElabErrors_2008_, lean_object* v_x_2009_){
_start:
{
if (lean_obj_tag(v_x_2009_) == 1)
{
lean_object* v_pre_2010_; 
v_pre_2010_ = lean_ctor_get(v_x_2009_, 0);
switch(lean_obj_tag(v_pre_2010_))
{
case 1:
{
lean_object* v_pre_2011_; 
v_pre_2011_ = lean_ctor_get(v_pre_2010_, 0);
switch(lean_obj_tag(v_pre_2011_))
{
case 0:
{
lean_object* v_str_2012_; lean_object* v_str_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; 
v_str_2012_ = lean_ctor_get(v_x_2009_, 1);
v_str_2013_ = lean_ctor_get(v_pre_2010_, 1);
v___x_2014_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0));
v___x_2015_ = lean_string_dec_eq(v_str_2013_, v___x_2014_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2016_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1));
v___x_2017_ = lean_string_dec_eq(v_str_2013_, v___x_2016_);
if (v___x_2017_ == 0)
{
return v___y_2007_;
}
else
{
lean_object* v___x_2018_; uint8_t v___x_2019_; 
v___x_2018_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__2));
v___x_2019_ = lean_string_dec_eq(v_str_2012_, v___x_2018_);
if (v___x_2019_ == 0)
{
return v___y_2007_;
}
else
{
return v_suppressElabErrors_2008_;
}
}
}
else
{
lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2020_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__3));
v___x_2021_ = lean_string_dec_eq(v_str_2012_, v___x_2020_);
if (v___x_2021_ == 0)
{
return v___y_2007_;
}
else
{
return v_suppressElabErrors_2008_;
}
}
}
case 1:
{
lean_object* v_pre_2022_; 
v_pre_2022_ = lean_ctor_get(v_pre_2011_, 0);
if (lean_obj_tag(v_pre_2022_) == 0)
{
lean_object* v_str_2023_; lean_object* v_str_2024_; lean_object* v_str_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v_str_2023_ = lean_ctor_get(v_x_2009_, 1);
v_str_2024_ = lean_ctor_get(v_pre_2010_, 1);
v_str_2025_ = lean_ctor_get(v_pre_2011_, 1);
v___x_2026_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4));
v___x_2027_ = lean_string_dec_eq(v_str_2025_, v___x_2026_);
if (v___x_2027_ == 0)
{
return v___y_2007_;
}
else
{
lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2028_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5));
v___x_2029_ = lean_string_dec_eq(v_str_2024_, v___x_2028_);
if (v___x_2029_ == 0)
{
return v___y_2007_;
}
else
{
lean_object* v___x_2030_; uint8_t v___x_2031_; 
v___x_2030_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__6));
v___x_2031_ = lean_string_dec_eq(v_str_2023_, v___x_2030_);
if (v___x_2031_ == 0)
{
return v___y_2007_;
}
else
{
return v_suppressElabErrors_2008_;
}
}
}
}
else
{
return v___y_2007_;
}
}
default: 
{
return v___y_2007_;
}
}
}
case 0:
{
lean_object* v_str_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v_str_2032_ = lean_ctor_get(v_x_2009_, 1);
v___x_2033_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__7));
v___x_2034_ = lean_string_dec_eq(v_str_2032_, v___x_2033_);
if (v___x_2034_ == 0)
{
return v___y_2007_;
}
else
{
return v_suppressElabErrors_2008_;
}
}
default: 
{
return v___y_2007_;
}
}
}
else
{
return v___y_2007_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___boxed(lean_object* v___y_2035_, lean_object* v_suppressElabErrors_2036_, lean_object* v_x_2037_){
_start:
{
uint8_t v___y_23722__boxed_2038_; uint8_t v_suppressElabErrors_boxed_2039_; uint8_t v_res_2040_; lean_object* v_r_2041_; 
v___y_23722__boxed_2038_ = lean_unbox(v___y_2035_);
v_suppressElabErrors_boxed_2039_ = lean_unbox(v_suppressElabErrors_2036_);
v_res_2040_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0(v___y_23722__boxed_2038_, v_suppressElabErrors_boxed_2039_, v_x_2037_);
lean_dec(v_x_2037_);
v_r_2041_ = lean_box(v_res_2040_);
return v_r_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(lean_object* v_ref_2043_, lean_object* v_msgData_2044_, uint8_t v_severity_2045_, uint8_t v_isSilent_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
uint8_t v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; uint8_t v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2089_; uint8_t v___y_2090_; uint8_t v___y_2091_; lean_object* v___y_2092_; uint8_t v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2114_; uint8_t v___y_2115_; lean_object* v___y_2116_; uint8_t v___y_2117_; uint8_t v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2125_; uint8_t v___y_2126_; uint8_t v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; uint8_t v___y_2131_; uint8_t v___x_2136_; lean_object* v___y_2138_; lean_object* v___y_2139_; uint8_t v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; uint8_t v___y_2143_; uint8_t v___y_2144_; uint8_t v___y_2146_; uint8_t v___x_2161_; 
v___x_2136_ = 2;
v___x_2161_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2045_, v___x_2136_);
if (v___x_2161_ == 0)
{
v___y_2146_ = v___x_2161_;
goto v___jp_2145_;
}
else
{
uint8_t v___x_2162_; 
lean_inc_ref(v_msgData_2044_);
v___x_2162_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2044_);
v___y_2146_ = v___x_2162_;
goto v___jp_2145_;
}
v___jp_2052_:
{
lean_object* v___x_2062_; lean_object* v_currNamespace_2063_; lean_object* v_openDecls_2064_; lean_object* v_env_2065_; lean_object* v_nextMacroScope_2066_; lean_object* v_ngen_2067_; lean_object* v_auxDeclNGen_2068_; lean_object* v_traceState_2069_; lean_object* v_cache_2070_; lean_object* v_messages_2071_; lean_object* v_infoState_2072_; lean_object* v_snapshotTasks_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2087_; 
v___x_2062_ = lean_st_ref_take(v___y_2061_);
v_currNamespace_2063_ = lean_ctor_get(v___y_2060_, 6);
lean_inc(v_currNamespace_2063_);
v_openDecls_2064_ = lean_ctor_get(v___y_2060_, 7);
lean_inc(v_openDecls_2064_);
lean_dec_ref(v___y_2060_);
v_env_2065_ = lean_ctor_get(v___x_2062_, 0);
v_nextMacroScope_2066_ = lean_ctor_get(v___x_2062_, 1);
v_ngen_2067_ = lean_ctor_get(v___x_2062_, 2);
v_auxDeclNGen_2068_ = lean_ctor_get(v___x_2062_, 3);
v_traceState_2069_ = lean_ctor_get(v___x_2062_, 4);
v_cache_2070_ = lean_ctor_get(v___x_2062_, 5);
v_messages_2071_ = lean_ctor_get(v___x_2062_, 6);
v_infoState_2072_ = lean_ctor_get(v___x_2062_, 7);
v_snapshotTasks_2073_ = lean_ctor_get(v___x_2062_, 8);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2075_ = v___x_2062_;
v_isShared_2076_ = v_isSharedCheck_2087_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_snapshotTasks_2073_);
lean_inc(v_infoState_2072_);
lean_inc(v_messages_2071_);
lean_inc(v_cache_2070_);
lean_inc(v_traceState_2069_);
lean_inc(v_auxDeclNGen_2068_);
lean_inc(v_ngen_2067_);
lean_inc(v_nextMacroScope_2066_);
lean_inc(v_env_2065_);
lean_dec(v___x_2062_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2087_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2077_, 0, v_currNamespace_2063_);
lean_ctor_set(v___x_2077_, 1, v_openDecls_2064_);
v___x_2078_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
lean_ctor_set(v___x_2078_, 1, v___y_2055_);
v___x_2079_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2079_, 0, v___y_2057_);
lean_ctor_set(v___x_2079_, 1, v___y_2059_);
lean_ctor_set(v___x_2079_, 2, v___y_2054_);
lean_ctor_set(v___x_2079_, 3, v___y_2056_);
lean_ctor_set(v___x_2079_, 4, v___x_2078_);
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*5, v___y_2053_);
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*5 + 1, v___y_2058_);
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*5 + 2, v_isSilent_2046_);
v___x_2080_ = l_Lean_MessageLog_add(v___x_2079_, v_messages_2071_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 6, v___x_2080_);
v___x_2082_ = v___x_2075_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_env_2065_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_nextMacroScope_2066_);
lean_ctor_set(v_reuseFailAlloc_2086_, 2, v_ngen_2067_);
lean_ctor_set(v_reuseFailAlloc_2086_, 3, v_auxDeclNGen_2068_);
lean_ctor_set(v_reuseFailAlloc_2086_, 4, v_traceState_2069_);
lean_ctor_set(v_reuseFailAlloc_2086_, 5, v_cache_2070_);
lean_ctor_set(v_reuseFailAlloc_2086_, 6, v___x_2080_);
lean_ctor_set(v_reuseFailAlloc_2086_, 7, v_infoState_2072_);
lean_ctor_set(v_reuseFailAlloc_2086_, 8, v_snapshotTasks_2073_);
v___x_2082_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2083_ = lean_st_ref_set(v___y_2061_, v___x_2082_);
v___x_2084_ = lean_box(0);
v___x_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
return v___x_2085_;
}
}
}
v___jp_2088_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2112_; 
v___x_2097_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2044_);
v___x_2098_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(v___x_2097_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2112_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2112_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
lean_inc_ref(v___y_2095_);
v___x_2103_ = l_Lean_FileMap_toPosition(v___y_2095_, v___y_2094_);
lean_dec(v___y_2094_);
v___x_2104_ = l_Lean_FileMap_toPosition(v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
v___x_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
v___x_2106_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0));
if (v___y_2091_ == 0)
{
lean_del_object(v___x_2101_);
lean_dec_ref(v___y_2089_);
v___y_2053_ = v___y_2090_;
v___y_2054_ = v___x_2105_;
v___y_2055_ = v_a_2099_;
v___y_2056_ = v___x_2106_;
v___y_2057_ = v___y_2092_;
v___y_2058_ = v___y_2093_;
v___y_2059_ = v___x_2103_;
v___y_2060_ = v___y_2049_;
v___y_2061_ = v___y_2050_;
goto v___jp_2052_;
}
else
{
uint8_t v___x_2107_; 
lean_inc(v_a_2099_);
v___x_2107_ = l_Lean_MessageData_hasTag(v___y_2089_, v_a_2099_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; lean_object* v___x_2110_; 
lean_dec_ref(v___x_2105_);
lean_dec_ref(v___x_2103_);
lean_dec(v_a_2099_);
lean_dec_ref(v___y_2092_);
lean_dec_ref(v___y_2049_);
v___x_2108_ = lean_box(0);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2108_);
v___x_2110_ = v___x_2101_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
else
{
lean_del_object(v___x_2101_);
v___y_2053_ = v___y_2090_;
v___y_2054_ = v___x_2105_;
v___y_2055_ = v_a_2099_;
v___y_2056_ = v___x_2106_;
v___y_2057_ = v___y_2092_;
v___y_2058_ = v___y_2093_;
v___y_2059_ = v___x_2103_;
v___y_2060_ = v___y_2049_;
v___y_2061_ = v___y_2050_;
goto v___jp_2052_;
}
}
}
}
v___jp_2113_:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_Syntax_getTailPos_x3f(v___y_2119_, v___y_2115_);
lean_dec(v___y_2119_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_inc(v___y_2121_);
v___y_2089_ = v___y_2114_;
v___y_2090_ = v___y_2115_;
v___y_2091_ = v___y_2117_;
v___y_2092_ = v___y_2116_;
v___y_2093_ = v___y_2118_;
v___y_2094_ = v___y_2121_;
v___y_2095_ = v___y_2120_;
v___y_2096_ = v___y_2121_;
goto v___jp_2088_;
}
else
{
lean_object* v_val_2123_; 
v_val_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_val_2123_);
lean_dec_ref(v___x_2122_);
v___y_2089_ = v___y_2114_;
v___y_2090_ = v___y_2115_;
v___y_2091_ = v___y_2117_;
v___y_2092_ = v___y_2116_;
v___y_2093_ = v___y_2118_;
v___y_2094_ = v___y_2121_;
v___y_2095_ = v___y_2120_;
v___y_2096_ = v_val_2123_;
goto v___jp_2088_;
}
}
v___jp_2124_:
{
lean_object* v_ref_2132_; lean_object* v___x_2133_; 
v_ref_2132_ = l_Lean_replaceRef(v_ref_2043_, v___y_2129_);
lean_dec(v___y_2129_);
v___x_2133_ = l_Lean_Syntax_getPos_x3f(v_ref_2132_, v___y_2126_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v___x_2134_; 
v___x_2134_ = lean_unsigned_to_nat(0u);
v___y_2114_ = v___y_2125_;
v___y_2115_ = v___y_2126_;
v___y_2116_ = v___y_2128_;
v___y_2117_ = v___y_2127_;
v___y_2118_ = v___y_2131_;
v___y_2119_ = v_ref_2132_;
v___y_2120_ = v___y_2130_;
v___y_2121_ = v___x_2134_;
goto v___jp_2113_;
}
else
{
lean_object* v_val_2135_; 
v_val_2135_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_val_2135_);
lean_dec_ref(v___x_2133_);
v___y_2114_ = v___y_2125_;
v___y_2115_ = v___y_2126_;
v___y_2116_ = v___y_2128_;
v___y_2117_ = v___y_2127_;
v___y_2118_ = v___y_2131_;
v___y_2119_ = v_ref_2132_;
v___y_2120_ = v___y_2130_;
v___y_2121_ = v_val_2135_;
goto v___jp_2113_;
}
}
v___jp_2137_:
{
if (v___y_2144_ == 0)
{
v___y_2125_ = v___y_2141_;
v___y_2126_ = v___y_2143_;
v___y_2127_ = v___y_2140_;
v___y_2128_ = v___y_2139_;
v___y_2129_ = v___y_2138_;
v___y_2130_ = v___y_2142_;
v___y_2131_ = v_severity_2045_;
goto v___jp_2124_;
}
else
{
v___y_2125_ = v___y_2141_;
v___y_2126_ = v___y_2143_;
v___y_2127_ = v___y_2140_;
v___y_2128_ = v___y_2139_;
v___y_2129_ = v___y_2138_;
v___y_2130_ = v___y_2142_;
v___y_2131_ = v___x_2136_;
goto v___jp_2124_;
}
}
v___jp_2145_:
{
if (v___y_2146_ == 0)
{
lean_object* v_fileName_2147_; lean_object* v_fileMap_2148_; lean_object* v_options_2149_; lean_object* v_ref_2150_; uint8_t v_suppressElabErrors_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___f_2154_; uint8_t v___x_2155_; uint8_t v___x_2156_; 
v_fileName_2147_ = lean_ctor_get(v___y_2049_, 0);
v_fileMap_2148_ = lean_ctor_get(v___y_2049_, 1);
v_options_2149_ = lean_ctor_get(v___y_2049_, 2);
v_ref_2150_ = lean_ctor_get(v___y_2049_, 5);
v_suppressElabErrors_2151_ = lean_ctor_get_uint8(v___y_2049_, sizeof(void*)*14 + 1);
v___x_2152_ = lean_box(v___y_2146_);
v___x_2153_ = lean_box(v_suppressElabErrors_2151_);
v___f_2154_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2154_, 0, v___x_2152_);
lean_closure_set(v___f_2154_, 1, v___x_2153_);
v___x_2155_ = 1;
v___x_2156_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2045_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_inc_ref(v_fileMap_2148_);
lean_inc_ref(v_fileName_2147_);
lean_inc(v_ref_2150_);
v___y_2138_ = v_ref_2150_;
v___y_2139_ = v_fileName_2147_;
v___y_2140_ = v_suppressElabErrors_2151_;
v___y_2141_ = v___f_2154_;
v___y_2142_ = v_fileMap_2148_;
v___y_2143_ = v___y_2146_;
v___y_2144_ = v___x_2156_;
goto v___jp_2137_;
}
else
{
lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2157_ = l_Lean_warningAsError;
v___x_2158_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34(v_options_2149_, v___x_2157_);
lean_inc_ref(v_fileMap_2148_);
lean_inc_ref(v_fileName_2147_);
lean_inc(v_ref_2150_);
v___y_2138_ = v_ref_2150_;
v___y_2139_ = v_fileName_2147_;
v___y_2140_ = v_suppressElabErrors_2151_;
v___y_2141_ = v___f_2154_;
v___y_2142_ = v_fileMap_2148_;
v___y_2143_ = v___y_2146_;
v___y_2144_ = v___x_2158_;
goto v___jp_2137_;
}
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec_ref(v___y_2049_);
lean_dec_ref(v_msgData_2044_);
v___x_2159_ = lean_box(0);
v___x_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
return v___x_2160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___boxed(lean_object* v_ref_2163_, lean_object* v_msgData_2164_, lean_object* v_severity_2165_, lean_object* v_isSilent_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
uint8_t v_severity_boxed_2172_; uint8_t v_isSilent_boxed_2173_; lean_object* v_res_2174_; 
v_severity_boxed_2172_ = lean_unbox(v_severity_2165_);
v_isSilent_boxed_2173_ = lean_unbox(v_isSilent_2166_);
v_res_2174_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(v_ref_2163_, v_msgData_2164_, v_severity_boxed_2172_, v_isSilent_boxed_2173_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
lean_dec(v___y_2170_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v_ref_2163_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(lean_object* v_msgData_2175_, uint8_t v_severity_2176_, uint8_t v_isSilent_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_ref_2184_; lean_object* v___x_2185_; 
v_ref_2184_ = lean_ctor_get(v___y_2181_, 5);
lean_inc(v_ref_2184_);
v___x_2185_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(v_ref_2184_, v_msgData_2175_, v_severity_2176_, v_isSilent_2177_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v_ref_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24___boxed(lean_object* v_msgData_2186_, lean_object* v_severity_2187_, lean_object* v_isSilent_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
uint8_t v_severity_boxed_2195_; uint8_t v_isSilent_boxed_2196_; lean_object* v_res_2197_; 
v_severity_boxed_2195_ = lean_unbox(v_severity_2187_);
v_isSilent_boxed_2196_ = lean_unbox(v_isSilent_2188_);
v_res_2197_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(v_msgData_2186_, v_severity_boxed_2195_, v_isSilent_boxed_2196_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15(lean_object* v_msgData_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
uint8_t v___x_2205_; uint8_t v___x_2206_; lean_object* v___x_2207_; 
v___x_2205_ = 1;
v___x_2206_ = 0;
v___x_2207_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(v_msgData_2198_, v___x_2205_, v___x_2206_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15___boxed(lean_object* v_msgData_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15(v_msgData_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
lean_dec(v___y_2213_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
return v_res_2215_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__1(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__0));
v___x_2218_ = l_Lean_stringToMessageData(v___x_2217_);
return v___x_2218_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__4(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = lean_box(0);
v___x_2225_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__3));
v___x_2226_ = l_Lean_mkConst(v___x_2225_, v___x_2224_);
return v___x_2226_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__5(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__4, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__4_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__4);
v___x_2228_ = l_Lean_MessageData_ofExpr(v___x_2227_);
return v___x_2228_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__6(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2229_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__5, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__5_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__5);
v___x_2230_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__1, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__1_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__1);
v___x_2231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
lean_ctor_set(v___x_2231_, 1, v___x_2229_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize(lean_object* v_goal_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v___x_2239_; 
lean_inc(v_a_2237_);
lean_inc_ref(v_a_2236_);
lean_inc(v_a_2235_);
lean_inc_ref(v_a_2234_);
lean_inc(v_goal_2232_);
v___x_2239_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq(v_goal_2232_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref(v___x_2239_);
if (lean_obj_tag(v_a_2240_) == 1)
{
lean_object* v_val_2241_; lean_object* v_fst_2242_; lean_object* v_snd_2243_; lean_object* v___x_2244_; lean_object* v___f_2245_; lean_object* v___x_2246_; 
v_val_2241_ = lean_ctor_get(v_a_2240_, 0);
lean_inc(v_val_2241_);
lean_dec_ref(v_a_2240_);
v_fst_2242_ = lean_ctor_get(v_val_2241_, 0);
lean_inc(v_fst_2242_);
v_snd_2243_ = lean_ctor_get(v_val_2241_, 1);
lean_inc(v_snd_2243_);
lean_dec(v_val_2241_);
v___x_2244_ = l_Lean_instInhabitedExpr;
lean_inc(v_goal_2232_);
v___f_2245_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___boxed), 10, 4);
lean_closure_set(v___f_2245_, 0, v_fst_2242_);
lean_closure_set(v___f_2245_, 1, v___x_2244_);
lean_closure_set(v___f_2245_, 2, v_snd_2243_);
lean_closure_set(v___f_2245_, 3, v_goal_2232_);
v___x_2246_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_goal_2232_, v___f_2245_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
return v___x_2246_;
}
else
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
lean_dec(v_a_2240_);
v___x_2247_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__6);
v___x_2248_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15(v___x_2247_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
lean_dec(v_a_2237_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
lean_dec(v_a_2233_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2255_ == 0)
{
lean_object* v_unused_2256_; 
v_unused_2256_ = lean_ctor_get(v___x_2248_, 0);
lean_dec(v_unused_2256_);
v___x_2250_ = v___x_2248_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_dec(v___x_2248_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 0, v_goal_2232_);
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_goal_2232_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec(v_goal_2232_);
v_a_2257_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2248_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2248_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
lean_dec(v_a_2233_);
lean_dec(v_goal_2232_);
v_a_2265_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2239_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2239_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___boxed(lean_object* v_goal_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize(v_goal_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0(lean_object* v_00_u03b2_2281_, lean_object* v_m_2282_, lean_object* v_a_2283_, lean_object* v_b_2284_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(v_m_2282_, v_a_2283_, v_b_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2(lean_object* v_as_2286_, size_t v_sz_2287_, size_t v_i_2288_, lean_object* v_b_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v___x_2296_; 
v___x_2296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(v_as_2286_, v_sz_2287_, v_i_2288_, v_b_2289_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2___boxed(lean_object* v_as_2297_, lean_object* v_sz_2298_, lean_object* v_i_2299_, lean_object* v_b_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
size_t v_sz_boxed_2307_; size_t v_i_boxed_2308_; lean_object* v_res_2309_; 
v_sz_boxed_2307_ = lean_unbox_usize(v_sz_2298_);
lean_dec(v_sz_2298_);
v_i_boxed_2308_ = lean_unbox_usize(v_i_2299_);
lean_dec(v_i_2299_);
v_res_2309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2(v_as_2297_, v_sz_boxed_2307_, v_i_boxed_2308_, v_b_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v_as_2297_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3(lean_object* v_00_u03b2_2310_, lean_object* v_m_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(v_m_2311_, v_a_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3___boxed(lean_object* v_00_u03b2_2314_, lean_object* v_m_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3(v_00_u03b2_2314_, v_m_2315_, v_a_2316_);
lean_dec_ref(v_a_2316_);
lean_dec_ref(v_m_2315_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5(lean_object* v_00_u03b1_2318_, lean_object* v_inst_2319_, lean_object* v_declInfos_2320_, lean_object* v_k_2321_, uint8_t v_kind_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5___redArg(v_inst_2319_, v_declInfos_2320_, v_k_2321_, v_kind_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5___boxed(lean_object* v_00_u03b1_2330_, lean_object* v_inst_2331_, lean_object* v_declInfos_2332_, lean_object* v_k_2333_, lean_object* v_kind_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
uint8_t v_kind_boxed_2341_; lean_object* v_res_2342_; 
v_kind_boxed_2341_ = lean_unbox(v_kind_2334_);
v_res_2342_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5(v_00_u03b1_2330_, v_inst_2331_, v_declInfos_2332_, v_k_2333_, v_kind_boxed_2341_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12(lean_object* v_00_u03b1_2343_, lean_object* v_name_2344_, uint8_t v_bi_2345_, lean_object* v_type_2346_, lean_object* v_k_2347_, uint8_t v_kind_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(v_name_2344_, v_bi_2345_, v_type_2346_, v_k_2347_, v_kind_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___boxed(lean_object* v_00_u03b1_2356_, lean_object* v_name_2357_, lean_object* v_bi_2358_, lean_object* v_type_2359_, lean_object* v_k_2360_, lean_object* v_kind_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
uint8_t v_bi_boxed_2368_; uint8_t v_kind_boxed_2369_; lean_object* v_res_2370_; 
v_bi_boxed_2368_ = lean_unbox(v_bi_2358_);
v_kind_boxed_2369_ = lean_unbox(v_kind_2361_);
v_res_2370_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12(v_00_u03b1_2356_, v_name_2357_, v_bi_boxed_2368_, v_type_2359_, v_k_2360_, v_kind_boxed_2369_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6(lean_object* v_00_u03b1_2371_, lean_object* v_name_2372_, lean_object* v_type_2373_, lean_object* v_k_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v_name_2372_, v_type_2373_, v_k_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___boxed(lean_object* v_00_u03b1_2382_, lean_object* v_name_2383_, lean_object* v_type_2384_, lean_object* v_k_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6(v_00_u03b1_2382_, v_name_2383_, v_type_2384_, v_k_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7(lean_object* v_mvarId_2393_, lean_object* v_val_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(v_mvarId_2393_, v_val_2394_, v___y_2397_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___boxed(lean_object* v_mvarId_2402_, lean_object* v_val_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7(v_mvarId_2402_, v_val_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9(lean_object* v_00_u03b1_2411_, lean_object* v_msg_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(v_msg_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___boxed(lean_object* v_00_u03b1_2419_, lean_object* v_msg_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9(v_00_u03b1_2419_, v_msg_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
return v_res_2426_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0(lean_object* v_00_u03b2_2427_, lean_object* v_a_2428_, lean_object* v_x_2429_){
_start:
{
uint8_t v___x_2430_; 
v___x_2430_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_2428_, v_x_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2431_, lean_object* v_a_2432_, lean_object* v_x_2433_){
_start:
{
uint8_t v_res_2434_; lean_object* v_r_2435_; 
v_res_2434_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0(v_00_u03b2_2431_, v_a_2432_, v_x_2433_);
lean_dec(v_x_2433_);
lean_dec_ref(v_a_2432_);
v_r_2435_ = lean_box(v_res_2434_);
return v_r_2435_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1(lean_object* v_00_u03b2_2436_, lean_object* v_data_2437_){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(v_data_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2(lean_object* v_00_u03b2_2439_, lean_object* v_a_2440_, lean_object* v_b_2441_, lean_object* v_x_2442_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(v_a_2440_, v_b_2441_, v_x_2442_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6(lean_object* v_00_u03b2_2444_, lean_object* v_a_2445_, lean_object* v_x_2446_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(v_a_2445_, v_x_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2448_, lean_object* v_a_2449_, lean_object* v_x_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6(v_00_u03b2_2448_, v_a_2449_, v_x_2450_);
lean_dec(v_x_2450_);
lean_dec_ref(v_a_2449_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10(lean_object* v_00_u03b1_2452_, lean_object* v_inst_2453_, lean_object* v_declInfos_2454_, lean_object* v_k_2455_, uint8_t v_kind_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___redArg(v_inst_2453_, v_declInfos_2454_, v_k_2455_, v_kind_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___boxed(lean_object* v_00_u03b1_2464_, lean_object* v_inst_2465_, lean_object* v_declInfos_2466_, lean_object* v_k_2467_, lean_object* v_kind_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
uint8_t v_kind_boxed_2475_; lean_object* v_res_2476_; 
v_kind_boxed_2475_ = lean_unbox(v_kind_2468_);
v_res_2476_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10(v_00_u03b1_2464_, v_inst_2465_, v_declInfos_2466_, v_k_2467_, v_kind_boxed_2475_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14(lean_object* v_00_u03b2_2477_, lean_object* v_x_2478_, lean_object* v_x_2479_, lean_object* v_x_2480_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(v_x_2478_, v_x_2479_, v_x_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2482_, lean_object* v_i_2483_, lean_object* v_source_2484_, lean_object* v_target_2485_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3___redArg(v_i_2483_, v_source_2484_, v_target_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14(lean_object* v_00_u03b1_2487_, lean_object* v_inst_2488_, lean_object* v_declInfos_2489_, lean_object* v_k_2490_, uint8_t v_kind_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg(v_inst_2488_, v_declInfos_2489_, v_k_2490_, v_kind_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2499_, lean_object* v_inst_2500_, lean_object* v_declInfos_2501_, lean_object* v_k_2502_, lean_object* v_kind_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
uint8_t v_kind_boxed_2510_; lean_object* v_res_2511_; 
v_kind_boxed_2510_ = lean_unbox(v_kind_2503_);
v_res_2511_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14(v_00_u03b1_2499_, v_inst_2500_, v_declInfos_2501_, v_k_2502_, v_kind_boxed_2510_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19(lean_object* v_00_u03b2_2512_, lean_object* v_x_2513_, size_t v_x_2514_, size_t v_x_2515_, lean_object* v_x_2516_, lean_object* v_x_2517_){
_start:
{
lean_object* v___x_2518_; 
v___x_2518_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_x_2513_, v_x_2514_, v_x_2515_, v_x_2516_, v_x_2517_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___boxed(lean_object* v_00_u03b2_2519_, lean_object* v_x_2520_, lean_object* v_x_2521_, lean_object* v_x_2522_, lean_object* v_x_2523_, lean_object* v_x_2524_){
_start:
{
size_t v_x_24379__boxed_2525_; size_t v_x_24380__boxed_2526_; lean_object* v_res_2527_; 
v_x_24379__boxed_2525_ = lean_unbox_usize(v_x_2521_);
lean_dec(v_x_2521_);
v_x_24380__boxed_2526_ = lean_unbox_usize(v_x_2522_);
lean_dec(v_x_2522_);
v_res_2527_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19(v_00_u03b2_2519_, v_x_2520_, v_x_24379__boxed_2525_, v_x_24380__boxed_2526_, v_x_2523_, v_x_2524_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29(lean_object* v_ref_2528_, lean_object* v_msgData_2529_, uint8_t v_severity_2530_, uint8_t v_isSilent_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v___x_2538_; 
v___x_2538_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(v_ref_2528_, v_msgData_2529_, v_severity_2530_, v_isSilent_2531_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___boxed(lean_object* v_ref_2539_, lean_object* v_msgData_2540_, lean_object* v_severity_2541_, lean_object* v_isSilent_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
uint8_t v_severity_boxed_2549_; uint8_t v_isSilent_boxed_2550_; lean_object* v_res_2551_; 
v_severity_boxed_2549_ = lean_unbox(v_severity_2541_);
v_isSilent_boxed_2550_ = lean_unbox(v_isSilent_2542_);
v_res_2551_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29(v_ref_2539_, v_msgData_2540_, v_severity_boxed_2549_, v_isSilent_boxed_2550_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec(v_ref_2539_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20(lean_object* v_00_u03b2_2552_, lean_object* v_x_2553_, lean_object* v_x_2554_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20___redArg(v_x_2553_, v_x_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30(lean_object* v_00_u03b2_2556_, lean_object* v_n_2557_, lean_object* v_k_2558_, lean_object* v_v_2559_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30___redArg(v_n_2557_, v_k_2558_, v_v_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31(lean_object* v_00_u03b2_2561_, size_t v_depth_2562_, lean_object* v_keys_2563_, lean_object* v_vals_2564_, lean_object* v_heq_2565_, lean_object* v_i_2566_, lean_object* v_entries_2567_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(v_depth_2562_, v_keys_2563_, v_vals_2564_, v_i_2566_, v_entries_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___boxed(lean_object* v_00_u03b2_2569_, lean_object* v_depth_2570_, lean_object* v_keys_2571_, lean_object* v_vals_2572_, lean_object* v_heq_2573_, lean_object* v_i_2574_, lean_object* v_entries_2575_){
_start:
{
size_t v_depth_boxed_2576_; lean_object* v_res_2577_; 
v_depth_boxed_2576_ = lean_unbox_usize(v_depth_2570_);
lean_dec(v_depth_2570_);
v_res_2577_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31(v_00_u03b2_2569_, v_depth_boxed_2576_, v_keys_2571_, v_vals_2572_, v_heq_2573_, v_i_2574_, v_entries_2575_);
lean_dec_ref(v_vals_2572_);
lean_dec_ref(v_keys_2571_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34(lean_object* v_00_u03b1_2578_, lean_object* v_acc_2579_, lean_object* v_declInfos_2580_, lean_object* v_k_2581_, uint8_t v_kind_2582_, lean_object* v_inst_2583_, lean_object* v_name_2584_, uint8_t v_bi_2585_, lean_object* v_type_2586_, uint8_t v_kind_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg(v_acc_2579_, v_declInfos_2580_, v_k_2581_, v_kind_2582_, v_inst_2583_, v_name_2584_, v_bi_2585_, v_type_2586_, v_kind_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___boxed(lean_object* v_00_u03b1_2595_, lean_object* v_acc_2596_, lean_object* v_declInfos_2597_, lean_object* v_k_2598_, lean_object* v_kind_2599_, lean_object* v_inst_2600_, lean_object* v_name_2601_, lean_object* v_bi_2602_, lean_object* v_type_2603_, lean_object* v_kind_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
uint8_t v_kind_boxed_2611_; uint8_t v_bi_boxed_2612_; uint8_t v_kind_boxed_2613_; lean_object* v_res_2614_; 
v_kind_boxed_2611_ = lean_unbox(v_kind_2599_);
v_bi_boxed_2612_ = lean_unbox(v_bi_2602_);
v_kind_boxed_2613_ = lean_unbox(v_kind_2604_);
v_res_2614_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34(v_00_u03b1_2595_, v_acc_2596_, v_declInfos_2597_, v_k_2598_, v_kind_boxed_2611_, v_inst_2600_, v_name_2601_, v_bi_boxed_2612_, v_type_2603_, v_kind_boxed_2613_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(lean_object* v_00_u03b1_2615_, lean_object* v_declInfos_2616_, lean_object* v_k_2617_, uint8_t v_kind_2618_, lean_object* v_inst_2619_, lean_object* v_acc_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v___x_2627_; 
v___x_2627_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg(v_declInfos_2616_, v_k_2617_, v_kind_2618_, v_inst_2619_, v_acc_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___boxed(lean_object* v_00_u03b1_2628_, lean_object* v_declInfos_2629_, lean_object* v_k_2630_, lean_object* v_kind_2631_, lean_object* v_inst_2632_, lean_object* v_acc_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
uint8_t v_kind_boxed_2640_; lean_object* v_res_2641_; 
v_kind_boxed_2640_ = lean_unbox(v_kind_2631_);
v_res_2641_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(v_00_u03b1_2628_, v_declInfos_2629_, v_k_2630_, v_kind_boxed_2640_, v_inst_2632_, v_acc_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32(lean_object* v_00_u03b2_2642_, lean_object* v_x_2643_, lean_object* v_x_2644_, lean_object* v_x_2645_, lean_object* v_x_2646_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32___redArg(v_x_2643_, v_x_2644_, v_x_2645_, v_x_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___redArg(lean_object* v_e_2648_, lean_object* v___y_2649_){
_start:
{
uint8_t v___x_2651_; 
v___x_2651_ = l_Lean_Expr_hasMVar(v_e_2648_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; 
v___x_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2652_, 0, v_e_2648_);
return v___x_2652_;
}
else
{
lean_object* v___x_2653_; lean_object* v_mctx_2654_; lean_object* v___x_2655_; lean_object* v_fst_2656_; lean_object* v_snd_2657_; lean_object* v___x_2658_; lean_object* v_cache_2659_; lean_object* v_zetaDeltaFVarIds_2660_; lean_object* v_postponed_2661_; lean_object* v_diag_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2671_; 
v___x_2653_ = lean_st_ref_get(v___y_2649_);
v_mctx_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc_ref(v_mctx_2654_);
lean_dec(v___x_2653_);
v___x_2655_ = l_Lean_instantiateMVarsCore(v_mctx_2654_, v_e_2648_);
v_fst_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_fst_2656_);
v_snd_2657_ = lean_ctor_get(v___x_2655_, 1);
lean_inc(v_snd_2657_);
lean_dec_ref(v___x_2655_);
v___x_2658_ = lean_st_ref_take(v___y_2649_);
v_cache_2659_ = lean_ctor_get(v___x_2658_, 1);
v_zetaDeltaFVarIds_2660_ = lean_ctor_get(v___x_2658_, 2);
v_postponed_2661_ = lean_ctor_get(v___x_2658_, 3);
v_diag_2662_ = lean_ctor_get(v___x_2658_, 4);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2671_ == 0)
{
lean_object* v_unused_2672_; 
v_unused_2672_ = lean_ctor_get(v___x_2658_, 0);
lean_dec(v_unused_2672_);
v___x_2664_ = v___x_2658_;
v_isShared_2665_ = v_isSharedCheck_2671_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_diag_2662_);
lean_inc(v_postponed_2661_);
lean_inc(v_zetaDeltaFVarIds_2660_);
lean_inc(v_cache_2659_);
lean_dec(v___x_2658_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2671_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v_snd_2657_);
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_snd_2657_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v_cache_2659_);
lean_ctor_set(v_reuseFailAlloc_2670_, 2, v_zetaDeltaFVarIds_2660_);
lean_ctor_set(v_reuseFailAlloc_2670_, 3, v_postponed_2661_);
lean_ctor_set(v_reuseFailAlloc_2670_, 4, v_diag_2662_);
v___x_2667_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2668_ = lean_st_ref_set(v___y_2649_, v___x_2667_);
v___x_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2669_, 0, v_fst_2656_);
return v___x_2669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___redArg___boxed(lean_object* v_e_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___redArg(v_e_2673_, v___y_2674_);
lean_dec(v___y_2674_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2(lean_object* v_e_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___redArg(v_e_2677_, v___y_2680_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___boxed(lean_object* v_e_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2(v_e_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
return v_res_2692_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(lean_object* v_m_2693_, lean_object* v_a_2694_){
_start:
{
lean_object* v_buckets_2695_; lean_object* v___x_2696_; uint64_t v___x_2697_; uint64_t v___x_2698_; uint64_t v___x_2699_; uint64_t v_fold_2700_; uint64_t v___x_2701_; uint64_t v___x_2702_; uint64_t v___x_2703_; size_t v___x_2704_; size_t v___x_2705_; size_t v___x_2706_; size_t v___x_2707_; size_t v___x_2708_; lean_object* v___x_2709_; uint8_t v___x_2710_; 
v_buckets_2695_ = lean_ctor_get(v_m_2693_, 1);
v___x_2696_ = lean_array_get_size(v_buckets_2695_);
v___x_2697_ = l_Lean_Expr_hash(v_a_2694_);
v___x_2698_ = 32ULL;
v___x_2699_ = lean_uint64_shift_right(v___x_2697_, v___x_2698_);
v_fold_2700_ = lean_uint64_xor(v___x_2697_, v___x_2699_);
v___x_2701_ = 16ULL;
v___x_2702_ = lean_uint64_shift_right(v_fold_2700_, v___x_2701_);
v___x_2703_ = lean_uint64_xor(v_fold_2700_, v___x_2702_);
v___x_2704_ = lean_uint64_to_usize(v___x_2703_);
v___x_2705_ = lean_usize_of_nat(v___x_2696_);
v___x_2706_ = ((size_t)1ULL);
v___x_2707_ = lean_usize_sub(v___x_2705_, v___x_2706_);
v___x_2708_ = lean_usize_land(v___x_2704_, v___x_2707_);
v___x_2709_ = lean_array_uget_borrowed(v_buckets_2695_, v___x_2708_);
v___x_2710_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_2694_, v___x_2709_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg___boxed(lean_object* v_m_2711_, lean_object* v_a_2712_){
_start:
{
uint8_t v_res_2713_; lean_object* v_r_2714_; 
v_res_2713_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(v_m_2711_, v_a_2712_);
lean_dec_ref(v_a_2712_);
lean_dec_ref(v_m_2711_);
v_r_2714_ = lean_box(v_res_2713_);
return v_r_2714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__0___redArg(lean_object* v_m_2715_, lean_object* v_a_2716_, lean_object* v_b_2717_){
_start:
{
lean_object* v_size_2718_; lean_object* v_buckets_2719_; lean_object* v___x_2720_; uint64_t v___x_2721_; uint64_t v___x_2722_; uint64_t v___x_2723_; uint64_t v_fold_2724_; uint64_t v___x_2725_; uint64_t v___x_2726_; uint64_t v___x_2727_; size_t v___x_2728_; size_t v___x_2729_; size_t v___x_2730_; size_t v___x_2731_; size_t v___x_2732_; lean_object* v_bkt_2733_; uint8_t v___x_2734_; 
v_size_2718_ = lean_ctor_get(v_m_2715_, 0);
v_buckets_2719_ = lean_ctor_get(v_m_2715_, 1);
v___x_2720_ = lean_array_get_size(v_buckets_2719_);
v___x_2721_ = l_Lean_Expr_hash(v_a_2716_);
v___x_2722_ = 32ULL;
v___x_2723_ = lean_uint64_shift_right(v___x_2721_, v___x_2722_);
v_fold_2724_ = lean_uint64_xor(v___x_2721_, v___x_2723_);
v___x_2725_ = 16ULL;
v___x_2726_ = lean_uint64_shift_right(v_fold_2724_, v___x_2725_);
v___x_2727_ = lean_uint64_xor(v_fold_2724_, v___x_2726_);
v___x_2728_ = lean_uint64_to_usize(v___x_2727_);
v___x_2729_ = lean_usize_of_nat(v___x_2720_);
v___x_2730_ = ((size_t)1ULL);
v___x_2731_ = lean_usize_sub(v___x_2729_, v___x_2730_);
v___x_2732_ = lean_usize_land(v___x_2728_, v___x_2731_);
v_bkt_2733_ = lean_array_uget_borrowed(v_buckets_2719_, v___x_2732_);
v___x_2734_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_2716_, v_bkt_2733_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2755_; 
lean_inc_ref(v_buckets_2719_);
lean_inc(v_size_2718_);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_m_2715_);
if (v_isSharedCheck_2755_ == 0)
{
lean_object* v_unused_2756_; lean_object* v_unused_2757_; 
v_unused_2756_ = lean_ctor_get(v_m_2715_, 1);
lean_dec(v_unused_2756_);
v_unused_2757_ = lean_ctor_get(v_m_2715_, 0);
lean_dec(v_unused_2757_);
v___x_2736_ = v_m_2715_;
v_isShared_2737_ = v_isSharedCheck_2755_;
goto v_resetjp_2735_;
}
else
{
lean_dec(v_m_2715_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2755_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2738_; lean_object* v_size_x27_2739_; lean_object* v___x_2740_; lean_object* v_buckets_x27_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; uint8_t v___x_2747_; 
v___x_2738_ = lean_unsigned_to_nat(1u);
v_size_x27_2739_ = lean_nat_add(v_size_2718_, v___x_2738_);
lean_dec(v_size_2718_);
lean_inc(v_bkt_2733_);
v___x_2740_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2740_, 0, v_a_2716_);
lean_ctor_set(v___x_2740_, 1, v_b_2717_);
lean_ctor_set(v___x_2740_, 2, v_bkt_2733_);
v_buckets_x27_2741_ = lean_array_uset(v_buckets_2719_, v___x_2732_, v___x_2740_);
v___x_2742_ = lean_unsigned_to_nat(4u);
v___x_2743_ = lean_nat_mul(v_size_x27_2739_, v___x_2742_);
v___x_2744_ = lean_unsigned_to_nat(3u);
v___x_2745_ = lean_nat_div(v___x_2743_, v___x_2744_);
lean_dec(v___x_2743_);
v___x_2746_ = lean_array_get_size(v_buckets_x27_2741_);
v___x_2747_ = lean_nat_dec_le(v___x_2745_, v___x_2746_);
lean_dec(v___x_2745_);
if (v___x_2747_ == 0)
{
lean_object* v_val_2748_; lean_object* v___x_2750_; 
v_val_2748_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(v_buckets_x27_2741_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 1, v_val_2748_);
lean_ctor_set(v___x_2736_, 0, v_size_x27_2739_);
v___x_2750_ = v___x_2736_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_size_x27_2739_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v_val_2748_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
else
{
lean_object* v___x_2753_; 
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 1, v_buckets_x27_2741_);
lean_ctor_set(v___x_2736_, 0, v_size_x27_2739_);
v___x_2753_ = v___x_2736_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_size_x27_2739_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v_buckets_x27_2741_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
else
{
lean_dec(v_b_2717_);
lean_dec_ref(v_a_2716_);
return v_m_2715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(lean_object* v_e_2758_, lean_object* v_a_2759_){
_start:
{
lean_object* v___x_2761_; lean_object* v_checked_2762_; uint8_t v___x_2763_; 
v___x_2761_ = lean_st_ref_get(v_a_2759_);
v_checked_2762_ = lean_ctor_get(v___x_2761_, 1);
lean_inc_ref(v_checked_2762_);
lean_dec(v___x_2761_);
v___x_2763_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(v_checked_2762_, v_e_2758_);
lean_dec_ref(v_checked_2762_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; lean_object* v_visited_2765_; lean_object* v_checked_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2778_; 
v___x_2764_ = lean_st_ref_take(v_a_2759_);
v_visited_2765_ = lean_ctor_get(v___x_2764_, 0);
v_checked_2766_ = lean_ctor_get(v___x_2764_, 1);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2768_ = v___x_2764_;
v_isShared_2769_ = v_isSharedCheck_2778_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_checked_2766_);
lean_inc(v_visited_2765_);
lean_dec(v___x_2764_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2778_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2773_; 
v___x_2770_ = lean_box(0);
v___x_2771_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__0___redArg(v_checked_2766_, v_e_2758_, v___x_2770_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 1, v___x_2771_);
v___x_2773_ = v___x_2768_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_visited_2765_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v___x_2771_);
v___x_2773_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2774_ = lean_st_ref_set(v_a_2759_, v___x_2773_);
v___x_2775_ = lean_box(v___x_2763_);
v___x_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2775_);
return v___x_2776_;
}
}
}
else
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
lean_dec_ref(v_e_2758_);
v___x_2779_ = lean_box(v___x_2763_);
v___x_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2779_);
return v___x_2780_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_e_2781_, lean_object* v_a_2782_, lean_object* v___y_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(v_e_2781_, v_a_2782_);
lean_dec(v_a_2782_);
return v_res_2784_;
}
}
static size_t _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0(void){
_start:
{
size_t v___x_2785_; size_t v___x_2786_; size_t v___x_2787_; 
v___x_2785_ = ((size_t)1ULL);
v___x_2786_ = ((size_t)8192ULL);
v___x_2787_ = lean_usize_sub(v___x_2786_, v___x_2785_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(lean_object* v_e_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v___x_2791_; lean_object* v_visited_2792_; size_t v___x_2793_; size_t v___x_2794_; size_t v___x_2795_; lean_object* v___x_2796_; size_t v___x_2797_; uint8_t v___x_2798_; 
v___x_2791_ = lean_st_ref_get(v_a_2789_);
v_visited_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc_ref(v_visited_2792_);
lean_dec(v___x_2791_);
v___x_2793_ = lean_ptr_addr(v_e_2788_);
v___x_2794_ = lean_usize_once(&l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0, &l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0);
v___x_2795_ = lean_usize_mod(v___x_2793_, v___x_2794_);
v___x_2796_ = lean_array_uget(v_visited_2792_, v___x_2795_);
lean_dec_ref(v_visited_2792_);
v___x_2797_ = lean_ptr_addr(v___x_2796_);
lean_dec(v___x_2796_);
v___x_2798_ = lean_usize_dec_eq(v___x_2797_, v___x_2793_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; lean_object* v_visited_2800_; lean_object* v_checked_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2812_; 
v___x_2799_ = lean_st_ref_take(v_a_2789_);
v_visited_2800_ = lean_ctor_get(v___x_2799_, 0);
v_checked_2801_ = lean_ctor_get(v___x_2799_, 1);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2803_ = v___x_2799_;
v_isShared_2804_ = v_isSharedCheck_2812_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_checked_2801_);
lean_inc(v_visited_2800_);
lean_dec(v___x_2799_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2812_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2805_; lean_object* v___x_2807_; 
v___x_2805_ = lean_array_uset(v_visited_2800_, v___x_2795_, v_e_2788_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 0, v___x_2805_);
v___x_2807_ = v___x_2803_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2805_);
lean_ctor_set(v_reuseFailAlloc_2811_, 1, v_checked_2801_);
v___x_2807_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2808_ = lean_st_ref_set(v_a_2789_, v___x_2807_);
v___x_2809_ = lean_box(v___x_2798_);
v___x_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2809_);
return v___x_2810_;
}
}
}
else
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
lean_dec_ref(v_e_2788_);
v___x_2813_ = lean_box(v___x_2798_);
v___x_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
return v___x_2814_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_e_2815_, lean_object* v_a_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(v_e_2815_, v_a_2816_);
lean_dec(v_a_2816_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(lean_object* v_p_2819_, lean_object* v_f_2820_, uint8_t v_stopWhenVisited_2821_, lean_object* v_e_2822_, lean_object* v_a_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v_d_2836_; lean_object* v_b_2837_; lean_object* v___y_2838_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___x_2868_; 
lean_inc_ref(v_e_2822_);
v___x_2868_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(v_e_2822_, v_a_2823_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2901_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2871_ = v___x_2868_;
v_isShared_2872_ = v_isSharedCheck_2901_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2868_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2901_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
uint8_t v___x_2873_; 
v___x_2873_ = lean_unbox(v_a_2869_);
lean_dec(v_a_2869_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; uint8_t v___x_2875_; 
lean_del_object(v___x_2871_);
lean_inc_ref(v_p_2819_);
lean_inc_ref(v_e_2822_);
v___x_2874_ = lean_apply_1(v_p_2819_, v_e_2822_);
v___x_2875_ = lean_unbox(v___x_2874_);
if (v___x_2875_ == 0)
{
v___y_2842_ = v_a_2823_;
v___y_2843_ = v___y_2824_;
v___y_2844_ = v___y_2825_;
v___y_2845_ = v___y_2826_;
v___y_2846_ = v___y_2827_;
v___y_2847_ = v___y_2828_;
goto v___jp_2841_;
}
else
{
lean_object* v___x_2876_; 
lean_inc_ref(v_e_2822_);
v___x_2876_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(v_e_2822_, v_a_2823_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; uint8_t v___x_2878_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
lean_dec_ref(v___x_2876_);
v___x_2878_ = lean_unbox(v_a_2877_);
lean_dec(v_a_2877_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; 
lean_inc_ref(v_f_2820_);
lean_inc(v___y_2828_);
lean_inc_ref(v___y_2827_);
lean_inc(v___y_2826_);
lean_inc_ref(v___y_2825_);
lean_inc(v___y_2824_);
lean_inc_ref(v_e_2822_);
v___x_2879_ = lean_apply_7(v_f_2820_, v_e_2822_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, lean_box(0));
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2887_; 
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2887_ == 0)
{
lean_object* v_unused_2888_; 
v_unused_2888_ = lean_ctor_get(v___x_2879_, 0);
lean_dec(v_unused_2888_);
v___x_2881_ = v___x_2879_;
v_isShared_2882_ = v_isSharedCheck_2887_;
goto v_resetjp_2880_;
}
else
{
lean_dec(v___x_2879_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2887_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
if (v_stopWhenVisited_2821_ == 0)
{
lean_del_object(v___x_2881_);
v___y_2842_ = v_a_2823_;
v___y_2843_ = v___y_2824_;
v___y_2844_ = v___y_2825_;
v___y_2845_ = v___y_2826_;
v___y_2846_ = v___y_2827_;
v___y_2847_ = v___y_2828_;
goto v___jp_2841_;
}
else
{
lean_object* v___x_2883_; lean_object* v___x_2885_; 
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v_e_2822_);
lean_dec_ref(v_f_2820_);
lean_dec_ref(v_p_2819_);
v___x_2883_ = lean_box(0);
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
}
else
{
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v_e_2822_);
lean_dec_ref(v_f_2820_);
lean_dec_ref(v_p_2819_);
return v___x_2879_;
}
}
else
{
v___y_2842_ = v_a_2823_;
v___y_2843_ = v___y_2824_;
v___y_2844_ = v___y_2825_;
v___y_2845_ = v___y_2826_;
v___y_2846_ = v___y_2827_;
v___y_2847_ = v___y_2828_;
goto v___jp_2841_;
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v_e_2822_);
lean_dec_ref(v_f_2820_);
lean_dec_ref(v_p_2819_);
v_a_2889_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2876_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2876_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
}
else
{
lean_object* v___x_2897_; lean_object* v___x_2899_; 
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v_e_2822_);
lean_dec_ref(v_f_2820_);
lean_dec_ref(v_p_2819_);
v___x_2897_ = lean_box(0);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v___x_2897_);
v___x_2899_ = v___x_2871_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2897_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
else
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v_e_2822_);
lean_dec_ref(v_f_2820_);
lean_dec_ref(v_p_2819_);
v_a_2902_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2868_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2868_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
v___jp_2830_:
{
lean_object* v___x_2839_; 
lean_inc(v___y_2832_);
lean_inc_ref(v___y_2835_);
lean_inc(v___y_2834_);
lean_inc_ref(v___y_2831_);
lean_inc(v___y_2833_);
lean_inc_ref(v_f_2820_);
lean_inc_ref(v_p_2819_);
v___x_2839_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2819_, v_f_2820_, v_stopWhenVisited_2821_, v_d_2836_, v___y_2838_, v___y_2833_, v___y_2831_, v___y_2834_, v___y_2835_, v___y_2832_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_dec_ref(v___x_2839_);
v_e_2822_ = v_b_2837_;
v_a_2823_ = v___y_2838_;
v___y_2824_ = v___y_2833_;
v___y_2825_ = v___y_2831_;
v___y_2826_ = v___y_2834_;
v___y_2827_ = v___y_2835_;
v___y_2828_ = v___y_2832_;
goto _start;
}
else
{
lean_dec_ref(v_b_2837_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
lean_dec_ref(v_f_2820_);
lean_dec_ref(v_p_2819_);
return v___x_2839_;
}
}
v___jp_2841_:
{
switch(lean_obj_tag(v_e_2822_))
{
case 7:
{
lean_object* v_binderType_2848_; lean_object* v_body_2849_; 
v_binderType_2848_ = lean_ctor_get(v_e_2822_, 1);
lean_inc_ref(v_binderType_2848_);
v_body_2849_ = lean_ctor_get(v_e_2822_, 2);
lean_inc_ref(v_body_2849_);
lean_dec_ref(v_e_2822_);
v___y_2831_ = v___y_2844_;
v___y_2832_ = v___y_2847_;
v___y_2833_ = v___y_2843_;
v___y_2834_ = v___y_2845_;
v___y_2835_ = v___y_2846_;
v_d_2836_ = v_binderType_2848_;
v_b_2837_ = v_body_2849_;
v___y_2838_ = v___y_2842_;
goto v___jp_2830_;
}
case 6:
{
lean_object* v_binderType_2850_; lean_object* v_body_2851_; 
v_binderType_2850_ = lean_ctor_get(v_e_2822_, 1);
lean_inc_ref(v_binderType_2850_);
v_body_2851_ = lean_ctor_get(v_e_2822_, 2);
lean_inc_ref(v_body_2851_);
lean_dec_ref(v_e_2822_);
v___y_2831_ = v___y_2844_;
v___y_2832_ = v___y_2847_;
v___y_2833_ = v___y_2843_;
v___y_2834_ = v___y_2845_;
v___y_2835_ = v___y_2846_;
v_d_2836_ = v_binderType_2850_;
v_b_2837_ = v_body_2851_;
v___y_2838_ = v___y_2842_;
goto v___jp_2830_;
}
case 8:
{
lean_object* v_type_2852_; lean_object* v_value_2853_; lean_object* v_body_2854_; lean_object* v___x_2855_; 
v_type_2852_ = lean_ctor_get(v_e_2822_, 1);
lean_inc_ref(v_type_2852_);
v_value_2853_ = lean_ctor_get(v_e_2822_, 2);
lean_inc_ref(v_value_2853_);
v_body_2854_ = lean_ctor_get(v_e_2822_, 3);
lean_inc_ref(v_body_2854_);
lean_dec_ref(v_e_2822_);
lean_inc(v___y_2847_);
lean_inc_ref(v___y_2846_);
lean_inc(v___y_2845_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc_ref(v_f_2820_);
lean_inc_ref(v_p_2819_);
v___x_2855_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2819_, v_f_2820_, v_stopWhenVisited_2821_, v_type_2852_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v___x_2856_; 
lean_dec_ref(v___x_2855_);
lean_inc(v___y_2847_);
lean_inc_ref(v___y_2846_);
lean_inc(v___y_2845_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc_ref(v_f_2820_);
lean_inc_ref(v_p_2819_);
v___x_2856_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2819_, v_f_2820_, v_stopWhenVisited_2821_, v_value_2853_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_dec_ref(v___x_2856_);
v_e_2822_ = v_body_2854_;
v_a_2823_ = v___y_2842_;
v___y_2824_ = v___y_2843_;
v___y_2825_ = v___y_2844_;
v___y_2826_ = v___y_2845_;
v___y_2827_ = v___y_2846_;
v___y_2828_ = v___y_2847_;
goto _start;
}
else
{
lean_dec_ref(v_body_2854_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v_f_2820_);
lean_dec_ref(v_p_2819_);
return v___x_2856_;
}
}
else
{
lean_dec_ref(v_body_2854_);
lean_dec_ref(v_value_2853_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v_f_2820_);
lean_dec_ref(v_p_2819_);
return v___x_2855_;
}
}
case 5:
{
lean_object* v_fn_2858_; lean_object* v_arg_2859_; lean_object* v___x_2860_; 
v_fn_2858_ = lean_ctor_get(v_e_2822_, 0);
lean_inc_ref(v_fn_2858_);
v_arg_2859_ = lean_ctor_get(v_e_2822_, 1);
lean_inc_ref(v_arg_2859_);
lean_dec_ref(v_e_2822_);
lean_inc(v___y_2847_);
lean_inc_ref(v___y_2846_);
lean_inc(v___y_2845_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc_ref(v_f_2820_);
lean_inc_ref(v_p_2819_);
v___x_2860_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2819_, v_f_2820_, v_stopWhenVisited_2821_, v_fn_2858_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_dec_ref(v___x_2860_);
v_e_2822_ = v_arg_2859_;
v_a_2823_ = v___y_2842_;
v___y_2824_ = v___y_2843_;
v___y_2825_ = v___y_2844_;
v___y_2826_ = v___y_2845_;
v___y_2827_ = v___y_2846_;
v___y_2828_ = v___y_2847_;
goto _start;
}
else
{
lean_dec_ref(v_arg_2859_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v_f_2820_);
lean_dec_ref(v_p_2819_);
return v___x_2860_;
}
}
case 10:
{
lean_object* v_expr_2862_; 
v_expr_2862_ = lean_ctor_get(v_e_2822_, 1);
lean_inc_ref(v_expr_2862_);
lean_dec_ref(v_e_2822_);
v_e_2822_ = v_expr_2862_;
v_a_2823_ = v___y_2842_;
v___y_2824_ = v___y_2843_;
v___y_2825_ = v___y_2844_;
v___y_2826_ = v___y_2845_;
v___y_2827_ = v___y_2846_;
v___y_2828_ = v___y_2847_;
goto _start;
}
case 11:
{
lean_object* v_struct_2864_; 
v_struct_2864_ = lean_ctor_get(v_e_2822_, 2);
lean_inc_ref(v_struct_2864_);
lean_dec_ref(v_e_2822_);
v_e_2822_ = v_struct_2864_;
v_a_2823_ = v___y_2842_;
v___y_2824_ = v___y_2843_;
v___y_2825_ = v___y_2844_;
v___y_2826_ = v___y_2845_;
v___y_2827_ = v___y_2846_;
v___y_2828_ = v___y_2847_;
goto _start;
}
default: 
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v_e_2822_);
lean_dec_ref(v_f_2820_);
lean_dec_ref(v_p_2819_);
v___x_2866_ = lean_box(0);
v___x_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2866_);
return v___x_2867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5___boxed(lean_object* v_p_2910_, lean_object* v_f_2911_, lean_object* v_stopWhenVisited_2912_, lean_object* v_e_2913_, lean_object* v_a_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
uint8_t v_stopWhenVisited_boxed_2921_; lean_object* v_res_2922_; 
v_stopWhenVisited_boxed_2921_ = lean_unbox(v_stopWhenVisited_2912_);
v_res_2922_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2910_, v_f_2911_, v_stopWhenVisited_boxed_2921_, v_e_2913_, v_a_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
lean_dec(v_a_2914_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3(lean_object* v_p_2923_, lean_object* v_f_2924_, lean_object* v_e_2925_, uint8_t v_stopWhenVisited_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2933_ = l_Lean_ForEachExprWhere_initCache;
v___x_2934_ = lean_st_mk_ref(v___x_2933_);
v___x_2935_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2923_, v_f_2924_, v_stopWhenVisited_2926_, v_e_2925_, v___x_2934_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2944_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2938_ = v___x_2935_;
v_isShared_2939_ = v_isSharedCheck_2944_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2935_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2944_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2940_; lean_object* v___x_2942_; 
v___x_2940_ = lean_st_ref_get(v___x_2934_);
lean_dec(v___x_2934_);
lean_dec(v___x_2940_);
if (v_isShared_2939_ == 0)
{
v___x_2942_ = v___x_2938_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2936_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
else
{
lean_dec(v___x_2934_);
return v___x_2935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3___boxed(lean_object* v_p_2945_, lean_object* v_f_2946_, lean_object* v_e_2947_, lean_object* v_stopWhenVisited_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
uint8_t v_stopWhenVisited_boxed_2955_; lean_object* v_res_2956_; 
v_stopWhenVisited_boxed_2955_ = lean_unbox(v_stopWhenVisited_2948_);
v_res_2956_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3(v_p_2945_, v_f_2946_, v_e_2947_, v_stopWhenVisited_boxed_2955_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
return v_res_2956_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(lean_object* v_a_2957_, lean_object* v_x_2958_){
_start:
{
if (lean_obj_tag(v_x_2958_) == 0)
{
uint8_t v___x_2959_; 
v___x_2959_ = 0;
return v___x_2959_;
}
else
{
lean_object* v_key_2960_; lean_object* v_tail_2961_; uint8_t v___x_2962_; 
v_key_2960_ = lean_ctor_get(v_x_2958_, 0);
v_tail_2961_ = lean_ctor_get(v_x_2958_, 2);
v___x_2962_ = l_Lean_instBEqFVarId_beq(v_key_2960_, v_a_2957_);
if (v___x_2962_ == 0)
{
v_x_2958_ = v_tail_2961_;
goto _start;
}
else
{
return v___x_2962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg___boxed(lean_object* v_a_2964_, lean_object* v_x_2965_){
_start:
{
uint8_t v_res_2966_; lean_object* v_r_2967_; 
v_res_2966_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(v_a_2964_, v_x_2965_);
lean_dec(v_x_2965_);
lean_dec(v_a_2964_);
v_r_2967_ = lean_box(v_res_2966_);
return v_r_2967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_2968_, lean_object* v_x_2969_){
_start:
{
if (lean_obj_tag(v_x_2969_) == 0)
{
return v_x_2968_;
}
else
{
lean_object* v_key_2970_; lean_object* v_value_2971_; lean_object* v_tail_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2995_; 
v_key_2970_ = lean_ctor_get(v_x_2969_, 0);
v_value_2971_ = lean_ctor_get(v_x_2969_, 1);
v_tail_2972_ = lean_ctor_get(v_x_2969_, 2);
v_isSharedCheck_2995_ = !lean_is_exclusive(v_x_2969_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2974_ = v_x_2969_;
v_isShared_2975_ = v_isSharedCheck_2995_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_tail_2972_);
lean_inc(v_value_2971_);
lean_inc(v_key_2970_);
lean_dec(v_x_2969_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2995_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; uint64_t v___x_2977_; uint64_t v___x_2978_; uint64_t v___x_2979_; uint64_t v_fold_2980_; uint64_t v___x_2981_; uint64_t v___x_2982_; uint64_t v___x_2983_; size_t v___x_2984_; size_t v___x_2985_; size_t v___x_2986_; size_t v___x_2987_; size_t v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2991_; 
v___x_2976_ = lean_array_get_size(v_x_2968_);
v___x_2977_ = l_Lean_instHashableFVarId_hash(v_key_2970_);
v___x_2978_ = 32ULL;
v___x_2979_ = lean_uint64_shift_right(v___x_2977_, v___x_2978_);
v_fold_2980_ = lean_uint64_xor(v___x_2977_, v___x_2979_);
v___x_2981_ = 16ULL;
v___x_2982_ = lean_uint64_shift_right(v_fold_2980_, v___x_2981_);
v___x_2983_ = lean_uint64_xor(v_fold_2980_, v___x_2982_);
v___x_2984_ = lean_uint64_to_usize(v___x_2983_);
v___x_2985_ = lean_usize_of_nat(v___x_2976_);
v___x_2986_ = ((size_t)1ULL);
v___x_2987_ = lean_usize_sub(v___x_2985_, v___x_2986_);
v___x_2988_ = lean_usize_land(v___x_2984_, v___x_2987_);
v___x_2989_ = lean_array_uget_borrowed(v_x_2968_, v___x_2988_);
lean_inc(v___x_2989_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 2, v___x_2989_);
v___x_2991_ = v___x_2974_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_key_2970_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v_value_2971_);
lean_ctor_set(v_reuseFailAlloc_2994_, 2, v___x_2989_);
v___x_2991_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
lean_object* v___x_2992_; 
v___x_2992_ = lean_array_uset(v_x_2968_, v___x_2988_, v___x_2991_);
v_x_2968_ = v___x_2992_;
v_x_2969_ = v_tail_2972_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4___redArg(lean_object* v_i_2996_, lean_object* v_source_2997_, lean_object* v_target_2998_){
_start:
{
lean_object* v___x_2999_; uint8_t v___x_3000_; 
v___x_2999_ = lean_array_get_size(v_source_2997_);
v___x_3000_ = lean_nat_dec_lt(v_i_2996_, v___x_2999_);
if (v___x_3000_ == 0)
{
lean_dec_ref(v_source_2997_);
lean_dec(v_i_2996_);
return v_target_2998_;
}
else
{
lean_object* v_es_3001_; lean_object* v___x_3002_; lean_object* v_source_3003_; lean_object* v_target_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_es_3001_ = lean_array_fget(v_source_2997_, v_i_2996_);
v___x_3002_ = lean_box(0);
v_source_3003_ = lean_array_fset(v_source_2997_, v_i_2996_, v___x_3002_);
v_target_3004_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(v_target_2998_, v_es_3001_);
v___x_3005_ = lean_unsigned_to_nat(1u);
v___x_3006_ = lean_nat_add(v_i_2996_, v___x_3005_);
lean_dec(v_i_2996_);
v_i_2996_ = v___x_3006_;
v_source_2997_ = v_source_3003_;
v_target_2998_ = v_target_3004_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2___redArg(lean_object* v_data_3008_){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v_nbuckets_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3009_ = lean_array_get_size(v_data_3008_);
v___x_3010_ = lean_unsigned_to_nat(2u);
v_nbuckets_3011_ = lean_nat_mul(v___x_3009_, v___x_3010_);
v___x_3012_ = lean_unsigned_to_nat(0u);
v___x_3013_ = lean_box(0);
v___x_3014_ = lean_mk_array(v_nbuckets_3011_, v___x_3013_);
v___x_3015_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4___redArg(v___x_3012_, v_data_3008_, v___x_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1___redArg(lean_object* v_m_3016_, lean_object* v_a_3017_, lean_object* v_b_3018_){
_start:
{
lean_object* v_size_3019_; lean_object* v_buckets_3020_; lean_object* v___x_3021_; uint64_t v___x_3022_; uint64_t v___x_3023_; uint64_t v___x_3024_; uint64_t v_fold_3025_; uint64_t v___x_3026_; uint64_t v___x_3027_; uint64_t v___x_3028_; size_t v___x_3029_; size_t v___x_3030_; size_t v___x_3031_; size_t v___x_3032_; size_t v___x_3033_; lean_object* v_bkt_3034_; uint8_t v___x_3035_; 
v_size_3019_ = lean_ctor_get(v_m_3016_, 0);
v_buckets_3020_ = lean_ctor_get(v_m_3016_, 1);
v___x_3021_ = lean_array_get_size(v_buckets_3020_);
v___x_3022_ = l_Lean_instHashableFVarId_hash(v_a_3017_);
v___x_3023_ = 32ULL;
v___x_3024_ = lean_uint64_shift_right(v___x_3022_, v___x_3023_);
v_fold_3025_ = lean_uint64_xor(v___x_3022_, v___x_3024_);
v___x_3026_ = 16ULL;
v___x_3027_ = lean_uint64_shift_right(v_fold_3025_, v___x_3026_);
v___x_3028_ = lean_uint64_xor(v_fold_3025_, v___x_3027_);
v___x_3029_ = lean_uint64_to_usize(v___x_3028_);
v___x_3030_ = lean_usize_of_nat(v___x_3021_);
v___x_3031_ = ((size_t)1ULL);
v___x_3032_ = lean_usize_sub(v___x_3030_, v___x_3031_);
v___x_3033_ = lean_usize_land(v___x_3029_, v___x_3032_);
v_bkt_3034_ = lean_array_uget_borrowed(v_buckets_3020_, v___x_3033_);
v___x_3035_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(v_a_3017_, v_bkt_3034_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3056_; 
lean_inc_ref(v_buckets_3020_);
lean_inc(v_size_3019_);
v_isSharedCheck_3056_ = !lean_is_exclusive(v_m_3016_);
if (v_isSharedCheck_3056_ == 0)
{
lean_object* v_unused_3057_; lean_object* v_unused_3058_; 
v_unused_3057_ = lean_ctor_get(v_m_3016_, 1);
lean_dec(v_unused_3057_);
v_unused_3058_ = lean_ctor_get(v_m_3016_, 0);
lean_dec(v_unused_3058_);
v___x_3037_ = v_m_3016_;
v_isShared_3038_ = v_isSharedCheck_3056_;
goto v_resetjp_3036_;
}
else
{
lean_dec(v_m_3016_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3056_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3039_; lean_object* v_size_x27_3040_; lean_object* v___x_3041_; lean_object* v_buckets_x27_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; uint8_t v___x_3048_; 
v___x_3039_ = lean_unsigned_to_nat(1u);
v_size_x27_3040_ = lean_nat_add(v_size_3019_, v___x_3039_);
lean_dec(v_size_3019_);
lean_inc(v_bkt_3034_);
v___x_3041_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3041_, 0, v_a_3017_);
lean_ctor_set(v___x_3041_, 1, v_b_3018_);
lean_ctor_set(v___x_3041_, 2, v_bkt_3034_);
v_buckets_x27_3042_ = lean_array_uset(v_buckets_3020_, v___x_3033_, v___x_3041_);
v___x_3043_ = lean_unsigned_to_nat(4u);
v___x_3044_ = lean_nat_mul(v_size_x27_3040_, v___x_3043_);
v___x_3045_ = lean_unsigned_to_nat(3u);
v___x_3046_ = lean_nat_div(v___x_3044_, v___x_3045_);
lean_dec(v___x_3044_);
v___x_3047_ = lean_array_get_size(v_buckets_x27_3042_);
v___x_3048_ = lean_nat_dec_le(v___x_3046_, v___x_3047_);
lean_dec(v___x_3046_);
if (v___x_3048_ == 0)
{
lean_object* v_val_3049_; lean_object* v___x_3051_; 
v_val_3049_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2___redArg(v_buckets_x27_3042_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 1, v_val_3049_);
lean_ctor_set(v___x_3037_, 0, v_size_x27_3040_);
v___x_3051_ = v___x_3037_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_size_x27_3040_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v_val_3049_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
else
{
lean_object* v___x_3054_; 
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 1, v_buckets_x27_3042_);
lean_ctor_set(v___x_3037_, 0, v_size_x27_3040_);
v___x_3054_ = v___x_3037_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_size_x27_3040_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_buckets_x27_3042_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
else
{
lean_dec(v_b_3018_);
lean_dec(v_a_3017_);
return v_m_3016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__1(lean_object* v___x_3059_, lean_object* v_a_3060_, lean_object* v_e_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v___x_3068_; lean_object* v_relevantTerms_3069_; lean_object* v_relevantHyps_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3092_; 
v___x_3068_ = lean_st_ref_take(v___y_3062_);
v_relevantTerms_3069_ = lean_ctor_get(v___x_3068_, 0);
v_relevantHyps_3070_ = lean_ctor_get(v___x_3068_, 1);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3072_ = v___x_3068_;
v_isShared_3073_ = v_isSharedCheck_3092_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_relevantHyps_3070_);
lean_inc(v_relevantTerms_3069_);
lean_dec(v___x_3068_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3092_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3074_; lean_object* v___x_3076_; 
v___x_3074_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__0___redArg(v_relevantTerms_3069_, v_e_3061_, v___x_3059_);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v___x_3074_);
v___x_3076_ = v___x_3072_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v___x_3074_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v_relevantHyps_3070_);
v___x_3076_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v_relevantTerms_3079_; lean_object* v_relevantHyps_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3090_; 
v___x_3077_ = lean_st_ref_set(v___y_3062_, v___x_3076_);
v___x_3078_ = lean_st_ref_take(v___y_3062_);
v_relevantTerms_3079_ = lean_ctor_get(v___x_3078_, 0);
v_relevantHyps_3080_ = lean_ctor_get(v___x_3078_, 1);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3082_ = v___x_3078_;
v_isShared_3083_ = v_isSharedCheck_3090_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_relevantHyps_3080_);
lean_inc(v_relevantTerms_3079_);
lean_dec(v___x_3078_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3090_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3084_; lean_object* v___x_3086_; 
v___x_3084_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1___redArg(v_relevantHyps_3080_, v_a_3060_, v___x_3059_);
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 1, v___x_3084_);
v___x_3086_ = v___x_3082_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_relevantTerms_3079_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v___x_3084_);
v___x_3086_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3087_ = lean_st_ref_set(v___y_3062_, v___x_3086_);
v___x_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3059_);
return v___x_3088_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__1___boxed(lean_object* v___x_3093_, lean_object* v_a_3094_, lean_object* v_e_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__1(v___x_3093_, v_a_3094_, v_e_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
return v_res_3102_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0(lean_object* v_e_3112_){
_start:
{
uint8_t v___y_3114_; lean_object* v___x_3117_; lean_object* v___x_3118_; uint8_t v___x_3119_; 
v___x_3117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2));
v___x_3118_ = lean_unsigned_to_nat(1u);
v___x_3119_ = l_Lean_Expr_isAppOfArity(v_e_3112_, v___x_3117_, v___x_3118_);
if (v___x_3119_ == 0)
{
lean_object* v___x_3120_; uint8_t v___x_3121_; 
v___x_3120_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4));
v___x_3121_ = l_Lean_Expr_isAppOfArity(v_e_3112_, v___x_3120_, v___x_3118_);
v___y_3114_ = v___x_3121_;
goto v___jp_3113_;
}
else
{
v___y_3114_ = v___x_3119_;
goto v___jp_3113_;
}
v___jp_3113_:
{
if (v___y_3114_ == 0)
{
return v___y_3114_;
}
else
{
uint8_t v___x_3115_; 
v___x_3115_ = l_Lean_Expr_hasLooseBVars(v_e_3112_);
if (v___x_3115_ == 0)
{
return v___y_3114_;
}
else
{
uint8_t v___x_3116_; 
v___x_3116_ = 0;
return v___x_3116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___boxed(lean_object* v_e_3122_){
_start:
{
uint8_t v_res_3123_; lean_object* v_r_3124_; 
v_res_3123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0(v_e_3122_);
lean_dec_ref(v_e_3122_);
v_r_3124_ = lean_box(v_res_3123_);
return v_r_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4(lean_object* v_as_3126_, size_t v_sz_3127_, size_t v_i_3128_, lean_object* v_b_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
uint8_t v___x_3136_; 
v___x_3136_ = lean_usize_dec_lt(v_i_3128_, v_sz_3127_);
if (v___x_3136_ == 0)
{
lean_object* v___x_3137_; 
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
v___x_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3137_, 0, v_b_3129_);
return v___x_3137_;
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3139_; 
v_a_3138_ = lean_array_uget_borrowed(v_as_3126_, v_i_3128_);
lean_inc_ref(v___y_3131_);
lean_inc(v_a_3138_);
v___x_3139_ = l_Lean_FVarId_getType___redArg(v_a_3138_, v___y_3131_, v___y_3133_, v___y_3134_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3141_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref(v___x_3139_);
v___x_3141_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___redArg(v_a_3140_, v___y_3132_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; lean_object* v___f_3143_; lean_object* v___x_3144_; lean_object* v___f_3145_; lean_object* v___x_3146_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_a_3142_);
lean_dec_ref(v___x_3141_);
v___f_3143_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___closed__0));
v___x_3144_ = lean_box(0);
lean_inc(v_a_3138_);
v___f_3145_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__1___boxed), 9, 2);
lean_closure_set(v___f_3145_, 0, v___x_3144_);
lean_closure_set(v___f_3145_, 1, v_a_3138_);
lean_inc(v___y_3134_);
lean_inc_ref(v___y_3133_);
lean_inc(v___y_3132_);
lean_inc_ref(v___y_3131_);
lean_inc(v___y_3130_);
v___x_3146_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3(v___f_3143_, v___f_3145_, v_a_3142_, v___x_3136_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
if (lean_obj_tag(v___x_3146_) == 0)
{
size_t v___x_3147_; size_t v___x_3148_; 
lean_dec_ref(v___x_3146_);
v___x_3147_ = ((size_t)1ULL);
v___x_3148_ = lean_usize_add(v_i_3128_, v___x_3147_);
v_i_3128_ = v___x_3148_;
v_b_3129_ = v___x_3144_;
goto _start;
}
else
{
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
return v___x_3146_;
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
v_a_3150_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3141_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3141_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
else
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
v_a_3158_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3139_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3139_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___boxed(lean_object* v_as_3166_, lean_object* v_sz_3167_, lean_object* v_i_3168_, lean_object* v_b_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
size_t v_sz_boxed_3176_; size_t v_i_boxed_3177_; lean_object* v_res_3178_; 
v_sz_boxed_3176_ = lean_unbox_usize(v_sz_3167_);
lean_dec(v_sz_3167_);
v_i_boxed_3177_ = lean_unbox_usize(v_i_3168_);
lean_dec(v_i_3168_);
v_res_3178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4(v_as_3166_, v_sz_boxed_3176_, v_i_boxed_3177_, v_b_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec_ref(v_as_3166_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___lam__0(lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v___x_3185_; 
lean_inc(v___y_3183_);
lean_inc_ref(v___y_3182_);
lean_inc(v___y_3181_);
lean_inc_ref(v___y_3180_);
v___x_3185_ = l_Lean_Meta_getPropHyps(v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; lean_object* v___x_3187_; size_t v_sz_3188_; size_t v___x_3189_; lean_object* v___x_3190_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
lean_inc(v_a_3186_);
lean_dec_ref(v___x_3185_);
v___x_3187_ = lean_box(0);
v_sz_3188_ = lean_array_size(v_a_3186_);
v___x_3189_ = ((size_t)0ULL);
lean_inc(v___y_3179_);
v___x_3190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4(v_a_3186_, v_sz_3188_, v___x_3189_, v___x_3187_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
lean_dec(v_a_3186_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3209_; 
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3209_ == 0)
{
lean_object* v_unused_3210_; 
v_unused_3210_ = lean_ctor_get(v___x_3190_, 0);
lean_dec(v_unused_3210_);
v___x_3192_ = v___x_3190_;
v_isShared_3193_ = v_isSharedCheck_3209_;
goto v_resetjp_3191_;
}
else
{
lean_dec(v___x_3190_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3209_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3194_; lean_object* v_relevantTerms_3195_; lean_object* v_size_3196_; lean_object* v___x_3197_; uint8_t v___x_3198_; 
v___x_3194_ = lean_st_ref_get(v___y_3179_);
lean_dec(v___y_3179_);
v_relevantTerms_3195_ = lean_ctor_get(v___x_3194_, 0);
lean_inc_ref(v_relevantTerms_3195_);
lean_dec(v___x_3194_);
v_size_3196_ = lean_ctor_get(v_relevantTerms_3195_, 0);
lean_inc(v_size_3196_);
lean_dec_ref(v_relevantTerms_3195_);
v___x_3197_ = lean_unsigned_to_nat(0u);
v___x_3198_ = lean_nat_dec_eq(v_size_3196_, v___x_3197_);
lean_dec(v_size_3196_);
if (v___x_3198_ == 0)
{
uint8_t v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3202_; 
v___x_3199_ = 1;
v___x_3200_ = lean_box(v___x_3199_);
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 0, v___x_3200_);
v___x_3202_ = v___x_3192_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3200_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
else
{
uint8_t v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3207_; 
v___x_3204_ = 0;
v___x_3205_ = lean_box(v___x_3204_);
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 0, v___x_3205_);
v___x_3207_ = v___x_3192_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3205_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_dec(v___y_3179_);
v_a_3211_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3190_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3190_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
v_a_3219_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3185_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3185_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___lam__0___boxed(lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___lam__0(v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize(lean_object* v_goal_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_){
_start:
{
lean_object* v___f_3242_; lean_object* v___x_3243_; 
v___f_3242_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___closed__0));
v___x_3243_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_goal_3235_, v___f_3242_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___boxed(lean_object* v_goal_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize(v_goal_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__0(lean_object* v_00_u03b2_3252_, lean_object* v_m_3253_, lean_object* v_a_3254_, lean_object* v_b_3255_){
_start:
{
lean_object* v___x_3256_; 
v___x_3256_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__0___redArg(v_m_3253_, v_a_3254_, v_b_3255_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1(lean_object* v_00_u03b2_3257_, lean_object* v_m_3258_, lean_object* v_a_3259_, lean_object* v_b_3260_){
_start:
{
lean_object* v___x_3261_; 
v___x_3261_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1___redArg(v_m_3258_, v_a_3259_, v_b_3260_);
return v___x_3261_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1(lean_object* v_00_u03b2_3262_, lean_object* v_a_3263_, lean_object* v_x_3264_){
_start:
{
uint8_t v___x_3265_; 
v___x_3265_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(v_a_3263_, v_x_3264_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3266_, lean_object* v_a_3267_, lean_object* v_x_3268_){
_start:
{
uint8_t v_res_3269_; lean_object* v_r_3270_; 
v_res_3269_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1(v_00_u03b2_3266_, v_a_3267_, v_x_3268_);
lean_dec(v_x_3268_);
lean_dec(v_a_3267_);
v_r_3270_ = lean_box(v_res_3269_);
return v_r_3270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2(lean_object* v_00_u03b2_3271_, lean_object* v_data_3272_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2___redArg(v_data_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7(lean_object* v_e_3274_, lean_object* v_a_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v___x_3282_; 
v___x_3282_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(v_e_3274_, v_a_3275_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___boxed(lean_object* v_e_3283_, lean_object* v_a_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7(v_e_3283_, v_a_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
lean_dec(v_a_3284_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3292_, lean_object* v_i_3293_, lean_object* v_source_3294_, lean_object* v_target_3295_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4___redArg(v_i_3293_, v_source_3294_, v_target_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8(lean_object* v_e_3297_, lean_object* v_a_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(v_e_3297_, v_a_3298_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___boxed(lean_object* v_e_3306_, lean_object* v_a_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8(v_e_3306_, v_a_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec(v_a_3307_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_3315_, lean_object* v_x_3316_, lean_object* v_x_3317_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(v_x_3316_, v_x_3317_);
return v___x_3318_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11(lean_object* v_00_u03b2_3319_, lean_object* v_m_3320_, lean_object* v_a_3321_){
_start:
{
uint8_t v___x_3322_; 
v___x_3322_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(v_m_3320_, v_a_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___boxed(lean_object* v_00_u03b2_3323_, lean_object* v_m_3324_, lean_object* v_a_3325_){
_start:
{
uint8_t v_res_3326_; lean_object* v_r_3327_; 
v_res_3326_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11(v_00_u03b2_3323_, v_m_3324_, v_a_3325_);
lean_dec_ref(v_a_3325_);
lean_dec_ref(v_m_3324_);
v_r_3327_ = lean_box(v_res_3326_);
return v_r_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_handleSize(lean_object* v_goal_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_){
_start:
{
lean_object* v___x_3335_; 
lean_inc(v_a_3333_);
lean_inc_ref(v_a_3332_);
lean_inc(v_a_3331_);
lean_inc_ref(v_a_3330_);
lean_inc(v_a_3329_);
lean_inc(v_goal_3328_);
v___x_3335_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize(v_goal_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3345_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3338_ = v___x_3335_;
v_isShared_3339_ = v_isSharedCheck_3345_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3335_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3345_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
uint8_t v___x_3340_; 
v___x_3340_ = lean_unbox(v_a_3336_);
lean_dec(v_a_3336_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3342_; 
lean_dec(v_a_3333_);
lean_dec_ref(v_a_3332_);
lean_dec(v_a_3331_);
lean_dec_ref(v_a_3330_);
lean_dec(v_a_3329_);
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 0, v_goal_3328_);
v___x_3342_ = v___x_3338_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_goal_3328_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
else
{
lean_object* v___x_3344_; 
lean_del_object(v___x_3338_);
v___x_3344_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize(v_goal_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_);
return v___x_3344_;
}
}
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
lean_dec(v_a_3333_);
lean_dec_ref(v_a_3332_);
lean_dec(v_a_3331_);
lean_dec_ref(v_a_3330_);
lean_dec(v_a_3329_);
lean_dec(v_goal_3328_);
v_a_3346_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3335_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3335_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_handleSize___boxed(lean_object* v_goal_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_){
_start:
{
lean_object* v_res_3361_; 
v_res_3361_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_handleSize(v_goal_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
return v_res_3361_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3364_; 
v___x_3364_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3364_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__1);
v___x_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
return v___x_3366_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3367_ = lean_unsigned_to_nat(0u);
v___x_3368_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2);
v___x_3369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
lean_ctor_set(v___x_3369_, 1, v___x_3367_);
return v___x_3369_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3370_ = lean_unsigned_to_nat(32u);
v___x_3371_ = lean_mk_empty_array_with_capacity(v___x_3370_);
v___x_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3371_);
return v___x_3372_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__5(void){
_start:
{
size_t v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3373_ = ((size_t)5ULL);
v___x_3374_ = lean_unsigned_to_nat(0u);
v___x_3375_ = lean_unsigned_to_nat(32u);
v___x_3376_ = lean_mk_empty_array_with_capacity(v___x_3375_);
v___x_3377_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__4);
v___x_3378_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
lean_ctor_set(v___x_3378_, 1, v___x_3376_);
lean_ctor_set(v___x_3378_, 2, v___x_3374_);
lean_ctor_set(v___x_3378_, 3, v___x_3374_);
lean_ctor_set_usize(v___x_3378_, 4, v___x_3373_);
return v___x_3378_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3379_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__5);
v___x_3380_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2);
v___x_3381_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3380_);
lean_ctor_set(v___x_3381_, 1, v___x_3380_);
lean_ctor_set(v___x_3381_, 2, v___x_3380_);
lean_ctor_set(v___x_3381_, 3, v___x_3379_);
return v___x_3381_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3382_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__6);
v___x_3383_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__3);
v___x_3384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3383_);
lean_ctor_set(v___x_3384_, 1, v___x_3382_);
return v___x_3384_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3385_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12);
v___x_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0(lean_object* v_goal_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = l_Lean_Elab_Tactic_BVDecide_Frontend_intToBitVecExt;
v___x_3396_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_3395_, v___y_3393_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; lean_object* v___x_3398_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_a_3397_);
lean_dec_ref(v___x_3396_);
v___x_3398_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_3393_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v_maxSteps_3400_; lean_object* v___x_3401_; uint8_t v___x_3402_; uint8_t v___x_3403_; uint8_t v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref(v___x_3398_);
v_maxSteps_3400_ = lean_ctor_get(v___y_3388_, 1);
v___x_3401_ = lean_unsigned_to_nat(2u);
v___x_3402_ = 0;
v___x_3403_ = 1;
v___x_3404_ = 0;
v___x_3405_ = lean_box(0);
lean_inc(v_maxSteps_3400_);
v___x_3406_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_3406_, 0, v_maxSteps_3400_);
lean_ctor_set(v___x_3406_, 1, v___x_3401_);
lean_ctor_set(v___x_3406_, 2, v___x_3405_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3, v___x_3402_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 1, v___x_3403_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 2, v___x_3402_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 3, v___x_3403_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 4, v___x_3403_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 5, v___x_3403_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 6, v___x_3404_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 7, v___x_3403_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 8, v___x_3403_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 9, v___x_3402_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 10, v___x_3402_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 11, v___x_3402_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 12, v___x_3403_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 13, v___x_3402_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 14, v___x_3402_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 15, v___x_3402_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 16, v___x_3403_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 17, v___x_3403_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 18, v___x_3402_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 19, v___x_3403_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 20, v___x_3403_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 21, v___x_3403_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 22, v___x_3403_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 23, v___x_3403_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 24, v___x_3403_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 25, v___x_3403_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 26, v___x_3402_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 27, v___x_3402_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*3 + 28, v___x_3403_);
v___x_3407_ = lean_unsigned_to_nat(1u);
v___x_3408_ = lean_mk_empty_array_with_capacity(v___x_3407_);
v___x_3409_ = lean_array_push(v___x_3408_, v_a_3397_);
v___x_3410_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_3406_, v___x_3409_, v_a_3399_, v___y_3390_, v___y_3392_, v___y_3393_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; lean_object* v___x_3412_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_a_3411_);
lean_dec_ref(v___x_3410_);
lean_inc(v___y_3393_);
lean_inc_ref(v___y_3392_);
lean_inc(v___y_3391_);
lean_inc_ref(v___y_3390_);
lean_inc(v_goal_3387_);
v___x_3412_ = l_Lean_MVarId_getNondepPropHyps(v_goal_3387_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_a_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_a_3413_);
lean_dec_ref(v___x_3412_);
v___x_3414_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__0));
v___x_3415_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__7);
lean_inc(v___y_3393_);
lean_inc_ref(v___y_3392_);
lean_inc(v___y_3391_);
lean_inc_ref(v___y_3390_);
v___x_3416_ = l_Lean_Meta_simpGoal(v_goal_3387_, v_a_3411_, v___x_3414_, v___x_3405_, v___x_3403_, v_a_3413_, v___x_3415_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3454_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3419_ = v___x_3416_;
v_isShared_3420_ = v_isSharedCheck_3454_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3416_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3454_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v_fst_3421_; 
v_fst_3421_ = lean_ctor_get(v_a_3417_, 0);
lean_inc(v_fst_3421_);
lean_dec(v_a_3417_);
if (lean_obj_tag(v_fst_3421_) == 1)
{
lean_object* v_val_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3450_; 
lean_del_object(v___x_3419_);
v_val_3422_ = lean_ctor_get(v_fst_3421_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v_fst_3421_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3424_ = v_fst_3421_;
v_isShared_3425_ = v_isSharedCheck_3450_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_val_3422_);
lean_dec(v_fst_3421_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3450_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v_snd_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v_snd_3426_ = lean_ctor_get(v_val_3422_, 1);
lean_inc(v_snd_3426_);
lean_dec(v_val_3422_);
v___x_3427_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__8);
v___x_3428_ = lean_st_mk_ref(v___x_3427_);
lean_inc(v___x_3428_);
v___x_3429_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_handleSize(v_snd_3426_, v___x_3428_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3441_; 
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3432_ = v___x_3429_;
v_isShared_3433_ = v_isSharedCheck_3441_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3429_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3441_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3434_; lean_object* v___x_3436_; 
v___x_3434_ = lean_st_ref_get(v___x_3428_);
lean_dec(v___x_3428_);
lean_dec(v___x_3434_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 0, v_a_3430_);
v___x_3436_ = v___x_3424_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3430_);
v___x_3436_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
lean_object* v___x_3438_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 0, v___x_3436_);
v___x_3438_ = v___x_3432_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3436_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
else
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3449_; 
lean_dec(v___x_3428_);
lean_del_object(v___x_3424_);
v_a_3442_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3444_ = v___x_3429_;
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3429_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3447_; 
if (v_isShared_3445_ == 0)
{
v___x_3447_ = v___x_3444_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3442_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
}
else
{
lean_object* v___x_3452_; 
lean_dec(v_fst_3421_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v___x_3405_);
v___x_3452_ = v___x_3419_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3405_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
else
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
v_a_3455_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3416_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3416_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3455_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
lean_dec(v_a_3411_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v_goal_3387_);
v_a_3463_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3412_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3412_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v_goal_3387_);
v_a_3471_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3410_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3410_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_dec(v_a_3397_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v_goal_3387_);
v_a_3479_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3398_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3398_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
else
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3494_; 
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v_goal_3387_);
v_a_3487_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___x_3396_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3396_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___boxed(lean_object* v_goal_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0(v_goal_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
return v_res_3503_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec(builtin);
}
#ifdef __cplusplus
}
#endif
