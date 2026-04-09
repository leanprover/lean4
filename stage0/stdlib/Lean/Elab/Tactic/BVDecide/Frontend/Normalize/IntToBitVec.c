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
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3(lean_object*, lean_object*, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
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
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
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
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v_b_239_);
return v___x_246_;
}
else
{
lean_object* v_a_247_; lean_object* v___x_248_; 
lean_dec_ref(v_b_239_);
v_a_247_ = lean_array_uget_borrowed(v_as_236_, v_i_238_);
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
lean_inc_ref(v_a_255_);
v_i_238_ = v___x_257_;
v_b_239_ = v_a_255_;
goto _start;
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
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
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec_ref(v_as_368_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___lam__0(lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; 
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
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
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
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0(lean_object* v_x_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v___x_450_; 
lean_inc(v___y_444_);
v___x_450_ = lean_apply_6(v_x_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, lean_box(0));
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0___boxed(lean_object* v_x_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0(v_x_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_452_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(lean_object* v_mvarId_459_, lean_object* v_x_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___f_467_; lean_object* v___x_468_; 
lean_inc(v___y_461_);
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
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
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
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
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
size_t v___x_21195__boxed_781_; uint8_t v___x_21197__boxed_782_; lean_object* v_res_783_; 
v___x_21195__boxed_781_ = lean_unbox_usize(v___x_771_);
lean_dec(v___x_771_);
v___x_21197__boxed_782_ = lean_unbox(v___x_773_);
v_res_783_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__1(v___x_767_, v___x_768_, v_z_769_, v___y_770_, v___x_21195__boxed_781_, v_a_772_, v___x_21197__boxed_782_, v_args_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___lam__0(lean_object* v___x_852_, lean_object* v_a_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; lean_object* v___x_20783__overap_861_; lean_object* v___x_862_; 
v___x_860_ = l_Lean_instInhabitedExpr;
v___x_20783__overap_861_ = l_instInhabitedOfMonad___redArg(v___x_852_, v___x_860_);
lean_inc(v___y_858_);
lean_inc_ref(v___y_857_);
lean_inc(v___y_856_);
lean_inc_ref(v___y_855_);
lean_inc(v___y_854_);
v___x_862_ = lean_apply_6(v___x_20783__overap_861_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, lean_box(0));
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___lam__0___boxed(lean_object* v___x_863_, lean_object* v_a_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___lam__0(v___x_863_, v_a_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v_a_864_);
return v_res_871_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0(void){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_instMonadEIO(lean_box(0));
return v___x_872_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0);
v___x_874_ = l_StateRefT_x27_instMonad___redArg(v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___lam__0___boxed(lean_object* v_acc_879_, lean_object* v_declInfos_880_, lean_object* v_k_881_, lean_object* v_kind_882_, lean_object* v___y_883_, lean_object* v_b_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
uint8_t v_kind_boxed_890_; lean_object* v_res_891_; 
v_kind_boxed_890_ = lean_unbox(v_kind_882_);
v_res_891_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___lam__0(v_acc_879_, v_declInfos_880_, v_k_881_, v_kind_boxed_890_, v___y_883_, v_b_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_883_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34(lean_object* v_acc_892_, lean_object* v_declInfos_893_, lean_object* v_k_894_, uint8_t v_kind_895_, lean_object* v_name_896_, uint8_t v_bi_897_, lean_object* v_type_898_, uint8_t v_kind_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_906_; lean_object* v___f_907_; lean_object* v___x_908_; 
v___x_906_ = lean_box(v_kind_895_);
lean_inc(v___y_900_);
v___f_907_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___lam__0___boxed), 11, 5);
lean_closure_set(v___f_907_, 0, v_acc_892_);
lean_closure_set(v___f_907_, 1, v_declInfos_893_);
lean_closure_set(v___f_907_, 2, v_k_894_);
lean_closure_set(v___f_907_, 3, v___x_906_);
lean_closure_set(v___f_907_, 4, v___y_900_);
v___x_908_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_896_, v_bi_897_, v_type_898_, v___f_907_, v_kind_899_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
if (lean_obj_tag(v___x_908_) == 0)
{
return v___x_908_;
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(lean_object* v_declInfos_917_, lean_object* v_k_918_, uint8_t v_kind_919_, lean_object* v_acc_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; lean_object* v_toApplicative_928_; lean_object* v_toFunctor_929_; lean_object* v_toSeq_930_; lean_object* v_toSeqLeft_931_; lean_object* v_toSeqRight_932_; lean_object* v___f_933_; lean_object* v___f_934_; lean_object* v___f_935_; lean_object* v___f_936_; lean_object* v___x_937_; lean_object* v___f_938_; lean_object* v___f_939_; lean_object* v___f_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v_toApplicative_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_992_; 
v___x_927_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1);
v_toApplicative_928_ = lean_ctor_get(v___x_927_, 0);
v_toFunctor_929_ = lean_ctor_get(v_toApplicative_928_, 0);
v_toSeq_930_ = lean_ctor_get(v_toApplicative_928_, 2);
v_toSeqLeft_931_ = lean_ctor_get(v_toApplicative_928_, 3);
v_toSeqRight_932_ = lean_ctor_get(v_toApplicative_928_, 4);
v___f_933_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__2));
v___f_934_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__3));
lean_inc_ref_n(v_toFunctor_929_, 2);
v___f_935_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_935_, 0, v_toFunctor_929_);
v___f_936_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_936_, 0, v_toFunctor_929_);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v___f_935_);
lean_ctor_set(v___x_937_, 1, v___f_936_);
lean_inc(v_toSeqRight_932_);
v___f_938_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_938_, 0, v_toSeqRight_932_);
lean_inc(v_toSeqLeft_931_);
v___f_939_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_939_, 0, v_toSeqLeft_931_);
lean_inc(v_toSeq_930_);
v___f_940_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_940_, 0, v_toSeq_930_);
v___x_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_941_, 0, v___x_937_);
lean_ctor_set(v___x_941_, 1, v___f_933_);
lean_ctor_set(v___x_941_, 2, v___f_940_);
lean_ctor_set(v___x_941_, 3, v___f_939_);
lean_ctor_set(v___x_941_, 4, v___f_938_);
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v___f_934_);
v___x_943_ = l_StateRefT_x27_instMonad___redArg(v___x_942_);
v_toApplicative_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_992_ == 0)
{
lean_object* v_unused_993_; 
v_unused_993_ = lean_ctor_get(v___x_943_, 1);
lean_dec(v_unused_993_);
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_992_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_toApplicative_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_992_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v_toFunctor_948_; lean_object* v_toSeq_949_; lean_object* v_toSeqLeft_950_; lean_object* v_toSeqRight_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_990_; 
v_toFunctor_948_ = lean_ctor_get(v_toApplicative_944_, 0);
v_toSeq_949_ = lean_ctor_get(v_toApplicative_944_, 2);
v_toSeqLeft_950_ = lean_ctor_get(v_toApplicative_944_, 3);
v_toSeqRight_951_ = lean_ctor_get(v_toApplicative_944_, 4);
v_isSharedCheck_990_ = !lean_is_exclusive(v_toApplicative_944_);
if (v_isSharedCheck_990_ == 0)
{
lean_object* v_unused_991_; 
v_unused_991_ = lean_ctor_get(v_toApplicative_944_, 1);
lean_dec(v_unused_991_);
v___x_953_ = v_toApplicative_944_;
v_isShared_954_ = v_isSharedCheck_990_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_toSeqRight_951_);
lean_inc(v_toSeqLeft_950_);
lean_inc(v_toSeq_949_);
lean_inc(v_toFunctor_948_);
lean_dec(v_toApplicative_944_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_990_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___f_955_; lean_object* v___f_956_; lean_object* v___f_957_; lean_object* v___f_958_; lean_object* v___x_959_; lean_object* v___f_960_; lean_object* v___f_961_; lean_object* v___f_962_; lean_object* v___x_964_; 
v___f_955_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__4));
v___f_956_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__5));
lean_inc_ref(v_toFunctor_948_);
v___f_957_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_957_, 0, v_toFunctor_948_);
v___f_958_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_958_, 0, v_toFunctor_948_);
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v___f_957_);
lean_ctor_set(v___x_959_, 1, v___f_958_);
v___f_960_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_960_, 0, v_toSeqRight_951_);
v___f_961_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_961_, 0, v_toSeqLeft_950_);
v___f_962_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_962_, 0, v_toSeq_949_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 4, v___f_960_);
lean_ctor_set(v___x_953_, 3, v___f_961_);
lean_ctor_set(v___x_953_, 2, v___f_962_);
lean_ctor_set(v___x_953_, 1, v___f_955_);
lean_ctor_set(v___x_953_, 0, v___x_959_);
v___x_964_ = v___x_953_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v___f_955_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v___f_962_);
lean_ctor_set(v_reuseFailAlloc_989_, 3, v___f_961_);
lean_ctor_set(v_reuseFailAlloc_989_, 4, v___f_960_);
v___x_964_ = v_reuseFailAlloc_989_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_966_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 1, v___f_956_);
lean_ctor_set(v___x_946_, 0, v___x_964_);
v___x_966_ = v___x_946_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v___f_956_);
v___x_966_ = v_reuseFailAlloc_988_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_967_ = l_StateRefT_x27_instMonad___redArg(v___x_966_);
v___x_968_ = lean_array_get_size(v_acc_920_);
v___x_969_ = lean_array_get_size(v_declInfos_917_);
v___x_970_ = lean_nat_dec_lt(v___x_968_, v___x_969_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; 
lean_dec_ref(v___x_967_);
lean_dec_ref(v_declInfos_917_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc_ref(v___y_922_);
lean_inc(v___y_921_);
v___x_971_ = lean_apply_7(v_k_918_, v_acc_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, lean_box(0));
return v___x_971_;
}
else
{
lean_object* v___f_972_; lean_object* v___x_973_; uint8_t v___x_974_; lean_object* v___f_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v_snd_980_; lean_object* v_fst_981_; lean_object* v_fst_982_; lean_object* v_snd_983_; lean_object* v___x_984_; 
v___f_972_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___lam__0___boxed), 8, 1);
lean_closure_set(v___f_972_, 0, v___x_967_);
v___x_973_ = lean_box(0);
v___x_974_ = 0;
v___f_975_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_975_, 0, v___f_972_);
v___x_976_ = lean_box(v___x_974_);
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v___f_975_);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_973_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = lean_array_get(v___x_978_, v_declInfos_917_, v___x_968_);
lean_dec_ref(v___x_978_);
v_snd_980_ = lean_ctor_get(v___x_979_, 1);
lean_inc(v_snd_980_);
v_fst_981_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_fst_981_);
lean_dec(v___x_979_);
v_fst_982_ = lean_ctor_get(v_snd_980_, 0);
lean_inc(v_fst_982_);
v_snd_983_ = lean_ctor_get(v_snd_980_, 1);
lean_inc(v_snd_983_);
lean_dec(v_snd_980_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc_ref(v___y_922_);
lean_inc(v___y_921_);
lean_inc_ref(v_acc_920_);
v___x_984_ = lean_apply_7(v_snd_983_, v_acc_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, lean_box(0));
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; uint8_t v___x_986_; lean_object* v___x_987_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref(v___x_984_);
v___x_986_ = lean_unbox(v_fst_982_);
lean_dec(v_fst_982_);
v___x_987_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34(v_acc_920_, v_declInfos_917_, v_k_918_, v_kind_919_, v_fst_981_, v___x_986_, v_a_985_, v_kind_919_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
return v___x_987_;
}
else
{
lean_dec(v_fst_982_);
lean_dec(v_fst_981_);
lean_dec_ref(v_acc_920_);
lean_dec_ref(v_k_918_);
lean_dec_ref(v_declInfos_917_);
return v___x_984_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___lam__0(lean_object* v_acc_994_, lean_object* v_declInfos_995_, lean_object* v_k_996_, uint8_t v_kind_997_, lean_object* v___y_998_, lean_object* v_b_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_array_push(v_acc_994_, v_b_999_);
v___x_1006_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(v_declInfos_995_, v_k_996_, v_kind_997_, v___x_1005_, v___y_998_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___boxed(lean_object* v_acc_1007_, lean_object* v_declInfos_1008_, lean_object* v_k_1009_, lean_object* v_kind_1010_, lean_object* v_name_1011_, lean_object* v_bi_1012_, lean_object* v_type_1013_, lean_object* v_kind_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
uint8_t v_kind_boxed_1021_; uint8_t v_bi_boxed_1022_; uint8_t v_kind_boxed_1023_; lean_object* v_res_1024_; 
v_kind_boxed_1021_ = lean_unbox(v_kind_1010_);
v_bi_boxed_1022_ = lean_unbox(v_bi_1012_);
v_kind_boxed_1023_ = lean_unbox(v_kind_1014_);
v_res_1024_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34(v_acc_1007_, v_declInfos_1008_, v_k_1009_, v_kind_boxed_1021_, v_name_1011_, v_bi_boxed_1022_, v_type_1013_, v_kind_boxed_1023_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___boxed(lean_object* v_declInfos_1025_, lean_object* v_k_1026_, lean_object* v_kind_1027_, lean_object* v_acc_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
uint8_t v_kind_boxed_1035_; lean_object* v_res_1036_; 
v_kind_boxed_1035_ = lean_unbox(v_kind_1027_);
v_res_1036_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(v_declInfos_1025_, v_k_1026_, v_kind_boxed_1035_, v_acc_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14(lean_object* v_declInfos_1039_, lean_object* v_k_1040_, uint8_t v_kind_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___closed__0));
v___x_1049_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(v_declInfos_1039_, v_k_1040_, v_kind_1041_, v___x_1048_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___boxed(lean_object* v_declInfos_1050_, lean_object* v_k_1051_, lean_object* v_kind_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
uint8_t v_kind_boxed_1059_; lean_object* v_res_1060_; 
v_kind_boxed_1059_ = lean_unbox(v_kind_1052_);
v_res_1060_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14(v_declInfos_1050_, v_k_1051_, v_kind_boxed_1059_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(size_t v_sz_1061_, size_t v_i_1062_, lean_object* v_bs_1063_){
_start:
{
uint8_t v___x_1064_; 
v___x_1064_ = lean_usize_dec_lt(v_i_1062_, v_sz_1061_);
if (v___x_1064_ == 0)
{
return v_bs_1063_;
}
else
{
lean_object* v_v_1065_; lean_object* v_fst_1066_; lean_object* v_snd_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1083_; 
v_v_1065_ = lean_array_uget(v_bs_1063_, v_i_1062_);
v_fst_1066_ = lean_ctor_get(v_v_1065_, 0);
v_snd_1067_ = lean_ctor_get(v_v_1065_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_v_1065_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1069_ = v_v_1065_;
v_isShared_1070_ = v_isSharedCheck_1083_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_snd_1067_);
lean_inc(v_fst_1066_);
lean_dec(v_v_1065_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1083_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; lean_object* v_bs_x27_1072_; uint8_t v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1071_ = lean_unsigned_to_nat(0u);
v_bs_x27_1072_ = lean_array_uset(v_bs_1063_, v_i_1062_, v___x_1071_);
v___x_1073_ = 0;
v___x_1074_ = lean_box(v___x_1073_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1074_);
v___x_1076_ = v___x_1069_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_snd_1067_);
v___x_1076_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1077_; size_t v___x_1078_; size_t v___x_1079_; lean_object* v___x_1080_; 
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_fst_1066_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = ((size_t)1ULL);
v___x_1079_ = lean_usize_add(v_i_1062_, v___x_1078_);
v___x_1080_ = lean_array_uset(v_bs_x27_1072_, v_i_1062_, v___x_1077_);
v_i_1062_ = v___x_1079_;
v_bs_1063_ = v___x_1080_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13___boxed(lean_object* v_sz_1084_, lean_object* v_i_1085_, lean_object* v_bs_1086_){
_start:
{
size_t v_sz_boxed_1087_; size_t v_i_boxed_1088_; lean_object* v_res_1089_; 
v_sz_boxed_1087_ = lean_unbox_usize(v_sz_1084_);
lean_dec(v_sz_1084_);
v_i_boxed_1088_ = lean_unbox_usize(v_i_1085_);
lean_dec(v_i_1085_);
v_res_1089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(v_sz_boxed_1087_, v_i_boxed_1088_, v_bs_1086_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10(lean_object* v_declInfos_1090_, lean_object* v_k_1091_, uint8_t v_kind_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
size_t v_sz_1099_; size_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_sz_1099_ = lean_array_size(v_declInfos_1090_);
v___x_1100_ = ((size_t)0ULL);
v___x_1101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(v_sz_1099_, v___x_1100_, v_declInfos_1090_);
v___x_1102_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14(v___x_1101_, v_k_1091_, v_kind_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___boxed(lean_object* v_declInfos_1103_, lean_object* v_k_1104_, lean_object* v_kind_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
uint8_t v_kind_boxed_1112_; lean_object* v_res_1113_; 
v_kind_boxed_1112_ = lean_unbox(v_kind_1105_);
v_res_1113_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10(v_declInfos_1103_, v_k_1104_, v_kind_boxed_1112_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5(lean_object* v_declInfos_1114_, lean_object* v_k_1115_, uint8_t v_kind_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
size_t v_sz_1123_; size_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v_sz_1123_ = lean_array_size(v_declInfos_1114_);
v___x_1124_ = ((size_t)0ULL);
v___x_1125_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9(v_sz_1123_, v___x_1124_, v_declInfos_1114_);
v___x_1126_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10(v___x_1125_, v_k_1115_, v_kind_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5___boxed(lean_object* v_declInfos_1127_, lean_object* v_k_1128_, lean_object* v_kind_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
uint8_t v_kind_boxed_1136_; lean_object* v_res_1137_; 
v_kind_boxed_1136_ = lean_unbox(v_kind_1129_);
v_res_1137_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5(v_declInfos_1127_, v_k_1128_, v_kind_boxed_1136_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2(lean_object* v___x_1141_, lean_object* v_z_1142_, lean_object* v___y_1143_, size_t v___x_1144_, lean_object* v___f_1145_, lean_object* v___x_1146_, uint8_t v___x_1147_, lean_object* v_other_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; size_t v_sz_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; lean_object* v___x_1161_; 
v___x_1155_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1));
v___x_1156_ = l_Lean_mkConst(v___x_1155_, v___x_1141_);
lean_inc_ref(v_z_1142_);
v___x_1157_ = l_Lean_Expr_app___override(v___x_1156_, v_z_1142_);
v_sz_1158_ = lean_array_size(v___y_1143_);
v___x_1159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4(v___x_1157_, v_sz_1158_, v___x_1144_, v___y_1143_);
v___x_1160_ = 0;
v___x_1161_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5(v___x_1159_, v___f_1145_, v___x_1160_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; uint8_t v___x_1169_; lean_object* v___x_1170_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref(v___x_1161_);
lean_inc_ref(v_z_1142_);
v___x_1163_ = l_Lean_Expr_replaceFVar(v_a_1162_, v_z_1142_, v___x_1146_);
v___x_1164_ = lean_unsigned_to_nat(2u);
v___x_1165_ = lean_mk_empty_array_with_capacity(v___x_1164_);
v___x_1166_ = lean_array_push(v___x_1165_, v_z_1142_);
v___x_1167_ = lean_array_push(v___x_1166_, v_other_1148_);
v___x_1168_ = 0;
v___x_1169_ = 1;
v___x_1170_ = l_Lean_Meta_mkLambdaFVars(v___x_1167_, v_a_1162_, v___x_1168_, v___x_1147_, v___x_1168_, v___x_1147_, v___x_1169_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec_ref(v___x_1167_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1179_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1179_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1179_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v_a_1171_);
lean_ctor_set(v___x_1175_, 1, v___x_1163_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v___x_1175_);
v___x_1177_ = v___x_1173_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec_ref(v___x_1163_);
v_a_1180_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1170_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1170_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec_ref(v_other_1148_);
lean_dec_ref(v_z_1142_);
v_a_1188_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1161_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1161_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___boxed(lean_object* v___x_1196_, lean_object* v_z_1197_, lean_object* v___y_1198_, lean_object* v___x_1199_, lean_object* v___f_1200_, lean_object* v___x_1201_, lean_object* v___x_1202_, lean_object* v_other_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
size_t v___x_21741__boxed_1210_; uint8_t v___x_21744__boxed_1211_; lean_object* v_res_1212_; 
v___x_21741__boxed_1210_ = lean_unbox_usize(v___x_1199_);
lean_dec(v___x_1199_);
v___x_21744__boxed_1211_ = lean_unbox(v___x_1202_);
v_res_1212_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2(v___x_1196_, v_z_1197_, v___y_1198_, v___x_21741__boxed_1210_, v___f_1200_, v___x_1201_, v___x_21744__boxed_1211_, v_other_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___x_1201_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0(lean_object* v_k_1213_, lean_object* v___y_1214_, lean_object* v_b_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v___x_1221_; 
lean_inc(v___y_1219_);
lean_inc_ref(v___y_1218_);
lean_inc(v___y_1217_);
lean_inc_ref(v___y_1216_);
lean_inc(v___y_1214_);
v___x_1221_ = lean_apply_7(v_k_1213_, v_b_1215_, v___y_1214_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, lean_box(0));
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0___boxed(lean_object* v_k_1222_, lean_object* v___y_1223_, lean_object* v_b_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0(v_k_1222_, v___y_1223_, v_b_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1223_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(lean_object* v_name_1231_, uint8_t v_bi_1232_, lean_object* v_type_1233_, lean_object* v_k_1234_, uint8_t v_kind_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___f_1242_; lean_object* v___x_1243_; 
lean_inc(v___y_1236_);
v___f_1242_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1242_, 0, v_k_1234_);
lean_closure_set(v___f_1242_, 1, v___y_1236_);
v___x_1243_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1231_, v_bi_1232_, v_type_1233_, v___f_1242_, v_kind_1235_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1243_) == 0)
{
return v___x_1243_;
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___boxed(lean_object* v_name_1252_, lean_object* v_bi_1253_, lean_object* v_type_1254_, lean_object* v_k_1255_, lean_object* v_kind_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
uint8_t v_bi_boxed_1263_; uint8_t v_kind_boxed_1264_; lean_object* v_res_1265_; 
v_bi_boxed_1263_ = lean_unbox(v_bi_1253_);
v_kind_boxed_1264_ = lean_unbox(v_kind_1256_);
v_res_1265_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(v_name_1252_, v_bi_boxed_1263_, v_type_1254_, v_k_1255_, v_kind_boxed_1264_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(lean_object* v_name_1266_, lean_object* v_type_1267_, lean_object* v_k_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
uint8_t v___x_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; 
v___x_1275_ = 0;
v___x_1276_ = 0;
v___x_1277_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(v_name_1266_, v___x_1275_, v_type_1267_, v_k_1268_, v___x_1276_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg___boxed(lean_object* v_name_1278_, lean_object* v_type_1279_, lean_object* v_k_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v_name_1278_, v_type_1279_, v_k_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3(lean_object* v___x_1291_, lean_object* v___y_1292_, size_t v___x_1293_, lean_object* v_a_1294_, uint8_t v___x_1295_, lean_object* v_fst_1296_, lean_object* v___x_1297_, lean_object* v_z_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___f_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___f_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1305_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2));
v___x_1306_ = lean_unsigned_to_nat(1u);
v___x_1307_ = lean_box_usize(v___x_1293_);
v___x_1308_ = lean_box(v___x_1295_);
lean_inc_ref(v___y_1292_);
lean_inc_ref_n(v_z_1298_, 2);
lean_inc_n(v___x_1291_, 2);
v___f_1309_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1309_, 0, v___x_1306_);
lean_closure_set(v___f_1309_, 1, v___x_1291_);
lean_closure_set(v___f_1309_, 2, v_z_1298_);
lean_closure_set(v___f_1309_, 3, v___y_1292_);
lean_closure_set(v___f_1309_, 4, v___x_1307_);
lean_closure_set(v___f_1309_, 5, v_a_1294_);
lean_closure_set(v___f_1309_, 6, v___x_1308_);
v___x_1310_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11);
v___x_1311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v___x_1291_);
v___x_1312_ = l_Lean_mkConst(v___x_1305_, v___x_1311_);
v___x_1313_ = l_Lean_mkNatLit(v_fst_1296_);
v___x_1314_ = lean_box_usize(v___x_1293_);
v___x_1315_ = lean_box(v___x_1295_);
lean_inc_ref(v___x_1313_);
v___f_1316_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___boxed), 14, 7);
lean_closure_set(v___f_1316_, 0, v___x_1291_);
lean_closure_set(v___f_1316_, 1, v_z_1298_);
lean_closure_set(v___f_1316_, 2, v___y_1292_);
lean_closure_set(v___f_1316_, 3, v___x_1314_);
lean_closure_set(v___f_1316_, 4, v___f_1309_);
lean_closure_set(v___f_1316_, 5, v___x_1313_);
lean_closure_set(v___f_1316_, 6, v___x_1315_);
v___x_1317_ = l_Lean_mkApp3(v___x_1312_, v___x_1297_, v___x_1313_, v_z_1298_);
v___x_1318_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1));
v___x_1319_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v___x_1318_, v___x_1317_, v___f_1316_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___boxed(lean_object* v___x_1320_, lean_object* v___y_1321_, lean_object* v___x_1322_, lean_object* v_a_1323_, lean_object* v___x_1324_, lean_object* v_fst_1325_, lean_object* v___x_1326_, lean_object* v_z_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
size_t v___x_21954__boxed_1334_; uint8_t v___x_21956__boxed_1335_; lean_object* v_res_1336_; 
v___x_21954__boxed_1334_ = lean_unbox_usize(v___x_1322_);
lean_dec(v___x_1322_);
v___x_21956__boxed_1335_ = lean_unbox(v___x_1324_);
v_res_1336_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3(v___x_1320_, v___y_1321_, v___x_21954__boxed_1334_, v_a_1323_, v___x_21956__boxed_1335_, v_fst_1325_, v___x_1326_, v_z_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__10(lean_object* v_x_1337_, lean_object* v_x_1338_){
_start:
{
if (lean_obj_tag(v_x_1338_) == 0)
{
return v_x_1337_;
}
else
{
lean_object* v_key_1339_; lean_object* v_tail_1340_; lean_object* v___x_1341_; 
v_key_1339_ = lean_ctor_get(v_x_1338_, 0);
lean_inc(v_key_1339_);
v_tail_1340_ = lean_ctor_get(v_x_1338_, 2);
lean_inc(v_tail_1340_);
lean_dec_ref(v_x_1338_);
v___x_1341_ = lean_array_push(v_x_1337_, v_key_1339_);
v_x_1337_ = v___x_1341_;
v_x_1338_ = v_tail_1340_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__11(lean_object* v_as_1343_, size_t v_i_1344_, size_t v_stop_1345_, lean_object* v_b_1346_){
_start:
{
uint8_t v___x_1347_; 
v___x_1347_ = lean_usize_dec_eq(v_i_1344_, v_stop_1345_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; size_t v___x_1350_; size_t v___x_1351_; 
v___x_1348_ = lean_array_uget_borrowed(v_as_1343_, v_i_1344_);
lean_inc(v___x_1348_);
v___x_1349_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__10(v_b_1346_, v___x_1348_);
v___x_1350_ = ((size_t)1ULL);
v___x_1351_ = lean_usize_add(v_i_1344_, v___x_1350_);
v_i_1344_ = v___x_1351_;
v_b_1346_ = v___x_1349_;
goto _start;
}
else
{
return v_b_1346_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__11___boxed(lean_object* v_as_1353_, lean_object* v_i_1354_, lean_object* v_stop_1355_, lean_object* v_b_1356_){
_start:
{
size_t v_i_boxed_1357_; size_t v_stop_boxed_1358_; lean_object* v_res_1359_; 
v_i_boxed_1357_ = lean_unbox_usize(v_i_1354_);
lean_dec(v_i_1354_);
v_stop_boxed_1358_ = lean_unbox_usize(v_stop_1355_);
lean_dec(v_stop_1355_);
v_res_1359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__11(v_as_1353_, v_i_boxed_1357_, v_stop_boxed_1358_, v_b_1356_);
lean_dec_ref(v_as_1353_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__8(size_t v_sz_1360_, size_t v_i_1361_, lean_object* v_bs_1362_){
_start:
{
uint8_t v___x_1363_; 
v___x_1363_ = lean_usize_dec_lt(v_i_1361_, v_sz_1360_);
if (v___x_1363_ == 0)
{
return v_bs_1362_;
}
else
{
lean_object* v_v_1364_; lean_object* v___x_1365_; lean_object* v_bs_x27_1366_; lean_object* v___x_1367_; size_t v___x_1368_; size_t v___x_1369_; lean_object* v___x_1370_; 
v_v_1364_ = lean_array_uget(v_bs_1362_, v_i_1361_);
v___x_1365_ = lean_unsigned_to_nat(0u);
v_bs_x27_1366_ = lean_array_uset(v_bs_1362_, v_i_1361_, v___x_1365_);
v___x_1367_ = l_Lean_Expr_fvarId_x21(v_v_1364_);
lean_dec(v_v_1364_);
v___x_1368_ = ((size_t)1ULL);
v___x_1369_ = lean_usize_add(v_i_1361_, v___x_1368_);
v___x_1370_ = lean_array_uset(v_bs_x27_1366_, v_i_1361_, v___x_1367_);
v_i_1361_ = v___x_1369_;
v_bs_1362_ = v___x_1370_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__8___boxed(lean_object* v_sz_1372_, lean_object* v_i_1373_, lean_object* v_bs_1374_){
_start:
{
size_t v_sz_boxed_1375_; size_t v_i_boxed_1376_; lean_object* v_res_1377_; 
v_sz_boxed_1375_ = lean_unbox_usize(v_sz_1372_);
lean_dec(v_sz_1372_);
v_i_boxed_1376_ = lean_unbox_usize(v_i_1373_);
lean_dec(v_i_1373_);
v_res_1377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__8(v_sz_boxed_1375_, v_i_boxed_1376_, v_bs_1374_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__12(lean_object* v_x_1378_, lean_object* v_x_1379_){
_start:
{
if (lean_obj_tag(v_x_1379_) == 0)
{
return v_x_1378_;
}
else
{
lean_object* v_key_1380_; lean_object* v_tail_1381_; lean_object* v___x_1382_; 
v_key_1380_ = lean_ctor_get(v_x_1379_, 0);
lean_inc(v_key_1380_);
v_tail_1381_ = lean_ctor_get(v_x_1379_, 2);
lean_inc(v_tail_1381_);
lean_dec_ref(v_x_1379_);
v___x_1382_ = lean_array_push(v_x_1378_, v_key_1380_);
v_x_1378_ = v___x_1382_;
v_x_1379_ = v_tail_1381_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__13(lean_object* v_as_1384_, size_t v_i_1385_, size_t v_stop_1386_, lean_object* v_b_1387_){
_start:
{
uint8_t v___x_1388_; 
v___x_1388_ = lean_usize_dec_eq(v_i_1385_, v_stop_1386_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1390_; size_t v___x_1391_; size_t v___x_1392_; 
v___x_1389_ = lean_array_uget_borrowed(v_as_1384_, v_i_1385_);
lean_inc(v___x_1389_);
v___x_1390_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__12(v_b_1387_, v___x_1389_);
v___x_1391_ = ((size_t)1ULL);
v___x_1392_ = lean_usize_add(v_i_1385_, v___x_1391_);
v_i_1385_ = v___x_1392_;
v_b_1387_ = v___x_1390_;
goto _start;
}
else
{
return v_b_1387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__13___boxed(lean_object* v_as_1394_, lean_object* v_i_1395_, lean_object* v_stop_1396_, lean_object* v_b_1397_){
_start:
{
size_t v_i_boxed_1398_; size_t v_stop_boxed_1399_; lean_object* v_res_1400_; 
v_i_boxed_1398_ = lean_unbox_usize(v_i_1395_);
lean_dec(v_i_1395_);
v_stop_boxed_1399_ = lean_unbox_usize(v_stop_1396_);
lean_dec(v_stop_1396_);
v_res_1400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__13(v_as_1394_, v_i_boxed_1398_, v_stop_boxed_1399_, v_b_1397_);
lean_dec_ref(v_as_1394_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32___redArg(lean_object* v_x_1401_, lean_object* v_x_1402_, lean_object* v_x_1403_, lean_object* v_x_1404_){
_start:
{
lean_object* v_ks_1405_; lean_object* v_vs_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1430_; 
v_ks_1405_ = lean_ctor_get(v_x_1401_, 0);
v_vs_1406_ = lean_ctor_get(v_x_1401_, 1);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_x_1401_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1408_ = v_x_1401_;
v_isShared_1409_ = v_isSharedCheck_1430_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_vs_1406_);
lean_inc(v_ks_1405_);
lean_dec(v_x_1401_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1430_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___x_1410_ = lean_array_get_size(v_ks_1405_);
v___x_1411_ = lean_nat_dec_lt(v_x_1402_, v___x_1410_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
lean_dec(v_x_1402_);
v___x_1412_ = lean_array_push(v_ks_1405_, v_x_1403_);
v___x_1413_ = lean_array_push(v_vs_1406_, v_x_1404_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 1, v___x_1413_);
lean_ctor_set(v___x_1408_, 0, v___x_1412_);
v___x_1415_ = v___x_1408_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
else
{
lean_object* v_k_x27_1417_; uint8_t v___x_1418_; 
v_k_x27_1417_ = lean_array_fget_borrowed(v_ks_1405_, v_x_1402_);
v___x_1418_ = l_Lean_instBEqMVarId_beq(v_x_1403_, v_k_x27_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1420_; 
if (v_isShared_1409_ == 0)
{
v___x_1420_ = v___x_1408_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_ks_1405_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_vs_1406_);
v___x_1420_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = lean_unsigned_to_nat(1u);
v___x_1422_ = lean_nat_add(v_x_1402_, v___x_1421_);
lean_dec(v_x_1402_);
v_x_1401_ = v___x_1420_;
v_x_1402_ = v___x_1422_;
goto _start;
}
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1425_ = lean_array_fset(v_ks_1405_, v_x_1402_, v_x_1403_);
v___x_1426_ = lean_array_fset(v_vs_1406_, v_x_1402_, v_x_1404_);
lean_dec(v_x_1402_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 1, v___x_1426_);
lean_ctor_set(v___x_1408_, 0, v___x_1425_);
v___x_1428_ = v___x_1408_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30___redArg(lean_object* v_n_1431_, lean_object* v_k_1432_, lean_object* v_v_1433_){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32___redArg(v_n_1431_, v___x_1434_, v_k_1432_, v_v_1433_);
return v___x_1435_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0(void){
_start:
{
size_t v___x_1436_; size_t v___x_1437_; size_t v___x_1438_; 
v___x_1436_ = ((size_t)5ULL);
v___x_1437_ = ((size_t)1ULL);
v___x_1438_ = lean_usize_shift_left(v___x_1437_, v___x_1436_);
return v___x_1438_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1(void){
_start:
{
size_t v___x_1439_; size_t v___x_1440_; size_t v___x_1441_; 
v___x_1439_ = ((size_t)1ULL);
v___x_1440_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0);
v___x_1441_ = lean_usize_sub(v___x_1440_, v___x_1439_);
return v___x_1441_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(lean_object* v_x_1443_, size_t v_x_1444_, size_t v_x_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_){
_start:
{
if (lean_obj_tag(v_x_1443_) == 0)
{
lean_object* v_es_1448_; size_t v___x_1449_; size_t v___x_1450_; size_t v___x_1451_; size_t v___x_1452_; lean_object* v_j_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v_es_1448_ = lean_ctor_get(v_x_1443_, 0);
v___x_1449_ = ((size_t)5ULL);
v___x_1450_ = ((size_t)1ULL);
v___x_1451_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1);
v___x_1452_ = lean_usize_land(v_x_1444_, v___x_1451_);
v_j_1453_ = lean_usize_to_nat(v___x_1452_);
v___x_1454_ = lean_array_get_size(v_es_1448_);
v___x_1455_ = lean_nat_dec_lt(v_j_1453_, v___x_1454_);
if (v___x_1455_ == 0)
{
lean_dec(v_j_1453_);
lean_dec(v_x_1447_);
lean_dec(v_x_1446_);
return v_x_1443_;
}
else
{
lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1492_; 
lean_inc_ref(v_es_1448_);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_x_1443_);
if (v_isSharedCheck_1492_ == 0)
{
lean_object* v_unused_1493_; 
v_unused_1493_ = lean_ctor_get(v_x_1443_, 0);
lean_dec(v_unused_1493_);
v___x_1457_ = v_x_1443_;
v_isShared_1458_ = v_isSharedCheck_1492_;
goto v_resetjp_1456_;
}
else
{
lean_dec(v_x_1443_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1492_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v_v_1459_; lean_object* v___x_1460_; lean_object* v_xs_x27_1461_; lean_object* v___y_1463_; 
v_v_1459_ = lean_array_fget(v_es_1448_, v_j_1453_);
v___x_1460_ = lean_box(0);
v_xs_x27_1461_ = lean_array_fset(v_es_1448_, v_j_1453_, v___x_1460_);
switch(lean_obj_tag(v_v_1459_))
{
case 0:
{
lean_object* v_key_1468_; lean_object* v_val_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1479_; 
v_key_1468_ = lean_ctor_get(v_v_1459_, 0);
v_val_1469_ = lean_ctor_get(v_v_1459_, 1);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_v_1459_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1471_ = v_v_1459_;
v_isShared_1472_ = v_isSharedCheck_1479_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_val_1469_);
lean_inc(v_key_1468_);
lean_dec(v_v_1459_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1479_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
uint8_t v___x_1473_; 
v___x_1473_ = l_Lean_instBEqMVarId_beq(v_x_1446_, v_key_1468_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_del_object(v___x_1471_);
v___x_1474_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1468_, v_val_1469_, v_x_1446_, v_x_1447_);
v___x_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
v___y_1463_ = v___x_1475_;
goto v___jp_1462_;
}
else
{
lean_object* v___x_1477_; 
lean_dec(v_val_1469_);
lean_dec(v_key_1468_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 1, v_x_1447_);
lean_ctor_set(v___x_1471_, 0, v_x_1446_);
v___x_1477_ = v___x_1471_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_x_1446_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_x_1447_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
v___y_1463_ = v___x_1477_;
goto v___jp_1462_;
}
}
}
}
case 1:
{
lean_object* v_node_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1490_; 
v_node_1480_ = lean_ctor_get(v_v_1459_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_v_1459_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1482_ = v_v_1459_;
v_isShared_1483_ = v_isSharedCheck_1490_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_node_1480_);
lean_dec(v_v_1459_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1490_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
size_t v___x_1484_; size_t v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1484_ = lean_usize_shift_right(v_x_1444_, v___x_1449_);
v___x_1485_ = lean_usize_add(v_x_1445_, v___x_1450_);
v___x_1486_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_node_1480_, v___x_1484_, v___x_1485_, v_x_1446_, v_x_1447_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v___x_1486_);
v___x_1488_ = v___x_1482_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
v___y_1463_ = v___x_1488_;
goto v___jp_1462_;
}
}
}
default: 
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v_x_1446_);
lean_ctor_set(v___x_1491_, 1, v_x_1447_);
v___y_1463_ = v___x_1491_;
goto v___jp_1462_;
}
}
v___jp_1462_:
{
lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1464_ = lean_array_fset(v_xs_x27_1461_, v_j_1453_, v___y_1463_);
lean_dec(v_j_1453_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1464_);
v___x_1466_ = v___x_1457_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
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
else
{
lean_object* v_ks_1494_; lean_object* v_vs_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1515_; 
v_ks_1494_ = lean_ctor_get(v_x_1443_, 0);
v_vs_1495_ = lean_ctor_get(v_x_1443_, 1);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_x_1443_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1497_ = v_x_1443_;
v_isShared_1498_ = v_isSharedCheck_1515_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_vs_1495_);
lean_inc(v_ks_1494_);
lean_dec(v_x_1443_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1515_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_ks_1494_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_vs_1495_);
v___x_1500_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v_newNode_1501_; uint8_t v___y_1503_; size_t v___x_1509_; uint8_t v___x_1510_; 
v_newNode_1501_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30___redArg(v___x_1500_, v_x_1446_, v_x_1447_);
v___x_1509_ = ((size_t)7ULL);
v___x_1510_ = lean_usize_dec_le(v___x_1509_, v_x_1445_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1511_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1501_);
v___x_1512_ = lean_unsigned_to_nat(4u);
v___x_1513_ = lean_nat_dec_lt(v___x_1511_, v___x_1512_);
lean_dec(v___x_1511_);
v___y_1503_ = v___x_1513_;
goto v___jp_1502_;
}
else
{
v___y_1503_ = v___x_1510_;
goto v___jp_1502_;
}
v___jp_1502_:
{
if (v___y_1503_ == 0)
{
lean_object* v_ks_1504_; lean_object* v_vs_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v_ks_1504_ = lean_ctor_get(v_newNode_1501_, 0);
lean_inc_ref(v_ks_1504_);
v_vs_1505_ = lean_ctor_get(v_newNode_1501_, 1);
lean_inc_ref(v_vs_1505_);
lean_dec_ref(v_newNode_1501_);
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2);
v___x_1508_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(v_x_1445_, v_ks_1504_, v_vs_1505_, v___x_1506_, v___x_1507_);
lean_dec_ref(v_vs_1505_);
lean_dec_ref(v_ks_1504_);
return v___x_1508_;
}
else
{
return v_newNode_1501_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(size_t v_depth_1516_, lean_object* v_keys_1517_, lean_object* v_vals_1518_, lean_object* v_i_1519_, lean_object* v_entries_1520_){
_start:
{
lean_object* v___x_1521_; uint8_t v___x_1522_; 
v___x_1521_ = lean_array_get_size(v_keys_1517_);
v___x_1522_ = lean_nat_dec_lt(v_i_1519_, v___x_1521_);
if (v___x_1522_ == 0)
{
lean_dec(v_i_1519_);
return v_entries_1520_;
}
else
{
lean_object* v_k_1523_; lean_object* v_v_1524_; uint64_t v___x_1525_; size_t v_h_1526_; size_t v___x_1527_; lean_object* v___x_1528_; size_t v___x_1529_; size_t v___x_1530_; size_t v___x_1531_; size_t v_h_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v_k_1523_ = lean_array_fget_borrowed(v_keys_1517_, v_i_1519_);
v_v_1524_ = lean_array_fget_borrowed(v_vals_1518_, v_i_1519_);
v___x_1525_ = l_Lean_instHashableMVarId_hash(v_k_1523_);
v_h_1526_ = lean_uint64_to_usize(v___x_1525_);
v___x_1527_ = ((size_t)5ULL);
v___x_1528_ = lean_unsigned_to_nat(1u);
v___x_1529_ = ((size_t)1ULL);
v___x_1530_ = lean_usize_sub(v_depth_1516_, v___x_1529_);
v___x_1531_ = lean_usize_mul(v___x_1527_, v___x_1530_);
v_h_1532_ = lean_usize_shift_right(v_h_1526_, v___x_1531_);
v___x_1533_ = lean_nat_add(v_i_1519_, v___x_1528_);
lean_dec(v_i_1519_);
lean_inc(v_v_1524_);
lean_inc(v_k_1523_);
v___x_1534_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_entries_1520_, v_h_1532_, v_depth_1516_, v_k_1523_, v_v_1524_);
v_i_1519_ = v___x_1533_;
v_entries_1520_ = v___x_1534_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg___boxed(lean_object* v_depth_1536_, lean_object* v_keys_1537_, lean_object* v_vals_1538_, lean_object* v_i_1539_, lean_object* v_entries_1540_){
_start:
{
size_t v_depth_boxed_1541_; lean_object* v_res_1542_; 
v_depth_boxed_1541_ = lean_unbox_usize(v_depth_1536_);
lean_dec(v_depth_1536_);
v_res_1542_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(v_depth_boxed_1541_, v_keys_1537_, v_vals_1538_, v_i_1539_, v_entries_1540_);
lean_dec_ref(v_vals_1538_);
lean_dec_ref(v_keys_1537_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___boxed(lean_object* v_x_1543_, lean_object* v_x_1544_, lean_object* v_x_1545_, lean_object* v_x_1546_, lean_object* v_x_1547_){
_start:
{
size_t v_x_22177__boxed_1548_; size_t v_x_22178__boxed_1549_; lean_object* v_res_1550_; 
v_x_22177__boxed_1548_ = lean_unbox_usize(v_x_1544_);
lean_dec(v_x_1544_);
v_x_22178__boxed_1549_ = lean_unbox_usize(v_x_1545_);
lean_dec(v_x_1545_);
v_res_1550_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_x_1543_, v_x_22177__boxed_1548_, v_x_22178__boxed_1549_, v_x_1546_, v_x_1547_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(lean_object* v_x_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_){
_start:
{
uint64_t v___x_1554_; size_t v___x_1555_; size_t v___x_1556_; lean_object* v___x_1557_; 
v___x_1554_ = l_Lean_instHashableMVarId_hash(v_x_1552_);
v___x_1555_ = lean_uint64_to_usize(v___x_1554_);
v___x_1556_ = ((size_t)1ULL);
v___x_1557_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_x_1551_, v___x_1555_, v___x_1556_, v_x_1552_, v_x_1553_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(lean_object* v_mvarId_1558_, lean_object* v_val_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v___x_1562_; lean_object* v_mctx_1563_; lean_object* v_cache_1564_; lean_object* v_zetaDeltaFVarIds_1565_; lean_object* v_postponed_1566_; lean_object* v_diag_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1595_; 
v___x_1562_ = lean_st_ref_take(v___y_1560_);
v_mctx_1563_ = lean_ctor_get(v___x_1562_, 0);
v_cache_1564_ = lean_ctor_get(v___x_1562_, 1);
v_zetaDeltaFVarIds_1565_ = lean_ctor_get(v___x_1562_, 2);
v_postponed_1566_ = lean_ctor_get(v___x_1562_, 3);
v_diag_1567_ = lean_ctor_get(v___x_1562_, 4);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1569_ = v___x_1562_;
v_isShared_1570_ = v_isSharedCheck_1595_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_diag_1567_);
lean_inc(v_postponed_1566_);
lean_inc(v_zetaDeltaFVarIds_1565_);
lean_inc(v_cache_1564_);
lean_inc(v_mctx_1563_);
lean_dec(v___x_1562_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1595_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v_depth_1571_; lean_object* v_levelAssignDepth_1572_; lean_object* v_lmvarCounter_1573_; lean_object* v_mvarCounter_1574_; lean_object* v_lDecls_1575_; lean_object* v_decls_1576_; lean_object* v_userNames_1577_; lean_object* v_lAssignment_1578_; lean_object* v_eAssignment_1579_; lean_object* v_dAssignment_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1594_; 
v_depth_1571_ = lean_ctor_get(v_mctx_1563_, 0);
v_levelAssignDepth_1572_ = lean_ctor_get(v_mctx_1563_, 1);
v_lmvarCounter_1573_ = lean_ctor_get(v_mctx_1563_, 2);
v_mvarCounter_1574_ = lean_ctor_get(v_mctx_1563_, 3);
v_lDecls_1575_ = lean_ctor_get(v_mctx_1563_, 4);
v_decls_1576_ = lean_ctor_get(v_mctx_1563_, 5);
v_userNames_1577_ = lean_ctor_get(v_mctx_1563_, 6);
v_lAssignment_1578_ = lean_ctor_get(v_mctx_1563_, 7);
v_eAssignment_1579_ = lean_ctor_get(v_mctx_1563_, 8);
v_dAssignment_1580_ = lean_ctor_get(v_mctx_1563_, 9);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_mctx_1563_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1582_ = v_mctx_1563_;
v_isShared_1583_ = v_isSharedCheck_1594_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_dAssignment_1580_);
lean_inc(v_eAssignment_1579_);
lean_inc(v_lAssignment_1578_);
lean_inc(v_userNames_1577_);
lean_inc(v_decls_1576_);
lean_inc(v_lDecls_1575_);
lean_inc(v_mvarCounter_1574_);
lean_inc(v_lmvarCounter_1573_);
lean_inc(v_levelAssignDepth_1572_);
lean_inc(v_depth_1571_);
lean_dec(v_mctx_1563_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1594_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1584_; lean_object* v___x_1586_; 
v___x_1584_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(v_eAssignment_1579_, v_mvarId_1558_, v_val_1559_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 8, v___x_1584_);
v___x_1586_ = v___x_1582_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_depth_1571_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_levelAssignDepth_1572_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_lmvarCounter_1573_);
lean_ctor_set(v_reuseFailAlloc_1593_, 3, v_mvarCounter_1574_);
lean_ctor_set(v_reuseFailAlloc_1593_, 4, v_lDecls_1575_);
lean_ctor_set(v_reuseFailAlloc_1593_, 5, v_decls_1576_);
lean_ctor_set(v_reuseFailAlloc_1593_, 6, v_userNames_1577_);
lean_ctor_set(v_reuseFailAlloc_1593_, 7, v_lAssignment_1578_);
lean_ctor_set(v_reuseFailAlloc_1593_, 8, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1593_, 9, v_dAssignment_1580_);
v___x_1586_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
lean_object* v___x_1588_; 
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v___x_1586_);
v___x_1588_ = v___x_1569_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_cache_1564_);
lean_ctor_set(v_reuseFailAlloc_1592_, 2, v_zetaDeltaFVarIds_1565_);
lean_ctor_set(v_reuseFailAlloc_1592_, 3, v_postponed_1566_);
lean_ctor_set(v_reuseFailAlloc_1592_, 4, v_diag_1567_);
v___x_1588_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1589_ = lean_st_ref_set(v___y_1560_, v___x_1588_);
v___x_1590_ = lean_box(0);
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
return v___x_1591_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___redArg___boxed(lean_object* v_mvarId_1596_, lean_object* v_val_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(v_mvarId_1596_, v_val_1597_, v___y_1598_);
lean_dec(v___y_1598_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(lean_object* v_msgData_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v___x_1607_; lean_object* v_env_1608_; lean_object* v___x_1609_; lean_object* v_mctx_1610_; lean_object* v_lctx_1611_; lean_object* v_options_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1607_ = lean_st_ref_get(v___y_1605_);
v_env_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc_ref(v_env_1608_);
lean_dec(v___x_1607_);
v___x_1609_ = lean_st_ref_get(v___y_1603_);
v_mctx_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc_ref(v_mctx_1610_);
lean_dec(v___x_1609_);
v_lctx_1611_ = lean_ctor_get(v___y_1602_, 2);
v_options_1612_ = lean_ctor_get(v___y_1604_, 2);
lean_inc_ref(v_options_1612_);
lean_inc_ref(v_lctx_1611_);
v___x_1613_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1613_, 0, v_env_1608_);
lean_ctor_set(v___x_1613_, 1, v_mctx_1610_);
lean_ctor_set(v___x_1613_, 2, v_lctx_1611_);
lean_ctor_set(v___x_1613_, 3, v_options_1612_);
v___x_1614_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
lean_ctor_set(v___x_1614_, 1, v_msgData_1601_);
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17___boxed(lean_object* v_msgData_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(v_msgData_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(lean_object* v_msg_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_ref_1629_; lean_object* v___x_1630_; lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1639_; 
v_ref_1629_ = lean_ctor_get(v___y_1626_, 5);
v___x_1630_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(v_msg_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1633_ = v___x_1630_;
v_isShared_1634_ = v_isSharedCheck_1639_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1639_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; lean_object* v___x_1637_; 
lean_inc(v_ref_1629_);
v___x_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1635_, 0, v_ref_1629_);
lean_ctor_set(v___x_1635_, 1, v_a_1631_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set_tag(v___x_1633_, 1);
lean_ctor_set(v___x_1633_, 0, v___x_1635_);
v___x_1637_ = v___x_1633_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___redArg___boxed(lean_object* v_msg_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(v_msg_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__1(size_t v_sz_1647_, size_t v_i_1648_, lean_object* v_bs_1649_){
_start:
{
uint8_t v___x_1650_; 
v___x_1650_ = lean_usize_dec_lt(v_i_1648_, v_sz_1647_);
if (v___x_1650_ == 0)
{
return v_bs_1649_;
}
else
{
lean_object* v_v_1651_; lean_object* v___x_1652_; lean_object* v_bs_x27_1653_; lean_object* v___x_1654_; size_t v___x_1655_; size_t v___x_1656_; lean_object* v___x_1657_; 
v_v_1651_ = lean_array_uget(v_bs_1649_, v_i_1648_);
v___x_1652_ = lean_unsigned_to_nat(0u);
v_bs_x27_1653_ = lean_array_uset(v_bs_1649_, v_i_1648_, v___x_1652_);
v___x_1654_ = l_Lean_mkFVar(v_v_1651_);
v___x_1655_ = ((size_t)1ULL);
v___x_1656_ = lean_usize_add(v_i_1648_, v___x_1655_);
v___x_1657_ = lean_array_uset(v_bs_x27_1653_, v_i_1648_, v___x_1654_);
v_i_1648_ = v___x_1656_;
v_bs_1649_ = v___x_1657_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__1___boxed(lean_object* v_sz_1659_, lean_object* v_i_1660_, lean_object* v_bs_1661_){
_start:
{
size_t v_sz_boxed_1662_; size_t v_i_boxed_1663_; lean_object* v_res_1664_; 
v_sz_boxed_1662_ = lean_unbox_usize(v_sz_1659_);
lean_dec(v_sz_1659_);
v_i_boxed_1663_ = lean_unbox_usize(v_i_1660_);
lean_dec(v_i_1660_);
v_res_1664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__1(v_sz_boxed_1662_, v_i_boxed_1663_, v_bs_1661_);
return v_res_1664_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4(void){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1671_ = lean_box(0);
v___x_1672_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3));
v___x_1673_ = l_Lean_mkConst(v___x_1672_, v___x_1671_);
return v___x_1673_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = lean_unsigned_to_nat(0u);
v___x_1679_ = l_Lean_Level_ofNat(v___x_1678_);
return v___x_1679_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1680_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12);
v___x_1681_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7);
v___x_1682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1681_);
lean_ctor_set(v___x_1682_, 1, v___x_1680_);
return v___x_1682_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9(void){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8);
v___x_1684_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6));
v___x_1685_ = l_Lean_mkConst(v___x_1684_, v___x_1683_);
return v___x_1685_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = lean_box(0);
v___x_1687_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6));
v___x_1688_ = l_Lean_mkConst(v___x_1687_, v___x_1686_);
return v___x_1688_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11(void){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = lean_box(0);
v___x_1690_ = lean_unsigned_to_nat(16u);
v___x_1691_ = lean_mk_array(v___x_1690_, v___x_1689_);
return v___x_1691_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12(void){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1692_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11);
v___x_1693_ = lean_unsigned_to_nat(0u);
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
lean_ctor_set(v___x_1694_, 1, v___x_1692_);
return v___x_1694_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13));
v___x_1697_ = l_Lean_stringToMessageData(v___x_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4(lean_object* v_fst_1698_, lean_object* v_snd_1699_, lean_object* v_goal_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
size_t v___y_1708_; uint8_t v___y_1709_; lean_object* v___y_1710_; size_t v___y_1711_; lean_object* v___y_1712_; lean_object* v_a_1713_; size_t v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___x_1903_; lean_object* v___y_1905_; lean_object* v_relevantHyps_1922_; lean_object* v_size_1923_; lean_object* v_buckets_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1903_ = lean_st_ref_get(v___y_1701_);
v_relevantHyps_1922_ = lean_ctor_get(v___x_1903_, 1);
lean_inc_ref(v_relevantHyps_1922_);
lean_dec(v___x_1903_);
v_size_1923_ = lean_ctor_get(v_relevantHyps_1922_, 0);
lean_inc(v_size_1923_);
v_buckets_1924_ = lean_ctor_get(v_relevantHyps_1922_, 1);
lean_inc_ref(v_buckets_1924_);
lean_dec_ref(v_relevantHyps_1922_);
v___x_1925_ = lean_mk_empty_array_with_capacity(v_size_1923_);
lean_dec(v_size_1923_);
v___x_1926_ = lean_unsigned_to_nat(0u);
v___x_1927_ = lean_array_get_size(v_buckets_1924_);
v___x_1928_ = lean_nat_dec_lt(v___x_1926_, v___x_1927_);
if (v___x_1928_ == 0)
{
lean_dec_ref(v_buckets_1924_);
v___y_1905_ = v___x_1925_;
goto v___jp_1904_;
}
else
{
uint8_t v___x_1929_; 
v___x_1929_ = lean_nat_dec_le(v___x_1927_, v___x_1927_);
if (v___x_1929_ == 0)
{
if (v___x_1928_ == 0)
{
lean_dec_ref(v_buckets_1924_);
v___y_1905_ = v___x_1925_;
goto v___jp_1904_;
}
else
{
size_t v___x_1930_; size_t v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = ((size_t)0ULL);
v___x_1931_ = lean_usize_of_nat(v___x_1927_);
v___x_1932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__13(v_buckets_1924_, v___x_1930_, v___x_1931_, v___x_1925_);
lean_dec_ref(v_buckets_1924_);
v___y_1905_ = v___x_1932_;
goto v___jp_1904_;
}
}
else
{
size_t v___x_1933_; size_t v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = ((size_t)0ULL);
v___x_1934_ = lean_usize_of_nat(v___x_1927_);
v___x_1935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__13(v_buckets_1924_, v___x_1933_, v___x_1934_, v___x_1925_);
lean_dec_ref(v_buckets_1924_);
v___y_1905_ = v___x_1935_;
goto v___jp_1904_;
}
}
v___jp_1707_:
{
lean_object* v_fst_1714_; lean_object* v_snd_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v_fst_1714_ = lean_ctor_get(v_a_1713_, 0);
lean_inc(v_fst_1714_);
v_snd_1715_ = lean_ctor_get(v_a_1713_, 1);
lean_inc(v_snd_1715_);
lean_dec_ref(v_a_1713_);
v___x_1716_ = l_Lean_Expr_getAppFn(v_fst_1714_);
lean_dec(v_fst_1714_);
v___x_1717_ = l_Lean_Expr_mvarId_x21(v___x_1716_);
lean_dec_ref(v___x_1716_);
v___x_1718_ = l_Lean_MVarId_getType(v___x_1717_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___f_1725_; lean_object* v___x_1726_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref(v___x_1718_);
v___x_1720_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1));
v___x_1721_ = lean_box(0);
v___x_1722_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4);
v___x_1723_ = lean_box_usize(v___y_1708_);
v___x_1724_ = lean_box(v___y_1709_);
lean_inc(v_fst_1698_);
v___f_1725_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___boxed), 14, 7);
lean_closure_set(v___f_1725_, 0, v___x_1721_);
lean_closure_set(v___f_1725_, 1, v___y_1710_);
lean_closure_set(v___f_1725_, 2, v___x_1723_);
lean_closure_set(v___f_1725_, 3, v_a_1719_);
lean_closure_set(v___f_1725_, 4, v___x_1724_);
lean_closure_set(v___f_1725_, 5, v_fst_1698_);
lean_closure_set(v___f_1725_, 6, v___x_1722_);
v___x_1726_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v___x_1720_, v___x_1722_, v___f_1725_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v_fst_1728_; lean_object* v_snd_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref(v___x_1726_);
v_fst_1728_ = lean_ctor_get(v_a_1727_, 0);
lean_inc(v_fst_1728_);
v_snd_1729_ = lean_ctor_get(v_a_1727_, 1);
lean_inc(v_snd_1729_);
lean_dec(v_a_1727_);
v___x_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1730_, 0, v_snd_1729_);
v___x_1731_ = 0;
v___x_1732_ = lean_box(0);
v___x_1733_ = l_Lean_Meta_mkFreshExprMVar(v___x_1730_, v___x_1731_, v___x_1732_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; size_t v_sz_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_a_1734_);
lean_dec_ref(v___x_1733_);
v___x_1735_ = l_Lean_Expr_mvarId_x21(v_a_1734_);
lean_dec(v_a_1734_);
v___x_1736_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9);
v___x_1737_ = l_Lean_mkNatLit(v_fst_1698_);
v___x_1738_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10);
lean_inc(v___x_1735_);
v___x_1739_ = l_Lean_mkMVar(v___x_1735_);
v___x_1740_ = l_Lean_mkApp6(v___x_1736_, v___x_1722_, v___x_1737_, v_fst_1728_, v___x_1738_, v_snd_1699_, v___x_1739_);
lean_inc_ref(v___y_1712_);
v___x_1741_ = l_Array_append___redArg(v___y_1712_, v_snd_1715_);
v___x_1742_ = l_Lean_mkAppN(v___x_1740_, v___x_1741_);
lean_dec_ref(v___x_1741_);
v___x_1743_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(v_goal_1700_, v___x_1742_, v___y_1703_);
lean_dec_ref(v___x_1743_);
v_sz_1744_ = lean_array_size(v_snd_1715_);
lean_inc(v_snd_1715_);
v___x_1745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__8(v_sz_1744_, v___y_1711_, v_snd_1715_);
v___x_1746_ = l_Lean_MVarId_tryClearMany_x27(v___x_1735_, v___x_1745_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v_fst_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; lean_object* v___x_1753_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref(v___x_1746_);
v_fst_1748_ = lean_ctor_get(v_a_1747_, 0);
lean_inc(v_fst_1748_);
lean_dec(v_a_1747_);
v___x_1749_ = lean_array_get_size(v___y_1712_);
lean_dec_ref(v___y_1712_);
v___x_1750_ = lean_array_get_size(v_snd_1715_);
lean_dec(v_snd_1715_);
v___x_1751_ = lean_nat_add(v___x_1749_, v___x_1750_);
v___x_1752_ = 0;
v___x_1753_ = l_Lean_Meta_introNCore(v_fst_1748_, v___x_1751_, v___x_1721_, v___x_1752_, v___x_1752_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1762_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1756_ = v___x_1753_;
v_isShared_1757_ = v_isSharedCheck_1762_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1762_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v_snd_1758_; lean_object* v___x_1760_; 
v_snd_1758_ = lean_ctor_get(v_a_1754_, 1);
lean_inc(v_snd_1758_);
lean_dec(v_a_1754_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v_snd_1758_);
v___x_1760_ = v___x_1756_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_snd_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
v_a_1763_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1753_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1753_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec(v_snd_1715_);
lean_dec_ref(v___y_1712_);
v_a_1771_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1746_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1746_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec(v_fst_1728_);
lean_dec(v_snd_1715_);
lean_dec_ref(v___y_1712_);
lean_dec(v_goal_1700_);
lean_dec_ref(v_snd_1699_);
lean_dec(v_fst_1698_);
v_a_1779_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1733_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1733_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec(v_snd_1715_);
lean_dec_ref(v___y_1712_);
lean_dec(v_goal_1700_);
lean_dec_ref(v_snd_1699_);
lean_dec(v_fst_1698_);
v_a_1787_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1726_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1726_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec(v_snd_1715_);
lean_dec_ref(v___y_1712_);
lean_dec_ref(v___y_1710_);
lean_dec(v_goal_1700_);
lean_dec_ref(v_snd_1699_);
lean_dec(v_fst_1698_);
v_a_1795_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1718_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1718_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
v___jp_1803_:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v_lctx_1810_; lean_object* v_mctx_1811_; lean_object* v_ngen_1812_; lean_object* v_quotContext_1813_; lean_object* v_nextMacroScope_1814_; uint8_t v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1807_ = lean_st_ref_get(v___y_1703_);
v___x_1808_ = lean_st_ref_get(v___y_1705_);
v___x_1809_ = lean_st_ref_get(v___y_1705_);
v_lctx_1810_ = lean_ctor_get(v___y_1702_, 2);
v_mctx_1811_ = lean_ctor_get(v___x_1807_, 0);
lean_inc_ref(v_mctx_1811_);
lean_dec(v___x_1807_);
v_ngen_1812_ = lean_ctor_get(v___x_1808_, 2);
lean_inc_ref(v_ngen_1812_);
lean_dec(v___x_1808_);
v_quotContext_1813_ = lean_ctor_get(v___y_1704_, 10);
v_nextMacroScope_1814_ = lean_ctor_get(v___x_1809_, 1);
lean_inc(v_nextMacroScope_1814_);
lean_dec(v___x_1809_);
v___x_1815_ = 1;
lean_inc_ref(v_lctx_1810_);
lean_inc(v_quotContext_1813_);
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v_quotContext_1813_);
lean_ctor_set(v___x_1816_, 1, v_lctx_1810_);
v___x_1817_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12);
v___x_1818_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1818_, 0, v_mctx_1811_);
lean_ctor_set(v___x_1818_, 1, v_nextMacroScope_1814_);
lean_ctor_set(v___x_1818_, 2, v_ngen_1812_);
lean_ctor_set(v___x_1818_, 3, v___x_1817_);
lean_inc(v_goal_1700_);
v___x_1819_ = l_Lean_MetavarContext_revert(v___y_1805_, v_goal_1700_, v___x_1815_, v___x_1816_, v___x_1818_);
lean_dec_ref(v___x_1816_);
lean_dec_ref(v___y_1805_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v_a_1821_; lean_object* v___x_1822_; lean_object* v_mctx_1823_; lean_object* v_nextMacroScope_1824_; lean_object* v_ngen_1825_; lean_object* v_cache_1826_; lean_object* v_zetaDeltaFVarIds_1827_; lean_object* v_postponed_1828_; lean_object* v_diag_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1855_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
v_a_1821_ = lean_ctor_get(v___x_1819_, 1);
lean_inc(v_a_1821_);
lean_dec_ref(v___x_1819_);
v___x_1822_ = lean_st_ref_take(v___y_1703_);
v_mctx_1823_ = lean_ctor_get(v_a_1821_, 0);
lean_inc_ref(v_mctx_1823_);
v_nextMacroScope_1824_ = lean_ctor_get(v_a_1821_, 1);
lean_inc(v_nextMacroScope_1824_);
v_ngen_1825_ = lean_ctor_get(v_a_1821_, 2);
lean_inc_ref(v_ngen_1825_);
lean_dec(v_a_1821_);
v_cache_1826_ = lean_ctor_get(v___x_1822_, 1);
v_zetaDeltaFVarIds_1827_ = lean_ctor_get(v___x_1822_, 2);
v_postponed_1828_ = lean_ctor_get(v___x_1822_, 3);
v_diag_1829_ = lean_ctor_get(v___x_1822_, 4);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1855_ == 0)
{
lean_object* v_unused_1856_; 
v_unused_1856_ = lean_ctor_get(v___x_1822_, 0);
lean_dec(v_unused_1856_);
v___x_1831_ = v___x_1822_;
v_isShared_1832_ = v_isSharedCheck_1855_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_diag_1829_);
lean_inc(v_postponed_1828_);
lean_inc(v_zetaDeltaFVarIds_1827_);
lean_inc(v_cache_1826_);
lean_dec(v___x_1822_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1855_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v_mctx_1823_);
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_mctx_1823_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_cache_1826_);
lean_ctor_set(v_reuseFailAlloc_1854_, 2, v_zetaDeltaFVarIds_1827_);
lean_ctor_set(v_reuseFailAlloc_1854_, 3, v_postponed_1828_);
lean_ctor_set(v_reuseFailAlloc_1854_, 4, v_diag_1829_);
v___x_1834_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v_env_1837_; lean_object* v_auxDeclNGen_1838_; lean_object* v_traceState_1839_; lean_object* v_cache_1840_; lean_object* v_messages_1841_; lean_object* v_infoState_1842_; lean_object* v_snapshotTasks_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1851_; 
v___x_1835_ = lean_st_ref_set(v___y_1703_, v___x_1834_);
v___x_1836_ = lean_st_ref_take(v___y_1705_);
v_env_1837_ = lean_ctor_get(v___x_1836_, 0);
v_auxDeclNGen_1838_ = lean_ctor_get(v___x_1836_, 3);
v_traceState_1839_ = lean_ctor_get(v___x_1836_, 4);
v_cache_1840_ = lean_ctor_get(v___x_1836_, 5);
v_messages_1841_ = lean_ctor_get(v___x_1836_, 6);
v_infoState_1842_ = lean_ctor_get(v___x_1836_, 7);
v_snapshotTasks_1843_ = lean_ctor_get(v___x_1836_, 8);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1851_ == 0)
{
lean_object* v_unused_1852_; lean_object* v_unused_1853_; 
v_unused_1852_ = lean_ctor_get(v___x_1836_, 2);
lean_dec(v_unused_1852_);
v_unused_1853_ = lean_ctor_get(v___x_1836_, 1);
lean_dec(v_unused_1853_);
v___x_1845_ = v___x_1836_;
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_snapshotTasks_1843_);
lean_inc(v_infoState_1842_);
lean_inc(v_messages_1841_);
lean_inc(v_cache_1840_);
lean_inc(v_traceState_1839_);
lean_inc(v_auxDeclNGen_1838_);
lean_inc(v_env_1837_);
lean_dec(v___x_1836_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 2, v_ngen_1825_);
lean_ctor_set(v___x_1845_, 1, v_nextMacroScope_1824_);
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_env_1837_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_nextMacroScope_1824_);
lean_ctor_set(v_reuseFailAlloc_1850_, 2, v_ngen_1825_);
lean_ctor_set(v_reuseFailAlloc_1850_, 3, v_auxDeclNGen_1838_);
lean_ctor_set(v_reuseFailAlloc_1850_, 4, v_traceState_1839_);
lean_ctor_set(v_reuseFailAlloc_1850_, 5, v_cache_1840_);
lean_ctor_set(v_reuseFailAlloc_1850_, 6, v_messages_1841_);
lean_ctor_set(v_reuseFailAlloc_1850_, 7, v_infoState_1842_);
lean_ctor_set(v_reuseFailAlloc_1850_, 8, v_snapshotTasks_1843_);
v___x_1848_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_st_ref_set(v___y_1705_, v___x_1848_);
lean_inc_ref(v___y_1806_);
v___y_1708_ = v___y_1804_;
v___y_1709_ = v___x_1815_;
v___y_1710_ = v___y_1806_;
v___y_1711_ = v___y_1804_;
v___y_1712_ = v___y_1806_;
v_a_1713_ = v_a_1820_;
goto v___jp_1707_;
}
}
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1858_; lean_object* v_mctx_1859_; lean_object* v_nextMacroScope_1860_; lean_object* v_ngen_1861_; lean_object* v_cache_1862_; lean_object* v_zetaDeltaFVarIds_1863_; lean_object* v_postponed_1864_; lean_object* v_diag_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1901_; 
lean_dec_ref(v___y_1806_);
lean_dec(v_goal_1700_);
lean_dec_ref(v_snd_1699_);
lean_dec(v_fst_1698_);
v_a_1857_ = lean_ctor_get(v___x_1819_, 1);
lean_inc(v_a_1857_);
lean_dec_ref(v___x_1819_);
v___x_1858_ = lean_st_ref_take(v___y_1703_);
v_mctx_1859_ = lean_ctor_get(v_a_1857_, 0);
lean_inc_ref(v_mctx_1859_);
v_nextMacroScope_1860_ = lean_ctor_get(v_a_1857_, 1);
lean_inc(v_nextMacroScope_1860_);
v_ngen_1861_ = lean_ctor_get(v_a_1857_, 2);
lean_inc_ref(v_ngen_1861_);
lean_dec(v_a_1857_);
v_cache_1862_ = lean_ctor_get(v___x_1858_, 1);
v_zetaDeltaFVarIds_1863_ = lean_ctor_get(v___x_1858_, 2);
v_postponed_1864_ = lean_ctor_get(v___x_1858_, 3);
v_diag_1865_ = lean_ctor_get(v___x_1858_, 4);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1901_ == 0)
{
lean_object* v_unused_1902_; 
v_unused_1902_ = lean_ctor_get(v___x_1858_, 0);
lean_dec(v_unused_1902_);
v___x_1867_ = v___x_1858_;
v_isShared_1868_ = v_isSharedCheck_1901_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_diag_1865_);
lean_inc(v_postponed_1864_);
lean_inc(v_zetaDeltaFVarIds_1863_);
lean_inc(v_cache_1862_);
lean_dec(v___x_1858_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1901_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v_mctx_1859_);
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_mctx_1859_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_cache_1862_);
lean_ctor_set(v_reuseFailAlloc_1900_, 2, v_zetaDeltaFVarIds_1863_);
lean_ctor_set(v_reuseFailAlloc_1900_, 3, v_postponed_1864_);
lean_ctor_set(v_reuseFailAlloc_1900_, 4, v_diag_1865_);
v___x_1870_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v_env_1873_; lean_object* v_auxDeclNGen_1874_; lean_object* v_traceState_1875_; lean_object* v_cache_1876_; lean_object* v_messages_1877_; lean_object* v_infoState_1878_; lean_object* v_snapshotTasks_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1897_; 
v___x_1871_ = lean_st_ref_set(v___y_1703_, v___x_1870_);
v___x_1872_ = lean_st_ref_take(v___y_1705_);
v_env_1873_ = lean_ctor_get(v___x_1872_, 0);
v_auxDeclNGen_1874_ = lean_ctor_get(v___x_1872_, 3);
v_traceState_1875_ = lean_ctor_get(v___x_1872_, 4);
v_cache_1876_ = lean_ctor_get(v___x_1872_, 5);
v_messages_1877_ = lean_ctor_get(v___x_1872_, 6);
v_infoState_1878_ = lean_ctor_get(v___x_1872_, 7);
v_snapshotTasks_1879_ = lean_ctor_get(v___x_1872_, 8);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; lean_object* v_unused_1899_; 
v_unused_1898_ = lean_ctor_get(v___x_1872_, 2);
lean_dec(v_unused_1898_);
v_unused_1899_ = lean_ctor_get(v___x_1872_, 1);
lean_dec(v_unused_1899_);
v___x_1881_ = v___x_1872_;
v_isShared_1882_ = v_isSharedCheck_1897_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_snapshotTasks_1879_);
lean_inc(v_infoState_1878_);
lean_inc(v_messages_1877_);
lean_inc(v_cache_1876_);
lean_inc(v_traceState_1875_);
lean_inc(v_auxDeclNGen_1874_);
lean_inc(v_env_1873_);
lean_dec(v___x_1872_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1897_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 2, v_ngen_1861_);
lean_ctor_set(v___x_1881_, 1, v_nextMacroScope_1860_);
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_env_1873_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_nextMacroScope_1860_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_ngen_1861_);
lean_ctor_set(v_reuseFailAlloc_1896_, 3, v_auxDeclNGen_1874_);
lean_ctor_set(v_reuseFailAlloc_1896_, 4, v_traceState_1875_);
lean_ctor_set(v_reuseFailAlloc_1896_, 5, v_cache_1876_);
lean_ctor_set(v_reuseFailAlloc_1896_, 6, v_messages_1877_);
lean_ctor_set(v_reuseFailAlloc_1896_, 7, v_infoState_1878_);
lean_ctor_set(v_reuseFailAlloc_1896_, 8, v_snapshotTasks_1879_);
v___x_1884_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
v___x_1885_ = lean_st_ref_set(v___y_1705_, v___x_1884_);
v___x_1886_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14);
v___x_1887_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(v___x_1886_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1887_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1887_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
}
}
}
v___jp_1904_:
{
lean_object* v___x_1906_; lean_object* v_relevantTerms_1907_; lean_object* v_size_1908_; lean_object* v_buckets_1909_; size_t v_sz_1910_; size_t v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; 
v___x_1906_ = lean_st_ref_get(v___y_1701_);
v_relevantTerms_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc_ref(v_relevantTerms_1907_);
lean_dec(v___x_1906_);
v_size_1908_ = lean_ctor_get(v_relevantTerms_1907_, 0);
lean_inc(v_size_1908_);
v_buckets_1909_ = lean_ctor_get(v_relevantTerms_1907_, 1);
lean_inc_ref(v_buckets_1909_);
lean_dec_ref(v_relevantTerms_1907_);
v_sz_1910_ = lean_array_size(v___y_1905_);
v___x_1911_ = ((size_t)0ULL);
v___x_1912_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__1(v_sz_1910_, v___x_1911_, v___y_1905_);
v___x_1913_ = lean_mk_empty_array_with_capacity(v_size_1908_);
lean_dec(v_size_1908_);
v___x_1914_ = lean_unsigned_to_nat(0u);
v___x_1915_ = lean_array_get_size(v_buckets_1909_);
v___x_1916_ = lean_nat_dec_lt(v___x_1914_, v___x_1915_);
if (v___x_1916_ == 0)
{
lean_dec_ref(v_buckets_1909_);
v___y_1804_ = v___x_1911_;
v___y_1805_ = v___x_1912_;
v___y_1806_ = v___x_1913_;
goto v___jp_1803_;
}
else
{
uint8_t v___x_1917_; 
v___x_1917_ = lean_nat_dec_le(v___x_1915_, v___x_1915_);
if (v___x_1917_ == 0)
{
if (v___x_1916_ == 0)
{
lean_dec_ref(v_buckets_1909_);
v___y_1804_ = v___x_1911_;
v___y_1805_ = v___x_1912_;
v___y_1806_ = v___x_1913_;
goto v___jp_1803_;
}
else
{
size_t v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_usize_of_nat(v___x_1915_);
v___x_1919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__11(v_buckets_1909_, v___x_1911_, v___x_1918_, v___x_1913_);
lean_dec_ref(v_buckets_1909_);
v___y_1804_ = v___x_1911_;
v___y_1805_ = v___x_1912_;
v___y_1806_ = v___x_1919_;
goto v___jp_1803_;
}
}
else
{
size_t v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = lean_usize_of_nat(v___x_1915_);
v___x_1921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__11(v_buckets_1909_, v___x_1911_, v___x_1920_, v___x_1913_);
lean_dec_ref(v_buckets_1909_);
v___y_1804_ = v___x_1911_;
v___y_1805_ = v___x_1912_;
v___y_1806_ = v___x_1921_;
goto v___jp_1803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___boxed(lean_object* v_fst_1936_, lean_object* v_snd_1937_, lean_object* v_goal_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4(v_fst_1936_, v_snd_1937_, v_goal_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
return v_res_1945_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34(lean_object* v_opts_1946_, lean_object* v_opt_1947_){
_start:
{
lean_object* v_name_1948_; lean_object* v_defValue_1949_; lean_object* v_map_1950_; lean_object* v___x_1951_; 
v_name_1948_ = lean_ctor_get(v_opt_1947_, 0);
v_defValue_1949_ = lean_ctor_get(v_opt_1947_, 1);
v_map_1950_ = lean_ctor_get(v_opts_1946_, 0);
v___x_1951_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1950_, v_name_1948_);
if (lean_obj_tag(v___x_1951_) == 0)
{
uint8_t v___x_1952_; 
v___x_1952_ = lean_unbox(v_defValue_1949_);
return v___x_1952_;
}
else
{
lean_object* v_val_1953_; 
v_val_1953_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_val_1953_);
lean_dec_ref(v___x_1951_);
if (lean_obj_tag(v_val_1953_) == 1)
{
uint8_t v_v_1954_; 
v_v_1954_ = lean_ctor_get_uint8(v_val_1953_, 0);
lean_dec_ref(v_val_1953_);
return v_v_1954_;
}
else
{
uint8_t v___x_1955_; 
lean_dec(v_val_1953_);
v___x_1955_ = lean_unbox(v_defValue_1949_);
return v___x_1955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34___boxed(lean_object* v_opts_1956_, lean_object* v_opt_1957_){
_start:
{
uint8_t v_res_1958_; lean_object* v_r_1959_; 
v_res_1958_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34(v_opts_1956_, v_opt_1957_);
lean_dec_ref(v_opt_1957_);
lean_dec_ref(v_opts_1956_);
v_r_1959_ = lean_box(v_res_1958_);
return v_r_1959_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0(uint8_t v___y_1968_, uint8_t v_suppressElabErrors_1969_, lean_object* v_x_1970_){
_start:
{
if (lean_obj_tag(v_x_1970_) == 1)
{
lean_object* v_pre_1971_; 
v_pre_1971_ = lean_ctor_get(v_x_1970_, 0);
switch(lean_obj_tag(v_pre_1971_))
{
case 1:
{
lean_object* v_pre_1972_; 
v_pre_1972_ = lean_ctor_get(v_pre_1971_, 0);
switch(lean_obj_tag(v_pre_1972_))
{
case 0:
{
lean_object* v_str_1973_; lean_object* v_str_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
v_str_1973_ = lean_ctor_get(v_x_1970_, 1);
v_str_1974_ = lean_ctor_get(v_pre_1971_, 1);
v___x_1975_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0));
v___x_1976_ = lean_string_dec_eq(v_str_1974_, v___x_1975_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; uint8_t v___x_1978_; 
v___x_1977_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1));
v___x_1978_ = lean_string_dec_eq(v_str_1974_, v___x_1977_);
if (v___x_1978_ == 0)
{
return v___y_1968_;
}
else
{
lean_object* v___x_1979_; uint8_t v___x_1980_; 
v___x_1979_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__2));
v___x_1980_ = lean_string_dec_eq(v_str_1973_, v___x_1979_);
if (v___x_1980_ == 0)
{
return v___y_1968_;
}
else
{
return v_suppressElabErrors_1969_;
}
}
}
else
{
lean_object* v___x_1981_; uint8_t v___x_1982_; 
v___x_1981_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__3));
v___x_1982_ = lean_string_dec_eq(v_str_1973_, v___x_1981_);
if (v___x_1982_ == 0)
{
return v___y_1968_;
}
else
{
return v_suppressElabErrors_1969_;
}
}
}
case 1:
{
lean_object* v_pre_1983_; 
v_pre_1983_ = lean_ctor_get(v_pre_1972_, 0);
if (lean_obj_tag(v_pre_1983_) == 0)
{
lean_object* v_str_1984_; lean_object* v_str_1985_; lean_object* v_str_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
v_str_1984_ = lean_ctor_get(v_x_1970_, 1);
v_str_1985_ = lean_ctor_get(v_pre_1971_, 1);
v_str_1986_ = lean_ctor_get(v_pre_1972_, 1);
v___x_1987_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4));
v___x_1988_ = lean_string_dec_eq(v_str_1986_, v___x_1987_);
if (v___x_1988_ == 0)
{
return v___y_1968_;
}
else
{
lean_object* v___x_1989_; uint8_t v___x_1990_; 
v___x_1989_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5));
v___x_1990_ = lean_string_dec_eq(v_str_1985_, v___x_1989_);
if (v___x_1990_ == 0)
{
return v___y_1968_;
}
else
{
lean_object* v___x_1991_; uint8_t v___x_1992_; 
v___x_1991_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__6));
v___x_1992_ = lean_string_dec_eq(v_str_1984_, v___x_1991_);
if (v___x_1992_ == 0)
{
return v___y_1968_;
}
else
{
return v_suppressElabErrors_1969_;
}
}
}
}
else
{
return v___y_1968_;
}
}
default: 
{
return v___y_1968_;
}
}
}
case 0:
{
lean_object* v_str_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v_str_1993_ = lean_ctor_get(v_x_1970_, 1);
v___x_1994_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__7));
v___x_1995_ = lean_string_dec_eq(v_str_1993_, v___x_1994_);
if (v___x_1995_ == 0)
{
return v___y_1968_;
}
else
{
return v_suppressElabErrors_1969_;
}
}
default: 
{
return v___y_1968_;
}
}
}
else
{
return v___y_1968_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___boxed(lean_object* v___y_1996_, lean_object* v_suppressElabErrors_1997_, lean_object* v_x_1998_){
_start:
{
uint8_t v___y_23019__boxed_1999_; uint8_t v_suppressElabErrors_boxed_2000_; uint8_t v_res_2001_; lean_object* v_r_2002_; 
v___y_23019__boxed_1999_ = lean_unbox(v___y_1996_);
v_suppressElabErrors_boxed_2000_ = lean_unbox(v_suppressElabErrors_1997_);
v_res_2001_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0(v___y_23019__boxed_1999_, v_suppressElabErrors_boxed_2000_, v_x_1998_);
lean_dec(v_x_1998_);
v_r_2002_ = lean_box(v_res_2001_);
return v_r_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(lean_object* v_ref_2004_, lean_object* v_msgData_2005_, uint8_t v_severity_2006_, uint8_t v_isSilent_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
uint8_t v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; uint8_t v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2050_; lean_object* v___y_2051_; uint8_t v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2054_; uint8_t v___y_2055_; uint8_t v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2075_; lean_object* v___y_2076_; uint8_t v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; uint8_t v___y_2080_; uint8_t v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2086_; lean_object* v___y_2087_; uint8_t v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2090_; uint8_t v___y_2091_; uint8_t v___y_2092_; uint8_t v___x_2097_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; uint8_t v___y_2102_; lean_object* v___y_2103_; uint8_t v___y_2104_; uint8_t v___y_2105_; uint8_t v___y_2107_; uint8_t v___x_2122_; 
v___x_2097_ = 2;
v___x_2122_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2006_, v___x_2097_);
if (v___x_2122_ == 0)
{
v___y_2107_ = v___x_2122_;
goto v___jp_2106_;
}
else
{
uint8_t v___x_2123_; 
lean_inc_ref(v_msgData_2005_);
v___x_2123_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2005_);
v___y_2107_ = v___x_2123_;
goto v___jp_2106_;
}
v___jp_2013_:
{
lean_object* v___x_2023_; lean_object* v_currNamespace_2024_; lean_object* v_openDecls_2025_; lean_object* v_env_2026_; lean_object* v_nextMacroScope_2027_; lean_object* v_ngen_2028_; lean_object* v_auxDeclNGen_2029_; lean_object* v_traceState_2030_; lean_object* v_cache_2031_; lean_object* v_messages_2032_; lean_object* v_infoState_2033_; lean_object* v_snapshotTasks_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2048_; 
v___x_2023_ = lean_st_ref_take(v___y_2022_);
v_currNamespace_2024_ = lean_ctor_get(v___y_2021_, 6);
v_openDecls_2025_ = lean_ctor_get(v___y_2021_, 7);
v_env_2026_ = lean_ctor_get(v___x_2023_, 0);
v_nextMacroScope_2027_ = lean_ctor_get(v___x_2023_, 1);
v_ngen_2028_ = lean_ctor_get(v___x_2023_, 2);
v_auxDeclNGen_2029_ = lean_ctor_get(v___x_2023_, 3);
v_traceState_2030_ = lean_ctor_get(v___x_2023_, 4);
v_cache_2031_ = lean_ctor_get(v___x_2023_, 5);
v_messages_2032_ = lean_ctor_get(v___x_2023_, 6);
v_infoState_2033_ = lean_ctor_get(v___x_2023_, 7);
v_snapshotTasks_2034_ = lean_ctor_get(v___x_2023_, 8);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2036_ = v___x_2023_;
v_isShared_2037_ = v_isSharedCheck_2048_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_snapshotTasks_2034_);
lean_inc(v_infoState_2033_);
lean_inc(v_messages_2032_);
lean_inc(v_cache_2031_);
lean_inc(v_traceState_2030_);
lean_inc(v_auxDeclNGen_2029_);
lean_inc(v_ngen_2028_);
lean_inc(v_nextMacroScope_2027_);
lean_inc(v_env_2026_);
lean_dec(v___x_2023_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2048_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2043_; 
lean_inc(v_openDecls_2025_);
lean_inc(v_currNamespace_2024_);
v___x_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2038_, 0, v_currNamespace_2024_);
lean_ctor_set(v___x_2038_, 1, v_openDecls_2025_);
v___x_2039_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
lean_ctor_set(v___x_2039_, 1, v___y_2020_);
lean_inc_ref(v___y_2016_);
lean_inc_ref(v___y_2017_);
v___x_2040_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2040_, 0, v___y_2017_);
lean_ctor_set(v___x_2040_, 1, v___y_2019_);
lean_ctor_set(v___x_2040_, 2, v___y_2015_);
lean_ctor_set(v___x_2040_, 3, v___y_2016_);
lean_ctor_set(v___x_2040_, 4, v___x_2039_);
lean_ctor_set_uint8(v___x_2040_, sizeof(void*)*5, v___y_2014_);
lean_ctor_set_uint8(v___x_2040_, sizeof(void*)*5 + 1, v___y_2018_);
lean_ctor_set_uint8(v___x_2040_, sizeof(void*)*5 + 2, v_isSilent_2007_);
v___x_2041_ = l_Lean_MessageLog_add(v___x_2040_, v_messages_2032_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 6, v___x_2041_);
v___x_2043_ = v___x_2036_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_env_2026_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_nextMacroScope_2027_);
lean_ctor_set(v_reuseFailAlloc_2047_, 2, v_ngen_2028_);
lean_ctor_set(v_reuseFailAlloc_2047_, 3, v_auxDeclNGen_2029_);
lean_ctor_set(v_reuseFailAlloc_2047_, 4, v_traceState_2030_);
lean_ctor_set(v_reuseFailAlloc_2047_, 5, v_cache_2031_);
lean_ctor_set(v_reuseFailAlloc_2047_, 6, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2047_, 7, v_infoState_2033_);
lean_ctor_set(v_reuseFailAlloc_2047_, 8, v_snapshotTasks_2034_);
v___x_2043_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = lean_st_ref_set(v___y_2022_, v___x_2043_);
v___x_2045_ = lean_box(0);
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
return v___x_2046_;
}
}
}
v___jp_2049_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2073_; 
v___x_2058_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2005_);
v___x_2059_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(v___x_2058_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2073_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2073_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
lean_inc_ref_n(v___y_2051_, 2);
v___x_2064_ = l_Lean_FileMap_toPosition(v___y_2051_, v___y_2053_);
lean_dec(v___y_2053_);
v___x_2065_ = l_Lean_FileMap_toPosition(v___y_2051_, v___y_2057_);
lean_dec(v___y_2057_);
v___x_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
v___x_2067_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0));
if (v___y_2055_ == 0)
{
lean_del_object(v___x_2062_);
lean_dec_ref(v___y_2050_);
v___y_2014_ = v___y_2052_;
v___y_2015_ = v___x_2066_;
v___y_2016_ = v___x_2067_;
v___y_2017_ = v___y_2054_;
v___y_2018_ = v___y_2056_;
v___y_2019_ = v___x_2064_;
v___y_2020_ = v_a_2060_;
v___y_2021_ = v___y_2010_;
v___y_2022_ = v___y_2011_;
goto v___jp_2013_;
}
else
{
uint8_t v___x_2068_; 
lean_inc(v_a_2060_);
v___x_2068_ = l_Lean_MessageData_hasTag(v___y_2050_, v_a_2060_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; lean_object* v___x_2071_; 
lean_dec_ref(v___x_2066_);
lean_dec_ref(v___x_2064_);
lean_dec(v_a_2060_);
v___x_2069_ = lean_box(0);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v___x_2069_);
v___x_2071_ = v___x_2062_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
else
{
lean_del_object(v___x_2062_);
v___y_2014_ = v___y_2052_;
v___y_2015_ = v___x_2066_;
v___y_2016_ = v___x_2067_;
v___y_2017_ = v___y_2054_;
v___y_2018_ = v___y_2056_;
v___y_2019_ = v___x_2064_;
v___y_2020_ = v_a_2060_;
v___y_2021_ = v___y_2010_;
v___y_2022_ = v___y_2011_;
goto v___jp_2013_;
}
}
}
}
v___jp_2074_:
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Lean_Syntax_getTailPos_x3f(v___y_2079_, v___y_2077_);
lean_dec(v___y_2079_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_inc(v___y_2082_);
v___y_2050_ = v___y_2075_;
v___y_2051_ = v___y_2076_;
v___y_2052_ = v___y_2077_;
v___y_2053_ = v___y_2082_;
v___y_2054_ = v___y_2078_;
v___y_2055_ = v___y_2080_;
v___y_2056_ = v___y_2081_;
v___y_2057_ = v___y_2082_;
goto v___jp_2049_;
}
else
{
lean_object* v_val_2084_; 
v_val_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_val_2084_);
lean_dec_ref(v___x_2083_);
v___y_2050_ = v___y_2075_;
v___y_2051_ = v___y_2076_;
v___y_2052_ = v___y_2077_;
v___y_2053_ = v___y_2082_;
v___y_2054_ = v___y_2078_;
v___y_2055_ = v___y_2080_;
v___y_2056_ = v___y_2081_;
v___y_2057_ = v_val_2084_;
goto v___jp_2049_;
}
}
v___jp_2085_:
{
lean_object* v_ref_2093_; lean_object* v___x_2094_; 
v_ref_2093_ = l_Lean_replaceRef(v_ref_2004_, v___y_2089_);
v___x_2094_ = l_Lean_Syntax_getPos_x3f(v_ref_2093_, v___y_2088_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v___x_2095_; 
v___x_2095_ = lean_unsigned_to_nat(0u);
v___y_2075_ = v___y_2086_;
v___y_2076_ = v___y_2087_;
v___y_2077_ = v___y_2088_;
v___y_2078_ = v___y_2090_;
v___y_2079_ = v_ref_2093_;
v___y_2080_ = v___y_2091_;
v___y_2081_ = v___y_2092_;
v___y_2082_ = v___x_2095_;
goto v___jp_2074_;
}
else
{
lean_object* v_val_2096_; 
v_val_2096_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_val_2096_);
lean_dec_ref(v___x_2094_);
v___y_2075_ = v___y_2086_;
v___y_2076_ = v___y_2087_;
v___y_2077_ = v___y_2088_;
v___y_2078_ = v___y_2090_;
v___y_2079_ = v_ref_2093_;
v___y_2080_ = v___y_2091_;
v___y_2081_ = v___y_2092_;
v___y_2082_ = v_val_2096_;
goto v___jp_2074_;
}
}
v___jp_2098_:
{
if (v___y_2105_ == 0)
{
v___y_2086_ = v___y_2103_;
v___y_2087_ = v___y_2099_;
v___y_2088_ = v___y_2104_;
v___y_2089_ = v___y_2100_;
v___y_2090_ = v___y_2101_;
v___y_2091_ = v___y_2102_;
v___y_2092_ = v_severity_2006_;
goto v___jp_2085_;
}
else
{
v___y_2086_ = v___y_2103_;
v___y_2087_ = v___y_2099_;
v___y_2088_ = v___y_2104_;
v___y_2089_ = v___y_2100_;
v___y_2090_ = v___y_2101_;
v___y_2091_ = v___y_2102_;
v___y_2092_ = v___x_2097_;
goto v___jp_2085_;
}
}
v___jp_2106_:
{
if (v___y_2107_ == 0)
{
lean_object* v_fileName_2108_; lean_object* v_fileMap_2109_; lean_object* v_options_2110_; lean_object* v_ref_2111_; uint8_t v_suppressElabErrors_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___f_2115_; uint8_t v___x_2116_; uint8_t v___x_2117_; 
v_fileName_2108_ = lean_ctor_get(v___y_2010_, 0);
v_fileMap_2109_ = lean_ctor_get(v___y_2010_, 1);
v_options_2110_ = lean_ctor_get(v___y_2010_, 2);
v_ref_2111_ = lean_ctor_get(v___y_2010_, 5);
v_suppressElabErrors_2112_ = lean_ctor_get_uint8(v___y_2010_, sizeof(void*)*14 + 1);
v___x_2113_ = lean_box(v___y_2107_);
v___x_2114_ = lean_box(v_suppressElabErrors_2112_);
v___f_2115_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2115_, 0, v___x_2113_);
lean_closure_set(v___f_2115_, 1, v___x_2114_);
v___x_2116_ = 1;
v___x_2117_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2006_, v___x_2116_);
if (v___x_2117_ == 0)
{
v___y_2099_ = v_fileMap_2109_;
v___y_2100_ = v_ref_2111_;
v___y_2101_ = v_fileName_2108_;
v___y_2102_ = v_suppressElabErrors_2112_;
v___y_2103_ = v___f_2115_;
v___y_2104_ = v___y_2107_;
v___y_2105_ = v___x_2117_;
goto v___jp_2098_;
}
else
{
lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2118_ = l_Lean_warningAsError;
v___x_2119_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34(v_options_2110_, v___x_2118_);
v___y_2099_ = v_fileMap_2109_;
v___y_2100_ = v_ref_2111_;
v___y_2101_ = v_fileName_2108_;
v___y_2102_ = v_suppressElabErrors_2112_;
v___y_2103_ = v___f_2115_;
v___y_2104_ = v___y_2107_;
v___y_2105_ = v___x_2119_;
goto v___jp_2098_;
}
}
else
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
lean_dec_ref(v_msgData_2005_);
v___x_2120_ = lean_box(0);
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
return v___x_2121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___boxed(lean_object* v_ref_2124_, lean_object* v_msgData_2125_, lean_object* v_severity_2126_, lean_object* v_isSilent_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
uint8_t v_severity_boxed_2133_; uint8_t v_isSilent_boxed_2134_; lean_object* v_res_2135_; 
v_severity_boxed_2133_ = lean_unbox(v_severity_2126_);
v_isSilent_boxed_2134_ = lean_unbox(v_isSilent_2127_);
v_res_2135_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(v_ref_2124_, v_msgData_2125_, v_severity_boxed_2133_, v_isSilent_boxed_2134_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v_ref_2124_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(lean_object* v_msgData_2136_, uint8_t v_severity_2137_, uint8_t v_isSilent_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v_ref_2145_; lean_object* v___x_2146_; 
v_ref_2145_ = lean_ctor_get(v___y_2142_, 5);
v___x_2146_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(v_ref_2145_, v_msgData_2136_, v_severity_2137_, v_isSilent_2138_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24___boxed(lean_object* v_msgData_2147_, lean_object* v_severity_2148_, lean_object* v_isSilent_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
uint8_t v_severity_boxed_2156_; uint8_t v_isSilent_boxed_2157_; lean_object* v_res_2158_; 
v_severity_boxed_2156_ = lean_unbox(v_severity_2148_);
v_isSilent_boxed_2157_ = lean_unbox(v_isSilent_2149_);
v_res_2158_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(v_msgData_2147_, v_severity_boxed_2156_, v_isSilent_boxed_2157_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15(lean_object* v_msgData_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
uint8_t v___x_2166_; uint8_t v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = 1;
v___x_2167_ = 0;
v___x_2168_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(v_msgData_2159_, v___x_2166_, v___x_2167_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15___boxed(lean_object* v_msgData_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15(v_msgData_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
return v_res_2176_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__1(void){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__0));
v___x_2179_ = l_Lean_stringToMessageData(v___x_2178_);
return v___x_2179_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__4(void){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2185_ = lean_box(0);
v___x_2186_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__3));
v___x_2187_ = l_Lean_mkConst(v___x_2186_, v___x_2185_);
return v___x_2187_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__5(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__4, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__4_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__4);
v___x_2189_ = l_Lean_MessageData_ofExpr(v___x_2188_);
return v___x_2189_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__6(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__5, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__5_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__5);
v___x_2191_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__1, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__1_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__1);
v___x_2192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
lean_ctor_set(v___x_2192_, 1, v___x_2190_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize(lean_object* v_goal_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v___x_2200_; 
lean_inc(v_goal_2193_);
v___x_2200_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq(v_goal_2193_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref(v___x_2200_);
if (lean_obj_tag(v_a_2201_) == 1)
{
lean_object* v_val_2202_; lean_object* v_fst_2203_; lean_object* v_snd_2204_; lean_object* v___f_2205_; lean_object* v___x_2206_; 
v_val_2202_ = lean_ctor_get(v_a_2201_, 0);
lean_inc(v_val_2202_);
lean_dec_ref(v_a_2201_);
v_fst_2203_ = lean_ctor_get(v_val_2202_, 0);
lean_inc(v_fst_2203_);
v_snd_2204_ = lean_ctor_get(v_val_2202_, 1);
lean_inc(v_snd_2204_);
lean_dec(v_val_2202_);
lean_inc(v_goal_2193_);
v___f_2205_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___boxed), 9, 3);
lean_closure_set(v___f_2205_, 0, v_fst_2203_);
lean_closure_set(v___f_2205_, 1, v_snd_2204_);
lean_closure_set(v___f_2205_, 2, v_goal_2193_);
v___x_2206_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_goal_2193_, v___f_2205_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
return v___x_2206_;
}
else
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_dec(v_a_2201_);
v___x_2207_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__6);
v___x_2208_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15(v___x_2207_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2215_ == 0)
{
lean_object* v_unused_2216_; 
v_unused_2216_ = lean_ctor_get(v___x_2208_, 0);
lean_dec(v_unused_2216_);
v___x_2210_ = v___x_2208_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_dec(v___x_2208_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v_goal_2193_);
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_goal_2193_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec(v_goal_2193_);
v_a_2217_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2208_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2208_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec(v_goal_2193_);
v_a_2225_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2200_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2200_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___boxed(lean_object* v_goal_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize(v_goal_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_);
lean_dec(v_a_2238_);
lean_dec_ref(v_a_2237_);
lean_dec(v_a_2236_);
lean_dec_ref(v_a_2235_);
lean_dec(v_a_2234_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0(lean_object* v_00_u03b2_2241_, lean_object* v_m_2242_, lean_object* v_a_2243_, lean_object* v_b_2244_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(v_m_2242_, v_a_2243_, v_b_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2(lean_object* v_as_2246_, size_t v_sz_2247_, size_t v_i_2248_, lean_object* v_b_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(v_as_2246_, v_sz_2247_, v_i_2248_, v_b_2249_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2___boxed(lean_object* v_as_2257_, lean_object* v_sz_2258_, lean_object* v_i_2259_, lean_object* v_b_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
size_t v_sz_boxed_2267_; size_t v_i_boxed_2268_; lean_object* v_res_2269_; 
v_sz_boxed_2267_ = lean_unbox_usize(v_sz_2258_);
lean_dec(v_sz_2258_);
v_i_boxed_2268_ = lean_unbox_usize(v_i_2259_);
lean_dec(v_i_2259_);
v_res_2269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2(v_as_2257_, v_sz_boxed_2267_, v_i_boxed_2268_, v_b_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v_as_2257_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3(lean_object* v_00_u03b2_2270_, lean_object* v_m_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(v_m_2271_, v_a_2272_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3___boxed(lean_object* v_00_u03b2_2274_, lean_object* v_m_2275_, lean_object* v_a_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3(v_00_u03b2_2274_, v_m_2275_, v_a_2276_);
lean_dec_ref(v_a_2276_);
lean_dec_ref(v_m_2275_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12(lean_object* v_00_u03b1_2278_, lean_object* v_name_2279_, uint8_t v_bi_2280_, lean_object* v_type_2281_, lean_object* v_k_2282_, uint8_t v_kind_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(v_name_2279_, v_bi_2280_, v_type_2281_, v_k_2282_, v_kind_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___boxed(lean_object* v_00_u03b1_2291_, lean_object* v_name_2292_, lean_object* v_bi_2293_, lean_object* v_type_2294_, lean_object* v_k_2295_, lean_object* v_kind_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
uint8_t v_bi_boxed_2303_; uint8_t v_kind_boxed_2304_; lean_object* v_res_2305_; 
v_bi_boxed_2303_ = lean_unbox(v_bi_2293_);
v_kind_boxed_2304_ = lean_unbox(v_kind_2296_);
v_res_2305_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12(v_00_u03b1_2291_, v_name_2292_, v_bi_boxed_2303_, v_type_2294_, v_k_2295_, v_kind_boxed_2304_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6(lean_object* v_00_u03b1_2306_, lean_object* v_name_2307_, lean_object* v_type_2308_, lean_object* v_k_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v_name_2307_, v_type_2308_, v_k_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___boxed(lean_object* v_00_u03b1_2317_, lean_object* v_name_2318_, lean_object* v_type_2319_, lean_object* v_k_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6(v_00_u03b1_2317_, v_name_2318_, v_type_2319_, v_k_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7(lean_object* v_mvarId_2328_, lean_object* v_val_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(v_mvarId_2328_, v_val_2329_, v___y_2332_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___boxed(lean_object* v_mvarId_2337_, lean_object* v_val_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7(v_mvarId_2337_, v_val_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9(lean_object* v_00_u03b1_2346_, lean_object* v_msg_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(v_msg_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___boxed(lean_object* v_00_u03b1_2354_, lean_object* v_msg_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9(v_00_u03b1_2354_, v_msg_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
return v_res_2361_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0(lean_object* v_00_u03b2_2362_, lean_object* v_a_2363_, lean_object* v_x_2364_){
_start:
{
uint8_t v___x_2365_; 
v___x_2365_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_2363_, v_x_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2366_, lean_object* v_a_2367_, lean_object* v_x_2368_){
_start:
{
uint8_t v_res_2369_; lean_object* v_r_2370_; 
v_res_2369_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0(v_00_u03b2_2366_, v_a_2367_, v_x_2368_);
lean_dec(v_x_2368_);
lean_dec_ref(v_a_2367_);
v_r_2370_ = lean_box(v_res_2369_);
return v_r_2370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1(lean_object* v_00_u03b2_2371_, lean_object* v_data_2372_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(v_data_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2(lean_object* v_00_u03b2_2374_, lean_object* v_a_2375_, lean_object* v_b_2376_, lean_object* v_x_2377_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(v_a_2375_, v_b_2376_, v_x_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6(lean_object* v_00_u03b2_2379_, lean_object* v_a_2380_, lean_object* v_x_2381_){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(v_a_2380_, v_x_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2383_, lean_object* v_a_2384_, lean_object* v_x_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6(v_00_u03b2_2383_, v_a_2384_, v_x_2385_);
lean_dec(v_x_2385_);
lean_dec_ref(v_a_2384_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14(lean_object* v_00_u03b2_2387_, lean_object* v_x_2388_, lean_object* v_x_2389_, lean_object* v_x_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(v_x_2388_, v_x_2389_, v_x_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2392_, lean_object* v_i_2393_, lean_object* v_source_2394_, lean_object* v_target_2395_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3___redArg(v_i_2393_, v_source_2394_, v_target_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19(lean_object* v_00_u03b2_2397_, lean_object* v_x_2398_, size_t v_x_2399_, size_t v_x_2400_, lean_object* v_x_2401_, lean_object* v_x_2402_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_x_2398_, v_x_2399_, v_x_2400_, v_x_2401_, v_x_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___boxed(lean_object* v_00_u03b2_2404_, lean_object* v_x_2405_, lean_object* v_x_2406_, lean_object* v_x_2407_, lean_object* v_x_2408_, lean_object* v_x_2409_){
_start:
{
size_t v_x_23590__boxed_2410_; size_t v_x_23591__boxed_2411_; lean_object* v_res_2412_; 
v_x_23590__boxed_2410_ = lean_unbox_usize(v_x_2406_);
lean_dec(v_x_2406_);
v_x_23591__boxed_2411_ = lean_unbox_usize(v_x_2407_);
lean_dec(v_x_2407_);
v_res_2412_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19(v_00_u03b2_2404_, v_x_2405_, v_x_23590__boxed_2410_, v_x_23591__boxed_2411_, v_x_2408_, v_x_2409_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29(lean_object* v_ref_2413_, lean_object* v_msgData_2414_, uint8_t v_severity_2415_, uint8_t v_isSilent_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(v_ref_2413_, v_msgData_2414_, v_severity_2415_, v_isSilent_2416_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___boxed(lean_object* v_ref_2424_, lean_object* v_msgData_2425_, lean_object* v_severity_2426_, lean_object* v_isSilent_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
uint8_t v_severity_boxed_2434_; uint8_t v_isSilent_boxed_2435_; lean_object* v_res_2436_; 
v_severity_boxed_2434_ = lean_unbox(v_severity_2426_);
v_isSilent_boxed_2435_ = lean_unbox(v_isSilent_2427_);
v_res_2436_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29(v_ref_2424_, v_msgData_2425_, v_severity_boxed_2434_, v_isSilent_boxed_2435_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec(v_ref_2424_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20(lean_object* v_00_u03b2_2437_, lean_object* v_x_2438_, lean_object* v_x_2439_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20___redArg(v_x_2438_, v_x_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30(lean_object* v_00_u03b2_2441_, lean_object* v_n_2442_, lean_object* v_k_2443_, lean_object* v_v_2444_){
_start:
{
lean_object* v___x_2445_; 
v___x_2445_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30___redArg(v_n_2442_, v_k_2443_, v_v_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31(lean_object* v_00_u03b2_2446_, size_t v_depth_2447_, lean_object* v_keys_2448_, lean_object* v_vals_2449_, lean_object* v_heq_2450_, lean_object* v_i_2451_, lean_object* v_entries_2452_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(v_depth_2447_, v_keys_2448_, v_vals_2449_, v_i_2451_, v_entries_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___boxed(lean_object* v_00_u03b2_2454_, lean_object* v_depth_2455_, lean_object* v_keys_2456_, lean_object* v_vals_2457_, lean_object* v_heq_2458_, lean_object* v_i_2459_, lean_object* v_entries_2460_){
_start:
{
size_t v_depth_boxed_2461_; lean_object* v_res_2462_; 
v_depth_boxed_2461_ = lean_unbox_usize(v_depth_2455_);
lean_dec(v_depth_2455_);
v_res_2462_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31(v_00_u03b2_2454_, v_depth_boxed_2461_, v_keys_2456_, v_vals_2457_, v_heq_2458_, v_i_2459_, v_entries_2460_);
lean_dec_ref(v_vals_2457_);
lean_dec_ref(v_keys_2456_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32(lean_object* v_00_u03b2_2463_, lean_object* v_x_2464_, lean_object* v_x_2465_, lean_object* v_x_2466_, lean_object* v_x_2467_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32___redArg(v_x_2464_, v_x_2465_, v_x_2466_, v_x_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___redArg(lean_object* v_e_2469_, lean_object* v___y_2470_){
_start:
{
uint8_t v___x_2472_; 
v___x_2472_ = l_Lean_Expr_hasMVar(v_e_2469_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2473_, 0, v_e_2469_);
return v___x_2473_;
}
else
{
lean_object* v___x_2474_; lean_object* v_mctx_2475_; lean_object* v___x_2476_; lean_object* v_fst_2477_; lean_object* v_snd_2478_; lean_object* v___x_2479_; lean_object* v_cache_2480_; lean_object* v_zetaDeltaFVarIds_2481_; lean_object* v_postponed_2482_; lean_object* v_diag_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2492_; 
v___x_2474_ = lean_st_ref_get(v___y_2470_);
v_mctx_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc_ref(v_mctx_2475_);
lean_dec(v___x_2474_);
v___x_2476_ = l_Lean_instantiateMVarsCore(v_mctx_2475_, v_e_2469_);
v_fst_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_fst_2477_);
v_snd_2478_ = lean_ctor_get(v___x_2476_, 1);
lean_inc(v_snd_2478_);
lean_dec_ref(v___x_2476_);
v___x_2479_ = lean_st_ref_take(v___y_2470_);
v_cache_2480_ = lean_ctor_get(v___x_2479_, 1);
v_zetaDeltaFVarIds_2481_ = lean_ctor_get(v___x_2479_, 2);
v_postponed_2482_ = lean_ctor_get(v___x_2479_, 3);
v_diag_2483_ = lean_ctor_get(v___x_2479_, 4);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2492_ == 0)
{
lean_object* v_unused_2493_; 
v_unused_2493_ = lean_ctor_get(v___x_2479_, 0);
lean_dec(v_unused_2493_);
v___x_2485_ = v___x_2479_;
v_isShared_2486_ = v_isSharedCheck_2492_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_diag_2483_);
lean_inc(v_postponed_2482_);
lean_inc(v_zetaDeltaFVarIds_2481_);
lean_inc(v_cache_2480_);
lean_dec(v___x_2479_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2492_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v_snd_2478_);
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_snd_2478_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_cache_2480_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_zetaDeltaFVarIds_2481_);
lean_ctor_set(v_reuseFailAlloc_2491_, 3, v_postponed_2482_);
lean_ctor_set(v_reuseFailAlloc_2491_, 4, v_diag_2483_);
v___x_2488_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = lean_st_ref_set(v___y_2470_, v___x_2488_);
v___x_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2490_, 0, v_fst_2477_);
return v___x_2490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___redArg___boxed(lean_object* v_e_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___redArg(v_e_2494_, v___y_2495_);
lean_dec(v___y_2495_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2(lean_object* v_e_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___redArg(v_e_2498_, v___y_2501_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___boxed(lean_object* v_e_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2(v_e_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
return v_res_2513_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(lean_object* v_m_2514_, lean_object* v_a_2515_){
_start:
{
lean_object* v_buckets_2516_; lean_object* v___x_2517_; uint64_t v___x_2518_; uint64_t v___x_2519_; uint64_t v___x_2520_; uint64_t v_fold_2521_; uint64_t v___x_2522_; uint64_t v___x_2523_; uint64_t v___x_2524_; size_t v___x_2525_; size_t v___x_2526_; size_t v___x_2527_; size_t v___x_2528_; size_t v___x_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v_buckets_2516_ = lean_ctor_get(v_m_2514_, 1);
v___x_2517_ = lean_array_get_size(v_buckets_2516_);
v___x_2518_ = l_Lean_Expr_hash(v_a_2515_);
v___x_2519_ = 32ULL;
v___x_2520_ = lean_uint64_shift_right(v___x_2518_, v___x_2519_);
v_fold_2521_ = lean_uint64_xor(v___x_2518_, v___x_2520_);
v___x_2522_ = 16ULL;
v___x_2523_ = lean_uint64_shift_right(v_fold_2521_, v___x_2522_);
v___x_2524_ = lean_uint64_xor(v_fold_2521_, v___x_2523_);
v___x_2525_ = lean_uint64_to_usize(v___x_2524_);
v___x_2526_ = lean_usize_of_nat(v___x_2517_);
v___x_2527_ = ((size_t)1ULL);
v___x_2528_ = lean_usize_sub(v___x_2526_, v___x_2527_);
v___x_2529_ = lean_usize_land(v___x_2525_, v___x_2528_);
v___x_2530_ = lean_array_uget_borrowed(v_buckets_2516_, v___x_2529_);
v___x_2531_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_2515_, v___x_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg___boxed(lean_object* v_m_2532_, lean_object* v_a_2533_){
_start:
{
uint8_t v_res_2534_; lean_object* v_r_2535_; 
v_res_2534_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(v_m_2532_, v_a_2533_);
lean_dec_ref(v_a_2533_);
lean_dec_ref(v_m_2532_);
v_r_2535_ = lean_box(v_res_2534_);
return v_r_2535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__0___redArg(lean_object* v_m_2536_, lean_object* v_a_2537_, lean_object* v_b_2538_){
_start:
{
lean_object* v_size_2539_; lean_object* v_buckets_2540_; lean_object* v___x_2541_; uint64_t v___x_2542_; uint64_t v___x_2543_; uint64_t v___x_2544_; uint64_t v_fold_2545_; uint64_t v___x_2546_; uint64_t v___x_2547_; uint64_t v___x_2548_; size_t v___x_2549_; size_t v___x_2550_; size_t v___x_2551_; size_t v___x_2552_; size_t v___x_2553_; lean_object* v_bkt_2554_; uint8_t v___x_2555_; 
v_size_2539_ = lean_ctor_get(v_m_2536_, 0);
v_buckets_2540_ = lean_ctor_get(v_m_2536_, 1);
v___x_2541_ = lean_array_get_size(v_buckets_2540_);
v___x_2542_ = l_Lean_Expr_hash(v_a_2537_);
v___x_2543_ = 32ULL;
v___x_2544_ = lean_uint64_shift_right(v___x_2542_, v___x_2543_);
v_fold_2545_ = lean_uint64_xor(v___x_2542_, v___x_2544_);
v___x_2546_ = 16ULL;
v___x_2547_ = lean_uint64_shift_right(v_fold_2545_, v___x_2546_);
v___x_2548_ = lean_uint64_xor(v_fold_2545_, v___x_2547_);
v___x_2549_ = lean_uint64_to_usize(v___x_2548_);
v___x_2550_ = lean_usize_of_nat(v___x_2541_);
v___x_2551_ = ((size_t)1ULL);
v___x_2552_ = lean_usize_sub(v___x_2550_, v___x_2551_);
v___x_2553_ = lean_usize_land(v___x_2549_, v___x_2552_);
v_bkt_2554_ = lean_array_uget_borrowed(v_buckets_2540_, v___x_2553_);
v___x_2555_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_2537_, v_bkt_2554_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2576_; 
lean_inc_ref(v_buckets_2540_);
lean_inc(v_size_2539_);
v_isSharedCheck_2576_ = !lean_is_exclusive(v_m_2536_);
if (v_isSharedCheck_2576_ == 0)
{
lean_object* v_unused_2577_; lean_object* v_unused_2578_; 
v_unused_2577_ = lean_ctor_get(v_m_2536_, 1);
lean_dec(v_unused_2577_);
v_unused_2578_ = lean_ctor_get(v_m_2536_, 0);
lean_dec(v_unused_2578_);
v___x_2557_ = v_m_2536_;
v_isShared_2558_ = v_isSharedCheck_2576_;
goto v_resetjp_2556_;
}
else
{
lean_dec(v_m_2536_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2576_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2559_; lean_object* v_size_x27_2560_; lean_object* v___x_2561_; lean_object* v_buckets_x27_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; uint8_t v___x_2568_; 
v___x_2559_ = lean_unsigned_to_nat(1u);
v_size_x27_2560_ = lean_nat_add(v_size_2539_, v___x_2559_);
lean_dec(v_size_2539_);
lean_inc(v_bkt_2554_);
v___x_2561_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2561_, 0, v_a_2537_);
lean_ctor_set(v___x_2561_, 1, v_b_2538_);
lean_ctor_set(v___x_2561_, 2, v_bkt_2554_);
v_buckets_x27_2562_ = lean_array_uset(v_buckets_2540_, v___x_2553_, v___x_2561_);
v___x_2563_ = lean_unsigned_to_nat(4u);
v___x_2564_ = lean_nat_mul(v_size_x27_2560_, v___x_2563_);
v___x_2565_ = lean_unsigned_to_nat(3u);
v___x_2566_ = lean_nat_div(v___x_2564_, v___x_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_array_get_size(v_buckets_x27_2562_);
v___x_2568_ = lean_nat_dec_le(v___x_2566_, v___x_2567_);
lean_dec(v___x_2566_);
if (v___x_2568_ == 0)
{
lean_object* v_val_2569_; lean_object* v___x_2571_; 
v_val_2569_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(v_buckets_x27_2562_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 1, v_val_2569_);
lean_ctor_set(v___x_2557_, 0, v_size_x27_2560_);
v___x_2571_ = v___x_2557_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_size_x27_2560_);
lean_ctor_set(v_reuseFailAlloc_2572_, 1, v_val_2569_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
else
{
lean_object* v___x_2574_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 1, v_buckets_x27_2562_);
lean_ctor_set(v___x_2557_, 0, v_size_x27_2560_);
v___x_2574_ = v___x_2557_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_size_x27_2560_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_buckets_x27_2562_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
else
{
lean_dec(v_b_2538_);
lean_dec_ref(v_a_2537_);
return v_m_2536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(lean_object* v_e_2579_, lean_object* v_a_2580_){
_start:
{
lean_object* v___x_2582_; lean_object* v_checked_2583_; uint8_t v___x_2584_; 
v___x_2582_ = lean_st_ref_get(v_a_2580_);
v_checked_2583_ = lean_ctor_get(v___x_2582_, 1);
lean_inc_ref(v_checked_2583_);
lean_dec(v___x_2582_);
v___x_2584_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(v_checked_2583_, v_e_2579_);
lean_dec_ref(v_checked_2583_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; lean_object* v_visited_2586_; lean_object* v_checked_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2599_; 
v___x_2585_ = lean_st_ref_take(v_a_2580_);
v_visited_2586_ = lean_ctor_get(v___x_2585_, 0);
v_checked_2587_ = lean_ctor_get(v___x_2585_, 1);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2589_ = v___x_2585_;
v_isShared_2590_ = v_isSharedCheck_2599_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_checked_2587_);
lean_inc(v_visited_2586_);
lean_dec(v___x_2585_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2599_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2594_; 
v___x_2591_ = lean_box(0);
v___x_2592_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__0___redArg(v_checked_2587_, v_e_2579_, v___x_2591_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 1, v___x_2592_);
v___x_2594_ = v___x_2589_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_visited_2586_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2595_ = lean_st_ref_set(v_a_2580_, v___x_2594_);
v___x_2596_ = lean_box(v___x_2584_);
v___x_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
return v___x_2597_;
}
}
}
else
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_dec_ref(v_e_2579_);
v___x_2600_ = lean_box(v___x_2584_);
v___x_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
return v___x_2601_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_e_2602_, lean_object* v_a_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(v_e_2602_, v_a_2603_);
lean_dec(v_a_2603_);
return v_res_2605_;
}
}
static size_t _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0(void){
_start:
{
size_t v___x_2606_; size_t v___x_2607_; size_t v___x_2608_; 
v___x_2606_ = ((size_t)1ULL);
v___x_2607_ = ((size_t)8192ULL);
v___x_2608_ = lean_usize_sub(v___x_2607_, v___x_2606_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(lean_object* v_e_2609_, lean_object* v_a_2610_){
_start:
{
lean_object* v___x_2612_; lean_object* v_visited_2613_; size_t v___x_2614_; size_t v___x_2615_; size_t v___x_2616_; lean_object* v___x_2617_; size_t v___x_2618_; uint8_t v___x_2619_; 
v___x_2612_ = lean_st_ref_get(v_a_2610_);
v_visited_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc_ref(v_visited_2613_);
lean_dec(v___x_2612_);
v___x_2614_ = lean_ptr_addr(v_e_2609_);
v___x_2615_ = lean_usize_once(&l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0, &l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0);
v___x_2616_ = lean_usize_mod(v___x_2614_, v___x_2615_);
v___x_2617_ = lean_array_uget(v_visited_2613_, v___x_2616_);
lean_dec_ref(v_visited_2613_);
v___x_2618_ = lean_ptr_addr(v___x_2617_);
lean_dec(v___x_2617_);
v___x_2619_ = lean_usize_dec_eq(v___x_2618_, v___x_2614_);
if (v___x_2619_ == 0)
{
lean_object* v___x_2620_; lean_object* v_visited_2621_; lean_object* v_checked_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2633_; 
v___x_2620_ = lean_st_ref_take(v_a_2610_);
v_visited_2621_ = lean_ctor_get(v___x_2620_, 0);
v_checked_2622_ = lean_ctor_get(v___x_2620_, 1);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2624_ = v___x_2620_;
v_isShared_2625_ = v_isSharedCheck_2633_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_checked_2622_);
lean_inc(v_visited_2621_);
lean_dec(v___x_2620_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2633_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2626_; lean_object* v___x_2628_; 
v___x_2626_ = lean_array_uset(v_visited_2621_, v___x_2616_, v_e_2609_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 0, v___x_2626_);
v___x_2628_ = v___x_2624_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2626_);
lean_ctor_set(v_reuseFailAlloc_2632_, 1, v_checked_2622_);
v___x_2628_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = lean_st_ref_set(v_a_2610_, v___x_2628_);
v___x_2630_ = lean_box(v___x_2619_);
v___x_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
return v___x_2631_;
}
}
}
else
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_dec_ref(v_e_2609_);
v___x_2634_ = lean_box(v___x_2619_);
v___x_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2634_);
return v___x_2635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_e_2636_, lean_object* v_a_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(v_e_2636_, v_a_2637_);
lean_dec(v_a_2637_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(lean_object* v_p_2640_, lean_object* v_f_2641_, uint8_t v_stopWhenVisited_2642_, lean_object* v_e_2643_, lean_object* v_a_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v_d_2657_; lean_object* v_b_2658_; lean_object* v___y_2659_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___x_2689_; 
lean_inc_ref(v_e_2643_);
v___x_2689_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(v_e_2643_, v_a_2644_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2722_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2692_ = v___x_2689_;
v_isShared_2693_ = v_isSharedCheck_2722_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2689_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2722_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
uint8_t v___x_2694_; 
v___x_2694_ = lean_unbox(v_a_2690_);
lean_dec(v_a_2690_);
if (v___x_2694_ == 0)
{
lean_object* v___x_2695_; uint8_t v___x_2696_; 
lean_del_object(v___x_2692_);
lean_inc_ref(v_p_2640_);
lean_inc_ref(v_e_2643_);
v___x_2695_ = lean_apply_1(v_p_2640_, v_e_2643_);
v___x_2696_ = lean_unbox(v___x_2695_);
if (v___x_2696_ == 0)
{
v___y_2663_ = v_a_2644_;
v___y_2664_ = v___y_2645_;
v___y_2665_ = v___y_2646_;
v___y_2666_ = v___y_2647_;
v___y_2667_ = v___y_2648_;
v___y_2668_ = v___y_2649_;
goto v___jp_2662_;
}
else
{
lean_object* v___x_2697_; 
lean_inc_ref(v_e_2643_);
v___x_2697_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(v_e_2643_, v_a_2644_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; uint8_t v___x_2699_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref(v___x_2697_);
v___x_2699_ = lean_unbox(v_a_2698_);
lean_dec(v_a_2698_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2700_; 
lean_inc_ref(v_f_2641_);
lean_inc(v___y_2649_);
lean_inc_ref(v___y_2648_);
lean_inc(v___y_2647_);
lean_inc_ref(v___y_2646_);
lean_inc(v___y_2645_);
lean_inc_ref(v_e_2643_);
v___x_2700_ = lean_apply_7(v_f_2641_, v_e_2643_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, lean_box(0));
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2708_; 
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2708_ == 0)
{
lean_object* v_unused_2709_; 
v_unused_2709_ = lean_ctor_get(v___x_2700_, 0);
lean_dec(v_unused_2709_);
v___x_2702_ = v___x_2700_;
v_isShared_2703_ = v_isSharedCheck_2708_;
goto v_resetjp_2701_;
}
else
{
lean_dec(v___x_2700_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2708_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
if (v_stopWhenVisited_2642_ == 0)
{
lean_del_object(v___x_2702_);
v___y_2663_ = v_a_2644_;
v___y_2664_ = v___y_2645_;
v___y_2665_ = v___y_2646_;
v___y_2666_ = v___y_2647_;
v___y_2667_ = v___y_2648_;
v___y_2668_ = v___y_2649_;
goto v___jp_2662_;
}
else
{
lean_object* v___x_2704_; lean_object* v___x_2706_; 
lean_dec_ref(v_e_2643_);
lean_dec_ref(v_f_2641_);
lean_dec_ref(v_p_2640_);
v___x_2704_ = lean_box(0);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 0, v___x_2704_);
v___x_2706_ = v___x_2702_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
else
{
lean_dec_ref(v_e_2643_);
lean_dec_ref(v_f_2641_);
lean_dec_ref(v_p_2640_);
return v___x_2700_;
}
}
else
{
v___y_2663_ = v_a_2644_;
v___y_2664_ = v___y_2645_;
v___y_2665_ = v___y_2646_;
v___y_2666_ = v___y_2647_;
v___y_2667_ = v___y_2648_;
v___y_2668_ = v___y_2649_;
goto v___jp_2662_;
}
}
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
lean_dec_ref(v_e_2643_);
lean_dec_ref(v_f_2641_);
lean_dec_ref(v_p_2640_);
v_a_2710_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2697_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2697_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
}
else
{
lean_object* v___x_2718_; lean_object* v___x_2720_; 
lean_dec_ref(v_e_2643_);
lean_dec_ref(v_f_2641_);
lean_dec_ref(v_p_2640_);
v___x_2718_ = lean_box(0);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v___x_2718_);
v___x_2720_ = v___x_2692_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2718_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_dec_ref(v_e_2643_);
lean_dec_ref(v_f_2641_);
lean_dec_ref(v_p_2640_);
v_a_2723_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2689_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2689_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
v___jp_2651_:
{
lean_object* v___x_2660_; 
lean_inc_ref(v_f_2641_);
lean_inc_ref(v_p_2640_);
v___x_2660_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2640_, v_f_2641_, v_stopWhenVisited_2642_, v_d_2657_, v___y_2659_, v___y_2656_, v___y_2654_, v___y_2652_, v___y_2653_, v___y_2655_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_dec_ref(v___x_2660_);
v_e_2643_ = v_b_2658_;
v_a_2644_ = v___y_2659_;
v___y_2645_ = v___y_2656_;
v___y_2646_ = v___y_2654_;
v___y_2647_ = v___y_2652_;
v___y_2648_ = v___y_2653_;
v___y_2649_ = v___y_2655_;
goto _start;
}
else
{
lean_dec_ref(v_b_2658_);
lean_dec_ref(v_f_2641_);
lean_dec_ref(v_p_2640_);
return v___x_2660_;
}
}
v___jp_2662_:
{
switch(lean_obj_tag(v_e_2643_))
{
case 7:
{
lean_object* v_binderType_2669_; lean_object* v_body_2670_; 
v_binderType_2669_ = lean_ctor_get(v_e_2643_, 1);
lean_inc_ref(v_binderType_2669_);
v_body_2670_ = lean_ctor_get(v_e_2643_, 2);
lean_inc_ref(v_body_2670_);
lean_dec_ref(v_e_2643_);
v___y_2652_ = v___y_2666_;
v___y_2653_ = v___y_2667_;
v___y_2654_ = v___y_2665_;
v___y_2655_ = v___y_2668_;
v___y_2656_ = v___y_2664_;
v_d_2657_ = v_binderType_2669_;
v_b_2658_ = v_body_2670_;
v___y_2659_ = v___y_2663_;
goto v___jp_2651_;
}
case 6:
{
lean_object* v_binderType_2671_; lean_object* v_body_2672_; 
v_binderType_2671_ = lean_ctor_get(v_e_2643_, 1);
lean_inc_ref(v_binderType_2671_);
v_body_2672_ = lean_ctor_get(v_e_2643_, 2);
lean_inc_ref(v_body_2672_);
lean_dec_ref(v_e_2643_);
v___y_2652_ = v___y_2666_;
v___y_2653_ = v___y_2667_;
v___y_2654_ = v___y_2665_;
v___y_2655_ = v___y_2668_;
v___y_2656_ = v___y_2664_;
v_d_2657_ = v_binderType_2671_;
v_b_2658_ = v_body_2672_;
v___y_2659_ = v___y_2663_;
goto v___jp_2651_;
}
case 8:
{
lean_object* v_type_2673_; lean_object* v_value_2674_; lean_object* v_body_2675_; lean_object* v___x_2676_; 
v_type_2673_ = lean_ctor_get(v_e_2643_, 1);
lean_inc_ref(v_type_2673_);
v_value_2674_ = lean_ctor_get(v_e_2643_, 2);
lean_inc_ref(v_value_2674_);
v_body_2675_ = lean_ctor_get(v_e_2643_, 3);
lean_inc_ref(v_body_2675_);
lean_dec_ref(v_e_2643_);
lean_inc_ref(v_f_2641_);
lean_inc_ref(v_p_2640_);
v___x_2676_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2640_, v_f_2641_, v_stopWhenVisited_2642_, v_type_2673_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v___x_2677_; 
lean_dec_ref(v___x_2676_);
lean_inc_ref(v_f_2641_);
lean_inc_ref(v_p_2640_);
v___x_2677_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2640_, v_f_2641_, v_stopWhenVisited_2642_, v_value_2674_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_dec_ref(v___x_2677_);
v_e_2643_ = v_body_2675_;
v_a_2644_ = v___y_2663_;
v___y_2645_ = v___y_2664_;
v___y_2646_ = v___y_2665_;
v___y_2647_ = v___y_2666_;
v___y_2648_ = v___y_2667_;
v___y_2649_ = v___y_2668_;
goto _start;
}
else
{
lean_dec_ref(v_body_2675_);
lean_dec_ref(v_f_2641_);
lean_dec_ref(v_p_2640_);
return v___x_2677_;
}
}
else
{
lean_dec_ref(v_body_2675_);
lean_dec_ref(v_value_2674_);
lean_dec_ref(v_f_2641_);
lean_dec_ref(v_p_2640_);
return v___x_2676_;
}
}
case 5:
{
lean_object* v_fn_2679_; lean_object* v_arg_2680_; lean_object* v___x_2681_; 
v_fn_2679_ = lean_ctor_get(v_e_2643_, 0);
lean_inc_ref(v_fn_2679_);
v_arg_2680_ = lean_ctor_get(v_e_2643_, 1);
lean_inc_ref(v_arg_2680_);
lean_dec_ref(v_e_2643_);
lean_inc_ref(v_f_2641_);
lean_inc_ref(v_p_2640_);
v___x_2681_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2640_, v_f_2641_, v_stopWhenVisited_2642_, v_fn_2679_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_dec_ref(v___x_2681_);
v_e_2643_ = v_arg_2680_;
v_a_2644_ = v___y_2663_;
v___y_2645_ = v___y_2664_;
v___y_2646_ = v___y_2665_;
v___y_2647_ = v___y_2666_;
v___y_2648_ = v___y_2667_;
v___y_2649_ = v___y_2668_;
goto _start;
}
else
{
lean_dec_ref(v_arg_2680_);
lean_dec_ref(v_f_2641_);
lean_dec_ref(v_p_2640_);
return v___x_2681_;
}
}
case 10:
{
lean_object* v_expr_2683_; 
v_expr_2683_ = lean_ctor_get(v_e_2643_, 1);
lean_inc_ref(v_expr_2683_);
lean_dec_ref(v_e_2643_);
v_e_2643_ = v_expr_2683_;
v_a_2644_ = v___y_2663_;
v___y_2645_ = v___y_2664_;
v___y_2646_ = v___y_2665_;
v___y_2647_ = v___y_2666_;
v___y_2648_ = v___y_2667_;
v___y_2649_ = v___y_2668_;
goto _start;
}
case 11:
{
lean_object* v_struct_2685_; 
v_struct_2685_ = lean_ctor_get(v_e_2643_, 2);
lean_inc_ref(v_struct_2685_);
lean_dec_ref(v_e_2643_);
v_e_2643_ = v_struct_2685_;
v_a_2644_ = v___y_2663_;
v___y_2645_ = v___y_2664_;
v___y_2646_ = v___y_2665_;
v___y_2647_ = v___y_2666_;
v___y_2648_ = v___y_2667_;
v___y_2649_ = v___y_2668_;
goto _start;
}
default: 
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
lean_dec_ref(v_e_2643_);
lean_dec_ref(v_f_2641_);
lean_dec_ref(v_p_2640_);
v___x_2687_ = lean_box(0);
v___x_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2687_);
return v___x_2688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5___boxed(lean_object* v_p_2731_, lean_object* v_f_2732_, lean_object* v_stopWhenVisited_2733_, lean_object* v_e_2734_, lean_object* v_a_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
uint8_t v_stopWhenVisited_boxed_2742_; lean_object* v_res_2743_; 
v_stopWhenVisited_boxed_2742_ = lean_unbox(v_stopWhenVisited_2733_);
v_res_2743_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2731_, v_f_2732_, v_stopWhenVisited_boxed_2742_, v_e_2734_, v_a_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec(v_a_2735_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3(lean_object* v_p_2744_, lean_object* v_f_2745_, lean_object* v_e_2746_, uint8_t v_stopWhenVisited_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2754_ = l_Lean_ForEachExprWhere_initCache;
v___x_2755_ = lean_st_mk_ref(v___x_2754_);
v___x_2756_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2744_, v_f_2745_, v_stopWhenVisited_2747_, v_e_2746_, v___x_2755_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2765_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2759_ = v___x_2756_;
v_isShared_2760_ = v_isSharedCheck_2765_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2756_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2765_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2761_; lean_object* v___x_2763_; 
v___x_2761_ = lean_st_ref_get(v___x_2755_);
lean_dec(v___x_2755_);
lean_dec(v___x_2761_);
if (v_isShared_2760_ == 0)
{
v___x_2763_ = v___x_2759_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2757_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
else
{
lean_dec(v___x_2755_);
return v___x_2756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3___boxed(lean_object* v_p_2766_, lean_object* v_f_2767_, lean_object* v_e_2768_, lean_object* v_stopWhenVisited_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
uint8_t v_stopWhenVisited_boxed_2776_; lean_object* v_res_2777_; 
v_stopWhenVisited_boxed_2776_ = lean_unbox(v_stopWhenVisited_2769_);
v_res_2777_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3(v_p_2766_, v_f_2767_, v_e_2768_, v_stopWhenVisited_boxed_2776_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
return v_res_2777_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(lean_object* v_a_2778_, lean_object* v_x_2779_){
_start:
{
if (lean_obj_tag(v_x_2779_) == 0)
{
uint8_t v___x_2780_; 
v___x_2780_ = 0;
return v___x_2780_;
}
else
{
lean_object* v_key_2781_; lean_object* v_tail_2782_; uint8_t v___x_2783_; 
v_key_2781_ = lean_ctor_get(v_x_2779_, 0);
v_tail_2782_ = lean_ctor_get(v_x_2779_, 2);
v___x_2783_ = l_Lean_instBEqFVarId_beq(v_key_2781_, v_a_2778_);
if (v___x_2783_ == 0)
{
v_x_2779_ = v_tail_2782_;
goto _start;
}
else
{
return v___x_2783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg___boxed(lean_object* v_a_2785_, lean_object* v_x_2786_){
_start:
{
uint8_t v_res_2787_; lean_object* v_r_2788_; 
v_res_2787_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(v_a_2785_, v_x_2786_);
lean_dec(v_x_2786_);
lean_dec(v_a_2785_);
v_r_2788_ = lean_box(v_res_2787_);
return v_r_2788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_2789_, lean_object* v_x_2790_){
_start:
{
if (lean_obj_tag(v_x_2790_) == 0)
{
return v_x_2789_;
}
else
{
lean_object* v_key_2791_; lean_object* v_value_2792_; lean_object* v_tail_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2816_; 
v_key_2791_ = lean_ctor_get(v_x_2790_, 0);
v_value_2792_ = lean_ctor_get(v_x_2790_, 1);
v_tail_2793_ = lean_ctor_get(v_x_2790_, 2);
v_isSharedCheck_2816_ = !lean_is_exclusive(v_x_2790_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2795_ = v_x_2790_;
v_isShared_2796_ = v_isSharedCheck_2816_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_tail_2793_);
lean_inc(v_value_2792_);
lean_inc(v_key_2791_);
lean_dec(v_x_2790_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2816_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2797_; uint64_t v___x_2798_; uint64_t v___x_2799_; uint64_t v___x_2800_; uint64_t v_fold_2801_; uint64_t v___x_2802_; uint64_t v___x_2803_; uint64_t v___x_2804_; size_t v___x_2805_; size_t v___x_2806_; size_t v___x_2807_; size_t v___x_2808_; size_t v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2797_ = lean_array_get_size(v_x_2789_);
v___x_2798_ = l_Lean_instHashableFVarId_hash(v_key_2791_);
v___x_2799_ = 32ULL;
v___x_2800_ = lean_uint64_shift_right(v___x_2798_, v___x_2799_);
v_fold_2801_ = lean_uint64_xor(v___x_2798_, v___x_2800_);
v___x_2802_ = 16ULL;
v___x_2803_ = lean_uint64_shift_right(v_fold_2801_, v___x_2802_);
v___x_2804_ = lean_uint64_xor(v_fold_2801_, v___x_2803_);
v___x_2805_ = lean_uint64_to_usize(v___x_2804_);
v___x_2806_ = lean_usize_of_nat(v___x_2797_);
v___x_2807_ = ((size_t)1ULL);
v___x_2808_ = lean_usize_sub(v___x_2806_, v___x_2807_);
v___x_2809_ = lean_usize_land(v___x_2805_, v___x_2808_);
v___x_2810_ = lean_array_uget_borrowed(v_x_2789_, v___x_2809_);
lean_inc(v___x_2810_);
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 2, v___x_2810_);
v___x_2812_ = v___x_2795_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_key_2791_);
lean_ctor_set(v_reuseFailAlloc_2815_, 1, v_value_2792_);
lean_ctor_set(v_reuseFailAlloc_2815_, 2, v___x_2810_);
v___x_2812_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
lean_object* v___x_2813_; 
v___x_2813_ = lean_array_uset(v_x_2789_, v___x_2809_, v___x_2812_);
v_x_2789_ = v___x_2813_;
v_x_2790_ = v_tail_2793_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4___redArg(lean_object* v_i_2817_, lean_object* v_source_2818_, lean_object* v_target_2819_){
_start:
{
lean_object* v___x_2820_; uint8_t v___x_2821_; 
v___x_2820_ = lean_array_get_size(v_source_2818_);
v___x_2821_ = lean_nat_dec_lt(v_i_2817_, v___x_2820_);
if (v___x_2821_ == 0)
{
lean_dec_ref(v_source_2818_);
lean_dec(v_i_2817_);
return v_target_2819_;
}
else
{
lean_object* v_es_2822_; lean_object* v___x_2823_; lean_object* v_source_2824_; lean_object* v_target_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v_es_2822_ = lean_array_fget(v_source_2818_, v_i_2817_);
v___x_2823_ = lean_box(0);
v_source_2824_ = lean_array_fset(v_source_2818_, v_i_2817_, v___x_2823_);
v_target_2825_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(v_target_2819_, v_es_2822_);
v___x_2826_ = lean_unsigned_to_nat(1u);
v___x_2827_ = lean_nat_add(v_i_2817_, v___x_2826_);
lean_dec(v_i_2817_);
v_i_2817_ = v___x_2827_;
v_source_2818_ = v_source_2824_;
v_target_2819_ = v_target_2825_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2___redArg(lean_object* v_data_2829_){
_start:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v_nbuckets_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2830_ = lean_array_get_size(v_data_2829_);
v___x_2831_ = lean_unsigned_to_nat(2u);
v_nbuckets_2832_ = lean_nat_mul(v___x_2830_, v___x_2831_);
v___x_2833_ = lean_unsigned_to_nat(0u);
v___x_2834_ = lean_box(0);
v___x_2835_ = lean_mk_array(v_nbuckets_2832_, v___x_2834_);
v___x_2836_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4___redArg(v___x_2833_, v_data_2829_, v___x_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1___redArg(lean_object* v_m_2837_, lean_object* v_a_2838_, lean_object* v_b_2839_){
_start:
{
lean_object* v_size_2840_; lean_object* v_buckets_2841_; lean_object* v___x_2842_; uint64_t v___x_2843_; uint64_t v___x_2844_; uint64_t v___x_2845_; uint64_t v_fold_2846_; uint64_t v___x_2847_; uint64_t v___x_2848_; uint64_t v___x_2849_; size_t v___x_2850_; size_t v___x_2851_; size_t v___x_2852_; size_t v___x_2853_; size_t v___x_2854_; lean_object* v_bkt_2855_; uint8_t v___x_2856_; 
v_size_2840_ = lean_ctor_get(v_m_2837_, 0);
v_buckets_2841_ = lean_ctor_get(v_m_2837_, 1);
v___x_2842_ = lean_array_get_size(v_buckets_2841_);
v___x_2843_ = l_Lean_instHashableFVarId_hash(v_a_2838_);
v___x_2844_ = 32ULL;
v___x_2845_ = lean_uint64_shift_right(v___x_2843_, v___x_2844_);
v_fold_2846_ = lean_uint64_xor(v___x_2843_, v___x_2845_);
v___x_2847_ = 16ULL;
v___x_2848_ = lean_uint64_shift_right(v_fold_2846_, v___x_2847_);
v___x_2849_ = lean_uint64_xor(v_fold_2846_, v___x_2848_);
v___x_2850_ = lean_uint64_to_usize(v___x_2849_);
v___x_2851_ = lean_usize_of_nat(v___x_2842_);
v___x_2852_ = ((size_t)1ULL);
v___x_2853_ = lean_usize_sub(v___x_2851_, v___x_2852_);
v___x_2854_ = lean_usize_land(v___x_2850_, v___x_2853_);
v_bkt_2855_ = lean_array_uget_borrowed(v_buckets_2841_, v___x_2854_);
v___x_2856_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(v_a_2838_, v_bkt_2855_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2877_; 
lean_inc_ref(v_buckets_2841_);
lean_inc(v_size_2840_);
v_isSharedCheck_2877_ = !lean_is_exclusive(v_m_2837_);
if (v_isSharedCheck_2877_ == 0)
{
lean_object* v_unused_2878_; lean_object* v_unused_2879_; 
v_unused_2878_ = lean_ctor_get(v_m_2837_, 1);
lean_dec(v_unused_2878_);
v_unused_2879_ = lean_ctor_get(v_m_2837_, 0);
lean_dec(v_unused_2879_);
v___x_2858_ = v_m_2837_;
v_isShared_2859_ = v_isSharedCheck_2877_;
goto v_resetjp_2857_;
}
else
{
lean_dec(v_m_2837_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2877_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2860_; lean_object* v_size_x27_2861_; lean_object* v___x_2862_; lean_object* v_buckets_x27_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; 
v___x_2860_ = lean_unsigned_to_nat(1u);
v_size_x27_2861_ = lean_nat_add(v_size_2840_, v___x_2860_);
lean_dec(v_size_2840_);
lean_inc(v_bkt_2855_);
v___x_2862_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2862_, 0, v_a_2838_);
lean_ctor_set(v___x_2862_, 1, v_b_2839_);
lean_ctor_set(v___x_2862_, 2, v_bkt_2855_);
v_buckets_x27_2863_ = lean_array_uset(v_buckets_2841_, v___x_2854_, v___x_2862_);
v___x_2864_ = lean_unsigned_to_nat(4u);
v___x_2865_ = lean_nat_mul(v_size_x27_2861_, v___x_2864_);
v___x_2866_ = lean_unsigned_to_nat(3u);
v___x_2867_ = lean_nat_div(v___x_2865_, v___x_2866_);
lean_dec(v___x_2865_);
v___x_2868_ = lean_array_get_size(v_buckets_x27_2863_);
v___x_2869_ = lean_nat_dec_le(v___x_2867_, v___x_2868_);
lean_dec(v___x_2867_);
if (v___x_2869_ == 0)
{
lean_object* v_val_2870_; lean_object* v___x_2872_; 
v_val_2870_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2___redArg(v_buckets_x27_2863_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 1, v_val_2870_);
lean_ctor_set(v___x_2858_, 0, v_size_x27_2861_);
v___x_2872_ = v___x_2858_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_size_x27_2861_);
lean_ctor_set(v_reuseFailAlloc_2873_, 1, v_val_2870_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
else
{
lean_object* v___x_2875_; 
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 1, v_buckets_x27_2863_);
lean_ctor_set(v___x_2858_, 0, v_size_x27_2861_);
v___x_2875_ = v___x_2858_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_size_x27_2861_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_buckets_x27_2863_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
else
{
lean_dec(v_b_2839_);
lean_dec(v_a_2838_);
return v_m_2837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__1(lean_object* v___x_2880_, lean_object* v_a_2881_, lean_object* v_e_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v___x_2889_; lean_object* v_relevantTerms_2890_; lean_object* v_relevantHyps_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2913_; 
v___x_2889_ = lean_st_ref_take(v___y_2883_);
v_relevantTerms_2890_ = lean_ctor_get(v___x_2889_, 0);
v_relevantHyps_2891_ = lean_ctor_get(v___x_2889_, 1);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2893_ = v___x_2889_;
v_isShared_2894_ = v_isSharedCheck_2913_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_relevantHyps_2891_);
lean_inc(v_relevantTerms_2890_);
lean_dec(v___x_2889_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2913_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2895_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__0___redArg(v_relevantTerms_2890_, v_e_2882_, v___x_2880_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v___x_2895_);
v___x_2897_ = v___x_2893_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2895_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_relevantHyps_2891_);
v___x_2897_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v_relevantTerms_2900_; lean_object* v_relevantHyps_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2911_; 
v___x_2898_ = lean_st_ref_set(v___y_2883_, v___x_2897_);
v___x_2899_ = lean_st_ref_take(v___y_2883_);
v_relevantTerms_2900_ = lean_ctor_get(v___x_2899_, 0);
v_relevantHyps_2901_ = lean_ctor_get(v___x_2899_, 1);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2903_ = v___x_2899_;
v_isShared_2904_ = v_isSharedCheck_2911_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_relevantHyps_2901_);
lean_inc(v_relevantTerms_2900_);
lean_dec(v___x_2899_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2911_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2905_; lean_object* v___x_2907_; 
v___x_2905_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1___redArg(v_relevantHyps_2901_, v_a_2881_, v___x_2880_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 1, v___x_2905_);
v___x_2907_ = v___x_2903_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_relevantTerms_2900_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v___x_2905_);
v___x_2907_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2908_ = lean_st_ref_set(v___y_2883_, v___x_2907_);
v___x_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2880_);
return v___x_2909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__1___boxed(lean_object* v___x_2914_, lean_object* v_a_2915_, lean_object* v_e_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__1(v___x_2914_, v_a_2915_, v_e_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
return v_res_2923_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0(lean_object* v_e_2933_){
_start:
{
uint8_t v___y_2935_; lean_object* v___x_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; 
v___x_2938_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2));
v___x_2939_ = lean_unsigned_to_nat(1u);
v___x_2940_ = l_Lean_Expr_isAppOfArity(v_e_2933_, v___x_2938_, v___x_2939_);
if (v___x_2940_ == 0)
{
lean_object* v___x_2941_; uint8_t v___x_2942_; 
v___x_2941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4));
v___x_2942_ = l_Lean_Expr_isAppOfArity(v_e_2933_, v___x_2941_, v___x_2939_);
v___y_2935_ = v___x_2942_;
goto v___jp_2934_;
}
else
{
v___y_2935_ = v___x_2940_;
goto v___jp_2934_;
}
v___jp_2934_:
{
if (v___y_2935_ == 0)
{
return v___y_2935_;
}
else
{
uint8_t v___x_2936_; 
v___x_2936_ = l_Lean_Expr_hasLooseBVars(v_e_2933_);
if (v___x_2936_ == 0)
{
return v___y_2935_;
}
else
{
uint8_t v___x_2937_; 
v___x_2937_ = 0;
return v___x_2937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___boxed(lean_object* v_e_2943_){
_start:
{
uint8_t v_res_2944_; lean_object* v_r_2945_; 
v_res_2944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0(v_e_2943_);
lean_dec_ref(v_e_2943_);
v_r_2945_ = lean_box(v_res_2944_);
return v_r_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4(lean_object* v_as_2947_, size_t v_sz_2948_, size_t v_i_2949_, lean_object* v_b_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
uint8_t v___x_2957_; 
v___x_2957_ = lean_usize_dec_lt(v_i_2949_, v_sz_2948_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2958_; 
v___x_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2958_, 0, v_b_2950_);
return v___x_2958_;
}
else
{
lean_object* v_a_2959_; lean_object* v___x_2960_; 
v_a_2959_ = lean_array_uget_borrowed(v_as_2947_, v_i_2949_);
lean_inc(v_a_2959_);
v___x_2960_ = l_Lean_FVarId_getType___redArg(v_a_2959_, v___y_2952_, v___y_2954_, v___y_2955_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2962_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref(v___x_2960_);
v___x_2962_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___redArg(v_a_2961_, v___y_2953_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; lean_object* v___f_2964_; lean_object* v___x_2965_; lean_object* v___f_2966_; lean_object* v___x_2967_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref(v___x_2962_);
v___f_2964_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___closed__0));
v___x_2965_ = lean_box(0);
lean_inc(v_a_2959_);
v___f_2966_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__1___boxed), 9, 2);
lean_closure_set(v___f_2966_, 0, v___x_2965_);
lean_closure_set(v___f_2966_, 1, v_a_2959_);
v___x_2967_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3(v___f_2964_, v___f_2966_, v_a_2963_, v___x_2957_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
if (lean_obj_tag(v___x_2967_) == 0)
{
size_t v___x_2968_; size_t v___x_2969_; 
lean_dec_ref(v___x_2967_);
v___x_2968_ = ((size_t)1ULL);
v___x_2969_ = lean_usize_add(v_i_2949_, v___x_2968_);
v_i_2949_ = v___x_2969_;
v_b_2950_ = v___x_2965_;
goto _start;
}
else
{
return v___x_2967_;
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
v_a_2971_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2962_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2962_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
v_a_2979_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2960_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2960_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___boxed(lean_object* v_as_2987_, lean_object* v_sz_2988_, lean_object* v_i_2989_, lean_object* v_b_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
size_t v_sz_boxed_2997_; size_t v_i_boxed_2998_; lean_object* v_res_2999_; 
v_sz_boxed_2997_ = lean_unbox_usize(v_sz_2988_);
lean_dec(v_sz_2988_);
v_i_boxed_2998_ = lean_unbox_usize(v_i_2989_);
lean_dec(v_i_2989_);
v_res_2999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4(v_as_2987_, v_sz_boxed_2997_, v_i_boxed_2998_, v_b_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec_ref(v_as_2987_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___lam__0(lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = l_Lean_Meta_getPropHyps(v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3008_; size_t v_sz_3009_; size_t v___x_3010_; lean_object* v___x_3011_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref(v___x_3006_);
v___x_3008_ = lean_box(0);
v_sz_3009_ = lean_array_size(v_a_3007_);
v___x_3010_ = ((size_t)0ULL);
v___x_3011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4(v_a_3007_, v_sz_3009_, v___x_3010_, v___x_3008_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec(v_a_3007_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3030_; 
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3030_ == 0)
{
lean_object* v_unused_3031_; 
v_unused_3031_ = lean_ctor_get(v___x_3011_, 0);
lean_dec(v_unused_3031_);
v___x_3013_ = v___x_3011_;
v_isShared_3014_ = v_isSharedCheck_3030_;
goto v_resetjp_3012_;
}
else
{
lean_dec(v___x_3011_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3030_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3015_; lean_object* v_relevantTerms_3016_; lean_object* v_size_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; 
v___x_3015_ = lean_st_ref_get(v___y_3000_);
v_relevantTerms_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc_ref(v_relevantTerms_3016_);
lean_dec(v___x_3015_);
v_size_3017_ = lean_ctor_get(v_relevantTerms_3016_, 0);
lean_inc(v_size_3017_);
lean_dec_ref(v_relevantTerms_3016_);
v___x_3018_ = lean_unsigned_to_nat(0u);
v___x_3019_ = lean_nat_dec_eq(v_size_3017_, v___x_3018_);
lean_dec(v_size_3017_);
if (v___x_3019_ == 0)
{
uint8_t v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3023_; 
v___x_3020_ = 1;
v___x_3021_ = lean_box(v___x_3020_);
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 0, v___x_3021_);
v___x_3023_ = v___x_3013_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3021_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
else
{
uint8_t v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3028_; 
v___x_3025_ = 0;
v___x_3026_ = lean_box(v___x_3025_);
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 0, v___x_3026_);
v___x_3028_ = v___x_3013_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_3026_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
v_a_3032_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3011_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3011_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
v_a_3040_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_3006_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_3006_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3043_ == 0)
{
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___lam__0___boxed(lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___lam__0(v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize(lean_object* v_goal_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_){
_start:
{
lean_object* v___f_3063_; lean_object* v___x_3064_; 
v___f_3063_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___closed__0));
v___x_3064_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_goal_3056_, v___f_3063_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___boxed(lean_object* v_goal_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize(v_goal_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__0(lean_object* v_00_u03b2_3073_, lean_object* v_m_3074_, lean_object* v_a_3075_, lean_object* v_b_3076_){
_start:
{
lean_object* v___x_3077_; 
v___x_3077_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__0___redArg(v_m_3074_, v_a_3075_, v_b_3076_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1(lean_object* v_00_u03b2_3078_, lean_object* v_m_3079_, lean_object* v_a_3080_, lean_object* v_b_3081_){
_start:
{
lean_object* v___x_3082_; 
v___x_3082_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1___redArg(v_m_3079_, v_a_3080_, v_b_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1(lean_object* v_00_u03b2_3083_, lean_object* v_a_3084_, lean_object* v_x_3085_){
_start:
{
uint8_t v___x_3086_; 
v___x_3086_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(v_a_3084_, v_x_3085_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3087_, lean_object* v_a_3088_, lean_object* v_x_3089_){
_start:
{
uint8_t v_res_3090_; lean_object* v_r_3091_; 
v_res_3090_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1(v_00_u03b2_3087_, v_a_3088_, v_x_3089_);
lean_dec(v_x_3089_);
lean_dec(v_a_3088_);
v_r_3091_ = lean_box(v_res_3090_);
return v_r_3091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2(lean_object* v_00_u03b2_3092_, lean_object* v_data_3093_){
_start:
{
lean_object* v___x_3094_; 
v___x_3094_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2___redArg(v_data_3093_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7(lean_object* v_e_3095_, lean_object* v_a_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v___x_3103_; 
v___x_3103_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(v_e_3095_, v_a_3096_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___boxed(lean_object* v_e_3104_, lean_object* v_a_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7(v_e_3104_, v_a_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec(v_a_3105_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3113_, lean_object* v_i_3114_, lean_object* v_source_3115_, lean_object* v_target_3116_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4___redArg(v_i_3114_, v_source_3115_, v_target_3116_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8(lean_object* v_e_3118_, lean_object* v_a_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(v_e_3118_, v_a_3119_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___boxed(lean_object* v_e_3127_, lean_object* v_a_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8(v_e_3127_, v_a_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec(v_a_3128_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_3136_, lean_object* v_x_3137_, lean_object* v_x_3138_){
_start:
{
lean_object* v___x_3139_; 
v___x_3139_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(v_x_3137_, v_x_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11(lean_object* v_00_u03b2_3140_, lean_object* v_m_3141_, lean_object* v_a_3142_){
_start:
{
uint8_t v___x_3143_; 
v___x_3143_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(v_m_3141_, v_a_3142_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___boxed(lean_object* v_00_u03b2_3144_, lean_object* v_m_3145_, lean_object* v_a_3146_){
_start:
{
uint8_t v_res_3147_; lean_object* v_r_3148_; 
v_res_3147_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11(v_00_u03b2_3144_, v_m_3145_, v_a_3146_);
lean_dec_ref(v_a_3146_);
lean_dec_ref(v_m_3145_);
v_r_3148_ = lean_box(v_res_3147_);
return v_r_3148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_handleSize(lean_object* v_goal_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_){
_start:
{
lean_object* v___x_3156_; 
lean_inc(v_goal_3149_);
v___x_3156_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize(v_goal_3149_, v_a_3150_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3166_; 
v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3159_ = v___x_3156_;
v_isShared_3160_ = v_isSharedCheck_3166_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3156_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3166_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
uint8_t v___x_3161_; 
v___x_3161_ = lean_unbox(v_a_3157_);
lean_dec(v_a_3157_);
if (v___x_3161_ == 0)
{
lean_object* v___x_3163_; 
if (v_isShared_3160_ == 0)
{
lean_ctor_set(v___x_3159_, 0, v_goal_3149_);
v___x_3163_ = v___x_3159_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_goal_3149_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
else
{
lean_object* v___x_3165_; 
lean_del_object(v___x_3159_);
v___x_3165_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize(v_goal_3149_, v_a_3150_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_);
return v___x_3165_;
}
}
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
lean_dec(v_goal_3149_);
v_a_3167_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___x_3156_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3156_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3167_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_handleSize___boxed(lean_object* v_goal_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_handleSize(v_goal_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_);
lean_dec(v_a_3180_);
lean_dec_ref(v_a_3179_);
lean_dec(v_a_3178_);
lean_dec_ref(v_a_3177_);
lean_dec(v_a_3176_);
return v_res_3182_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3185_; 
v___x_3185_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3185_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__1);
v___x_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
return v___x_3187_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3188_ = lean_unsigned_to_nat(0u);
v___x_3189_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2);
v___x_3190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
lean_ctor_set(v___x_3190_, 1, v___x_3188_);
return v___x_3190_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3191_ = lean_unsigned_to_nat(32u);
v___x_3192_ = lean_mk_empty_array_with_capacity(v___x_3191_);
v___x_3193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3192_);
return v___x_3193_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__5(void){
_start:
{
size_t v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3194_ = ((size_t)5ULL);
v___x_3195_ = lean_unsigned_to_nat(0u);
v___x_3196_ = lean_unsigned_to_nat(32u);
v___x_3197_ = lean_mk_empty_array_with_capacity(v___x_3196_);
v___x_3198_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__4);
v___x_3199_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3199_, 0, v___x_3198_);
lean_ctor_set(v___x_3199_, 1, v___x_3197_);
lean_ctor_set(v___x_3199_, 2, v___x_3195_);
lean_ctor_set(v___x_3199_, 3, v___x_3195_);
lean_ctor_set_usize(v___x_3199_, 4, v___x_3194_);
return v___x_3199_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3200_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__5);
v___x_3201_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2);
v___x_3202_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
lean_ctor_set(v___x_3202_, 1, v___x_3201_);
lean_ctor_set(v___x_3202_, 2, v___x_3201_);
lean_ctor_set(v___x_3202_, 3, v___x_3200_);
return v___x_3202_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3203_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__6);
v___x_3204_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__3);
v___x_3205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
lean_ctor_set(v___x_3205_, 1, v___x_3203_);
return v___x_3205_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12);
v___x_3207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0(lean_object* v_goal_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = l_Lean_Elab_Tactic_BVDecide_Frontend_intToBitVecExt;
v___x_3217_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_3216_, v___y_3214_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3219_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref(v___x_3217_);
v___x_3219_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_3214_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; lean_object* v_maxSteps_3221_; lean_object* v___x_3222_; uint8_t v___x_3223_; uint8_t v___x_3224_; uint8_t v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref(v___x_3219_);
v_maxSteps_3221_ = lean_ctor_get(v___y_3209_, 1);
v___x_3222_ = lean_unsigned_to_nat(2u);
v___x_3223_ = 0;
v___x_3224_ = 1;
v___x_3225_ = 0;
v___x_3226_ = lean_box(0);
lean_inc(v_maxSteps_3221_);
v___x_3227_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_3227_, 0, v_maxSteps_3221_);
lean_ctor_set(v___x_3227_, 1, v___x_3222_);
lean_ctor_set(v___x_3227_, 2, v___x_3226_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3, v___x_3223_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 1, v___x_3224_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 2, v___x_3223_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 3, v___x_3224_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 4, v___x_3224_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 5, v___x_3224_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 6, v___x_3225_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 7, v___x_3224_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 8, v___x_3224_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 9, v___x_3223_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 10, v___x_3223_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 11, v___x_3223_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 12, v___x_3224_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 13, v___x_3223_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 14, v___x_3223_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 15, v___x_3223_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 16, v___x_3224_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 17, v___x_3224_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 18, v___x_3223_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 19, v___x_3224_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 20, v___x_3224_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 21, v___x_3224_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 22, v___x_3224_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 23, v___x_3224_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 24, v___x_3224_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 25, v___x_3224_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 26, v___x_3223_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 27, v___x_3223_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 28, v___x_3224_);
v___x_3228_ = lean_unsigned_to_nat(1u);
v___x_3229_ = lean_mk_empty_array_with_capacity(v___x_3228_);
v___x_3230_ = lean_array_push(v___x_3229_, v_a_3218_);
v___x_3231_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_3227_, v___x_3230_, v_a_3220_, v___y_3211_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3233_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_a_3232_);
lean_dec_ref(v___x_3231_);
lean_inc(v_goal_3208_);
v___x_3233_ = l_Lean_MVarId_getNondepPropHyps(v_goal_3208_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_a_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
lean_inc(v_a_3234_);
lean_dec_ref(v___x_3233_);
v___x_3235_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__0));
v___x_3236_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__7);
v___x_3237_ = l_Lean_Meta_simpGoal(v_goal_3208_, v_a_3232_, v___x_3235_, v___x_3226_, v___x_3224_, v_a_3234_, v___x_3236_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3275_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3240_ = v___x_3237_;
v_isShared_3241_ = v_isSharedCheck_3275_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3237_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3275_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v_fst_3242_; 
v_fst_3242_ = lean_ctor_get(v_a_3238_, 0);
lean_inc(v_fst_3242_);
lean_dec(v_a_3238_);
if (lean_obj_tag(v_fst_3242_) == 1)
{
lean_object* v_val_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3271_; 
lean_del_object(v___x_3240_);
v_val_3243_ = lean_ctor_get(v_fst_3242_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v_fst_3242_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3245_ = v_fst_3242_;
v_isShared_3246_ = v_isSharedCheck_3271_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_val_3243_);
lean_dec(v_fst_3242_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3271_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v_snd_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v_snd_3247_ = lean_ctor_get(v_val_3243_, 1);
lean_inc(v_snd_3247_);
lean_dec(v_val_3243_);
v___x_3248_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__8);
v___x_3249_ = lean_st_mk_ref(v___x_3248_);
v___x_3250_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_handleSize(v_snd_3247_, v___x_3249_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3262_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3253_ = v___x_3250_;
v_isShared_3254_ = v_isSharedCheck_3262_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3250_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3262_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3255_; lean_object* v___x_3257_; 
v___x_3255_ = lean_st_ref_get(v___x_3249_);
lean_dec(v___x_3249_);
lean_dec(v___x_3255_);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 0, v_a_3251_);
v___x_3257_ = v___x_3245_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3251_);
v___x_3257_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
lean_object* v___x_3259_; 
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 0, v___x_3257_);
v___x_3259_ = v___x_3253_;
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
lean_dec(v___x_3249_);
lean_del_object(v___x_3245_);
v_a_3263_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___x_3250_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3250_);
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
}
else
{
lean_object* v___x_3273_; 
lean_dec(v_fst_3242_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 0, v___x_3226_);
v___x_3273_ = v___x_3240_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3226_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
else
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3283_; 
v_a_3276_ = lean_ctor_get(v___x_3237_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3278_ = v___x_3237_;
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3237_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3281_; 
if (v_isShared_3279_ == 0)
{
v___x_3281_ = v___x_3278_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_a_3276_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
lean_dec(v_a_3232_);
lean_dec(v_goal_3208_);
v_a_3284_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3233_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3233_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
else
{
lean_object* v_a_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3299_; 
lean_dec(v_goal_3208_);
v_a_3292_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3294_ = v___x_3231_;
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_a_3292_);
lean_dec(v___x_3231_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3297_; 
if (v_isShared_3295_ == 0)
{
v___x_3297_ = v___x_3294_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_a_3292_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
}
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
lean_dec(v_a_3218_);
lean_dec(v_goal_3208_);
v_a_3300_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3219_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3219_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3300_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
else
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
lean_dec(v_goal_3208_);
v_a_3308_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3310_ = v___x_3217_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3217_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3308_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___boxed(lean_object* v_goal_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0(v_goal_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
return v_res_3324_;
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
