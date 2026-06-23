// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.IntToBitVec
// Imports: public import Lean.Meta.Tactic.BVDecide.Normalize.Basic
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
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
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
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_tryClearMany_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_intToBitVecExt;
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "System"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Platform"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "numBits"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(244, 7, 92, 194, 164, 177, 167, 52)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(128, 236, 129, 7, 244, 3, 115, 42)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(195, 13, 33, 186, 170, 198, 65, 128)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "symm"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(220, 149, 144, 59, 77, 93, 25, 217)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3(lean_object*, lean_object*, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__13(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "z"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 196, 150, 181, 147, 170, 254, 79)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "casesOn"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(250, 240, 184, 175, 50, 245, 157, 81)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "failed to create binder due to failure when reverting variable dependencies"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 110, .m_capacity = 110, .m_length = 109, .m_data = "Detected USize/ISize in the goal but no hypothesis about System.Platform.numBits, consider case splitting on "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "numBits_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(244, 7, 92, 194, 164, 177, 167, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(128, 236, 129, 7, 244, 3, 115, 42)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(65, 163, 238, 100, 187, 225, 152, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toBitVec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(156, 179, 78, 164, 17, 99, 115, 128)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ISize"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(91, 57, 122, 235, 182, 82, 28, 168)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_handleSize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_handleSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__7;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "intToBitVec"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(130, 217, 71, 86, 75, 235, 18, 78)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg(lean_object* v_e_3_, lean_object* v_a_4_){
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
v___x_12_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0));
v___x_13_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___boxed(lean_object* v_e_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg(v_e_22_, v_a_23_);
lean_dec(v_a_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm(lean_object* v_e_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
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
v___x_39_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0));
v___x_40_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___boxed(lean_object* v_e_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm(v_e_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg(lean_object* v_f_59_, lean_object* v_a_60_){
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
v___x_68_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0));
v___x_69_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___boxed(lean_object* v_f_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg(v_f_78_, v_a_79_);
lean_dec(v_a_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp(lean_object* v_f_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
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
v___x_95_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0));
v___x_96_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___boxed(lean_object* v_f_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp(v_f_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(lean_object* v_e_113_, lean_object* v___y_114_){
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg___boxed(lean_object* v_e_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_e_138_, v___y_139_);
lean_dec(v___y_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0(lean_object* v_e_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_e_142_, v___y_144_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___boxed(lean_object* v_e_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0(v_e_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(lean_object* v_mvarId_156_, lean_object* v_x_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg___boxed(lean_object* v_mvarId_180_, lean_object* v_x_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_mvarId_180_, v_x_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2(lean_object* v_00_u03b1_188_, lean_object* v_mvarId_189_, lean_object* v_x_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_mvarId_189_, v_x_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___boxed(lean_object* v_00_u03b1_197_, lean_object* v_mvarId_198_, lean_object* v_x_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2(v_00_u03b1_197_, v_mvarId_198_, v_x_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
return v_res_205_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = l_Lean_Level_ofNat(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_box(0);
v___x_231_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11);
v___x_232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_230_);
return v___x_232_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12);
v___x_234_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10));
v___x_235_ = l_Lean_mkConst(v___x_234_, v___x_233_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1(lean_object* v_as_236_, size_t v_sz_237_, size_t v_i_238_, lean_object* v_b_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
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
lean_dec_ref_known(v___x_248_, 1);
v___x_250_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_a_249_, v___y_241_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_252_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
lean_dec_ref_known(v___x_250_, 1);
v___x_252_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_251_, v___y_241_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v_a_255_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
lean_dec_ref_known(v___x_252_, 1);
v___x_259_ = lean_box(0);
v___x_260_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0));
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
v___x_271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2));
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
v___x_273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6));
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
v___x_296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8));
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
v___x_318_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13);
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
v___x_331_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8));
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___boxed(lean_object* v_as_368_, lean_object* v_sz_369_, lean_object* v_i_370_, lean_object* v_b_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
size_t v_sz_boxed_377_; size_t v_i_boxed_378_; lean_object* v_res_379_; 
v_sz_boxed_377_ = lean_unbox_usize(v_sz_369_);
lean_dec(v_sz_369_);
v_i_boxed_378_ = lean_unbox_usize(v_i_370_);
lean_dec(v_i_370_);
v_res_379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1(v_as_368_, v_sz_boxed_377_, v_i_boxed_378_, v_b_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec_ref(v_as_368_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0(lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Meta_getPropHyps(v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_387_; lean_object* v___x_388_; size_t v_sz_389_; size_t v___x_390_; lean_object* v___x_391_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_385_, 1);
v___x_387_ = lean_box(0);
v___x_388_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0));
v_sz_389_ = lean_array_size(v_a_386_);
v___x_390_ = ((size_t)0ULL);
v___x_391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1(v_a_386_, v_sz_389_, v___x_390_, v___x_388_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
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
lean_dec_ref_known(v_fst_396_, 1);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0___boxed(lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0(v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq(lean_object* v_goal_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v___f_434_; lean_object* v___x_435_; 
v___f_434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___closed__0));
v___x_435_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_goal_428_, v___f_434_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___boxed(lean_object* v_goal_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq(v_goal_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0(lean_object* v_x_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v___x_450_; 
lean_inc(v___y_444_);
v___x_450_ = lean_apply_6(v_x_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, lean_box(0));
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0___boxed(lean_object* v_x_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0(v_x_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_452_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(lean_object* v_mvarId_459_, lean_object* v_x_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___f_467_; lean_object* v___x_468_; 
lean_inc(v___y_461_);
v___f_467_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0___boxed), 7, 2);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___boxed(lean_object* v_mvarId_477_, lean_object* v_x_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_mvarId_477_, v_x_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14(lean_object* v_00_u03b1_486_, lean_object* v_mvarId_487_, lean_object* v_x_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_mvarId_487_, v_x_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___boxed(lean_object* v_00_u03b1_496_, lean_object* v_mvarId_497_, lean_object* v_x_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14(v_00_u03b1_496_, v_mvarId_497_, v_x_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(lean_object* v_a_506_, lean_object* v_x_507_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg___boxed(lean_object* v_a_515_, lean_object* v_x_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(v_a_515_, v_x_516_);
lean_dec(v_x_516_);
lean_dec_ref(v_a_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(lean_object* v_m_518_, lean_object* v_a_519_){
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
v___x_535_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(v_a_519_, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3___redArg___boxed(lean_object* v_m_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(v_m_536_, v_a_537_);
lean_dec_ref(v_a_537_);
lean_dec_ref(v_m_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__0(lean_object* v_fst_539_, lean_object* v___y_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(v_fst_539_, v___y_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__0___boxed(lean_object* v_fst_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__0(v_fst_542_, v___y_543_);
lean_dec_ref(v___y_543_);
lean_dec(v_fst_542_);
return v_res_544_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(lean_object* v_a_545_, lean_object* v_x_546_){
_start:
{
if (lean_obj_tag(v_x_546_) == 0)
{
uint8_t v___x_547_; 
v___x_547_ = 0;
return v___x_547_;
}
else
{
lean_object* v_key_548_; lean_object* v_tail_549_; uint8_t v___x_550_; 
v_key_548_ = lean_ctor_get(v_x_546_, 0);
v_tail_549_ = lean_ctor_get(v_x_546_, 2);
v___x_550_ = lean_expr_eqv(v_key_548_, v_a_545_);
if (v___x_550_ == 0)
{
v_x_546_ = v_tail_549_;
goto _start;
}
else
{
return v___x_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg___boxed(lean_object* v_a_552_, lean_object* v_x_553_){
_start:
{
uint8_t v_res_554_; lean_object* v_r_555_; 
v_res_554_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_552_, v_x_553_);
lean_dec(v_x_553_);
lean_dec_ref(v_a_552_);
v_r_555_ = lean_box(v_res_554_);
return v_r_555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20___redArg(lean_object* v_x_556_, lean_object* v_x_557_){
_start:
{
if (lean_obj_tag(v_x_557_) == 0)
{
return v_x_556_;
}
else
{
lean_object* v_key_558_; lean_object* v_value_559_; lean_object* v_tail_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_583_; 
v_key_558_ = lean_ctor_get(v_x_557_, 0);
v_value_559_ = lean_ctor_get(v_x_557_, 1);
v_tail_560_ = lean_ctor_get(v_x_557_, 2);
v_isSharedCheck_583_ = !lean_is_exclusive(v_x_557_);
if (v_isSharedCheck_583_ == 0)
{
v___x_562_ = v_x_557_;
v_isShared_563_ = v_isSharedCheck_583_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_tail_560_);
lean_inc(v_value_559_);
lean_inc(v_key_558_);
lean_dec(v_x_557_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_583_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; uint64_t v___x_565_; uint64_t v___x_566_; uint64_t v___x_567_; uint64_t v_fold_568_; uint64_t v___x_569_; uint64_t v___x_570_; uint64_t v___x_571_; size_t v___x_572_; size_t v___x_573_; size_t v___x_574_; size_t v___x_575_; size_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_564_ = lean_array_get_size(v_x_556_);
v___x_565_ = l_Lean_Expr_hash(v_key_558_);
v___x_566_ = 32ULL;
v___x_567_ = lean_uint64_shift_right(v___x_565_, v___x_566_);
v_fold_568_ = lean_uint64_xor(v___x_565_, v___x_567_);
v___x_569_ = 16ULL;
v___x_570_ = lean_uint64_shift_right(v_fold_568_, v___x_569_);
v___x_571_ = lean_uint64_xor(v_fold_568_, v___x_570_);
v___x_572_ = lean_uint64_to_usize(v___x_571_);
v___x_573_ = lean_usize_of_nat(v___x_564_);
v___x_574_ = ((size_t)1ULL);
v___x_575_ = lean_usize_sub(v___x_573_, v___x_574_);
v___x_576_ = lean_usize_land(v___x_572_, v___x_575_);
v___x_577_ = lean_array_uget_borrowed(v_x_556_, v___x_576_);
lean_inc(v___x_577_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 2, v___x_577_);
v___x_579_ = v___x_562_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_key_558_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_value_559_);
lean_ctor_set(v_reuseFailAlloc_582_, 2, v___x_577_);
v___x_579_ = v_reuseFailAlloc_582_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; 
v___x_580_ = lean_array_uset(v_x_556_, v___x_576_, v___x_579_);
v_x_556_ = v___x_580_;
v_x_557_ = v_tail_560_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3___redArg(lean_object* v_i_584_, lean_object* v_source_585_, lean_object* v_target_586_){
_start:
{
lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_587_ = lean_array_get_size(v_source_585_);
v___x_588_ = lean_nat_dec_lt(v_i_584_, v___x_587_);
if (v___x_588_ == 0)
{
lean_dec_ref(v_source_585_);
lean_dec(v_i_584_);
return v_target_586_;
}
else
{
lean_object* v_es_589_; lean_object* v___x_590_; lean_object* v_source_591_; lean_object* v_target_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v_es_589_ = lean_array_fget(v_source_585_, v_i_584_);
v___x_590_ = lean_box(0);
v_source_591_ = lean_array_fset(v_source_585_, v_i_584_, v___x_590_);
v_target_592_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20___redArg(v_target_586_, v_es_589_);
v___x_593_ = lean_unsigned_to_nat(1u);
v___x_594_ = lean_nat_add(v_i_584_, v___x_593_);
lean_dec(v_i_584_);
v_i_584_ = v___x_594_;
v_source_585_ = v_source_591_;
v_target_586_ = v_target_592_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(lean_object* v_data_596_){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v_nbuckets_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_597_ = lean_array_get_size(v_data_596_);
v___x_598_ = lean_unsigned_to_nat(2u);
v_nbuckets_599_ = lean_nat_mul(v___x_597_, v___x_598_);
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = lean_box(0);
v___x_602_ = lean_mk_array(v_nbuckets_599_, v___x_601_);
v___x_603_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3___redArg(v___x_600_, v_data_596_, v___x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(lean_object* v_a_604_, lean_object* v_b_605_, lean_object* v_x_606_){
_start:
{
if (lean_obj_tag(v_x_606_) == 0)
{
lean_dec(v_b_605_);
lean_dec_ref(v_a_604_);
return v_x_606_;
}
else
{
lean_object* v_key_607_; lean_object* v_value_608_; lean_object* v_tail_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_621_; 
v_key_607_ = lean_ctor_get(v_x_606_, 0);
v_value_608_ = lean_ctor_get(v_x_606_, 1);
v_tail_609_ = lean_ctor_get(v_x_606_, 2);
v_isSharedCheck_621_ = !lean_is_exclusive(v_x_606_);
if (v_isSharedCheck_621_ == 0)
{
v___x_611_ = v_x_606_;
v_isShared_612_ = v_isSharedCheck_621_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_tail_609_);
lean_inc(v_value_608_);
lean_inc(v_key_607_);
lean_dec(v_x_606_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_621_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
uint8_t v___x_613_; 
v___x_613_ = lean_expr_eqv(v_key_607_, v_a_604_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_614_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(v_a_604_, v_b_605_, v_tail_609_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 2, v___x_614_);
v___x_616_ = v___x_611_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_key_607_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_value_608_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
else
{
lean_object* v___x_619_; 
lean_dec(v_value_608_);
lean_dec(v_key_607_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 1, v_b_605_);
lean_ctor_set(v___x_611_, 0, v_a_604_);
v___x_619_ = v___x_611_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_604_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_b_605_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_tail_609_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(lean_object* v_m_622_, lean_object* v_a_623_, lean_object* v_b_624_){
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
v___x_644_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_623_, v_bkt_643_);
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
v_val_655_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(v_buckets_x27_648_);
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
v___x_664_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(v_a_623_, v_b_624_, v_bkt_643_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(lean_object* v_as_670_, size_t v_sz_671_, size_t v_i_672_, lean_object* v_b_673_){
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
v___x_699_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(v_fst_678_, v_a_693_, v___x_694_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2___redArg___boxed(lean_object* v_as_712_, lean_object* v_sz_713_, lean_object* v_i_714_, lean_object* v_b_715_, lean_object* v___y_716_){
_start:
{
size_t v_sz_boxed_717_; size_t v_i_boxed_718_; lean_object* v_res_719_; 
v_sz_boxed_717_ = lean_unbox_usize(v_sz_713_);
lean_dec(v_sz_713_);
v_i_boxed_718_ = lean_unbox_usize(v_i_714_);
lean_dec(v_i_714_);
v_res_719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(v_as_712_, v_sz_boxed_717_, v_i_boxed_718_, v_b_715_);
lean_dec_ref(v_as_712_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__1(lean_object* v___x_720_, lean_object* v___x_721_, lean_object* v_z_722_, lean_object* v___y_723_, size_t v___x_724_, lean_object* v_a_725_, uint8_t v___x_726_, lean_object* v_args_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
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
v___x_745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6));
v___x_746_ = l_Lean_mkConst(v___x_745_, v___x_721_);
v___x_747_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(v___x_744_, v___x_746_, v_z_722_);
lean_inc_ref(v_args_727_);
v___x_748_ = l_Array_toSubarray___redArg(v_args_727_, v___x_736_, v___x_734_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v_sz_750_ = lean_array_size(v___y_723_);
v___x_751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(v___y_723_, v_sz_750_, v___x_724_, v___x_749_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v_fst_753_; lean_object* v___f_754_; lean_object* v___x_755_; uint8_t v___x_756_; uint8_t v___x_757_; lean_object* v___x_758_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_751_, 1);
v_fst_753_ = lean_ctor_get(v_a_752_, 0);
lean_inc(v_fst_753_);
lean_dec(v_a_752_);
v___f_754_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__0___boxed), 2, 1);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__1___boxed(lean_object* v___x_767_, lean_object* v___x_768_, lean_object* v_z_769_, lean_object* v___y_770_, lean_object* v___x_771_, lean_object* v_a_772_, lean_object* v___x_773_, lean_object* v_args_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
size_t v___x_21193__boxed_781_; uint8_t v___x_21195__boxed_782_; lean_object* v_res_783_; 
v___x_21193__boxed_781_ = lean_unbox_usize(v___x_771_);
lean_dec(v___x_771_);
v___x_21195__boxed_782_ = lean_unbox(v___x_773_);
v_res_783_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__1(v___x_767_, v___x_768_, v_z_769_, v___y_770_, v___x_21193__boxed_781_, v_a_772_, v___x_21195__boxed_782_, v_args_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(size_t v_sz_784_, size_t v_i_785_, lean_object* v_bs_786_){
_start:
{
uint8_t v___x_787_; 
v___x_787_ = lean_usize_dec_lt(v_i_785_, v_sz_784_);
if (v___x_787_ == 0)
{
return v_bs_786_;
}
else
{
lean_object* v_v_788_; lean_object* v_fst_789_; lean_object* v_snd_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_806_; 
v_v_788_ = lean_array_uget(v_bs_786_, v_i_785_);
v_fst_789_ = lean_ctor_get(v_v_788_, 0);
v_snd_790_ = lean_ctor_get(v_v_788_, 1);
v_isSharedCheck_806_ = !lean_is_exclusive(v_v_788_);
if (v_isSharedCheck_806_ == 0)
{
v___x_792_ = v_v_788_;
v_isShared_793_ = v_isSharedCheck_806_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_snd_790_);
lean_inc(v_fst_789_);
lean_dec(v_v_788_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_806_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v_bs_x27_795_; uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_794_ = lean_unsigned_to_nat(0u);
v_bs_x27_795_ = lean_array_uset(v_bs_786_, v_i_785_, v___x_794_);
v___x_796_ = 0;
v___x_797_ = lean_box(v___x_796_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_797_);
v___x_799_ = v___x_792_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_snd_790_);
v___x_799_ = v_reuseFailAlloc_805_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; size_t v___x_801_; size_t v___x_802_; lean_object* v___x_803_; 
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_fst_789_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_add(v_i_785_, v___x_801_);
v___x_803_ = lean_array_uset(v_bs_x27_795_, v_i_785_, v___x_800_);
v_i_785_ = v___x_802_;
v_bs_786_ = v___x_803_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13___boxed(lean_object* v_sz_807_, lean_object* v_i_808_, lean_object* v_bs_809_){
_start:
{
size_t v_sz_boxed_810_; size_t v_i_boxed_811_; lean_object* v_res_812_; 
v_sz_boxed_810_ = lean_unbox_usize(v_sz_807_);
lean_dec(v_sz_807_);
v_i_boxed_811_ = lean_unbox_usize(v_i_808_);
lean_dec(v_i_808_);
v_res_812_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(v_sz_boxed_810_, v_i_boxed_811_, v_bs_809_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___lam__0(lean_object* v___x_813_, lean_object* v_a_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_20781__overap_822_; lean_object* v___x_823_; 
v___x_821_ = l_Lean_instInhabitedExpr;
v___x_20781__overap_822_ = l_instInhabitedOfMonad___redArg(v___x_813_, v___x_821_);
lean_inc(v___y_819_);
lean_inc_ref(v___y_818_);
lean_inc(v___y_817_);
lean_inc_ref(v___y_816_);
lean_inc(v___y_815_);
v___x_823_ = lean_apply_6(v___x_20781__overap_822_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, lean_box(0));
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___lam__0___boxed(lean_object* v___x_824_, lean_object* v_a_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___lam__0(v___x_824_, v_a_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v_a_825_);
return v_res_832_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0(void){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_instMonadEIO(lean_box(0));
return v___x_833_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0);
v___x_835_ = l_StateRefT_x27_instMonad___redArg(v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___lam__0___boxed(lean_object* v_acc_840_, lean_object* v_declInfos_841_, lean_object* v_k_842_, lean_object* v_kind_843_, lean_object* v___y_844_, lean_object* v_b_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
uint8_t v_kind_boxed_851_; lean_object* v_res_852_; 
v_kind_boxed_851_ = lean_unbox(v_kind_843_);
v_res_852_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___lam__0(v_acc_840_, v_declInfos_841_, v_k_842_, v_kind_boxed_851_, v___y_844_, v_b_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_844_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34(lean_object* v_acc_853_, lean_object* v_declInfos_854_, lean_object* v_k_855_, uint8_t v_kind_856_, lean_object* v_name_857_, uint8_t v_bi_858_, lean_object* v_type_859_, uint8_t v_kind_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___x_867_; lean_object* v___f_868_; lean_object* v___x_869_; 
v___x_867_ = lean_box(v_kind_856_);
lean_inc(v___y_861_);
v___f_868_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___lam__0___boxed), 11, 5);
lean_closure_set(v___f_868_, 0, v_acc_853_);
lean_closure_set(v___f_868_, 1, v_declInfos_854_);
lean_closure_set(v___f_868_, 2, v_k_855_);
lean_closure_set(v___f_868_, 3, v___x_867_);
lean_closure_set(v___f_868_, 4, v___y_861_);
v___x_869_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_857_, v_bi_858_, v_type_859_, v___f_868_, v_kind_860_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_869_) == 0)
{
return v___x_869_;
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(lean_object* v_declInfos_878_, lean_object* v_k_879_, uint8_t v_kind_880_, lean_object* v_acc_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___x_888_; lean_object* v_toApplicative_889_; lean_object* v_toFunctor_890_; lean_object* v_toSeq_891_; lean_object* v_toSeqLeft_892_; lean_object* v_toSeqRight_893_; lean_object* v___f_894_; lean_object* v___f_895_; lean_object* v___f_896_; lean_object* v___f_897_; lean_object* v___x_898_; lean_object* v___f_899_; lean_object* v___f_900_; lean_object* v___f_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v_toApplicative_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_953_; 
v___x_888_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1);
v_toApplicative_889_ = lean_ctor_get(v___x_888_, 0);
v_toFunctor_890_ = lean_ctor_get(v_toApplicative_889_, 0);
v_toSeq_891_ = lean_ctor_get(v_toApplicative_889_, 2);
v_toSeqLeft_892_ = lean_ctor_get(v_toApplicative_889_, 3);
v_toSeqRight_893_ = lean_ctor_get(v_toApplicative_889_, 4);
v___f_894_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__2));
v___f_895_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__3));
lean_inc_ref_n(v_toFunctor_890_, 2);
v___f_896_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_896_, 0, v_toFunctor_890_);
v___f_897_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_897_, 0, v_toFunctor_890_);
v___x_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_898_, 0, v___f_896_);
lean_ctor_set(v___x_898_, 1, v___f_897_);
lean_inc(v_toSeqRight_893_);
v___f_899_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_899_, 0, v_toSeqRight_893_);
lean_inc(v_toSeqLeft_892_);
v___f_900_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_900_, 0, v_toSeqLeft_892_);
lean_inc(v_toSeq_891_);
v___f_901_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_901_, 0, v_toSeq_891_);
v___x_902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_902_, 0, v___x_898_);
lean_ctor_set(v___x_902_, 1, v___f_894_);
lean_ctor_set(v___x_902_, 2, v___f_901_);
lean_ctor_set(v___x_902_, 3, v___f_900_);
lean_ctor_set(v___x_902_, 4, v___f_899_);
v___x_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
lean_ctor_set(v___x_903_, 1, v___f_895_);
v___x_904_ = l_StateRefT_x27_instMonad___redArg(v___x_903_);
v_toApplicative_905_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; 
v_unused_954_ = lean_ctor_get(v___x_904_, 1);
lean_dec(v_unused_954_);
v___x_907_ = v___x_904_;
v_isShared_908_ = v_isSharedCheck_953_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_toApplicative_905_);
lean_dec(v___x_904_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_953_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v_toFunctor_909_; lean_object* v_toSeq_910_; lean_object* v_toSeqLeft_911_; lean_object* v_toSeqRight_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_951_; 
v_toFunctor_909_ = lean_ctor_get(v_toApplicative_905_, 0);
v_toSeq_910_ = lean_ctor_get(v_toApplicative_905_, 2);
v_toSeqLeft_911_ = lean_ctor_get(v_toApplicative_905_, 3);
v_toSeqRight_912_ = lean_ctor_get(v_toApplicative_905_, 4);
v_isSharedCheck_951_ = !lean_is_exclusive(v_toApplicative_905_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; 
v_unused_952_ = lean_ctor_get(v_toApplicative_905_, 1);
lean_dec(v_unused_952_);
v___x_914_ = v_toApplicative_905_;
v_isShared_915_ = v_isSharedCheck_951_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_toSeqRight_912_);
lean_inc(v_toSeqLeft_911_);
lean_inc(v_toSeq_910_);
lean_inc(v_toFunctor_909_);
lean_dec(v_toApplicative_905_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_951_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___f_916_; lean_object* v___f_917_; lean_object* v___f_918_; lean_object* v___f_919_; lean_object* v___x_920_; lean_object* v___f_921_; lean_object* v___f_922_; lean_object* v___f_923_; lean_object* v___x_925_; 
v___f_916_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__4));
v___f_917_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__5));
lean_inc_ref(v_toFunctor_909_);
v___f_918_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_918_, 0, v_toFunctor_909_);
v___f_919_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_919_, 0, v_toFunctor_909_);
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v___f_918_);
lean_ctor_set(v___x_920_, 1, v___f_919_);
v___f_921_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_921_, 0, v_toSeqRight_912_);
v___f_922_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_922_, 0, v_toSeqLeft_911_);
v___f_923_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_923_, 0, v_toSeq_910_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 4, v___f_921_);
lean_ctor_set(v___x_914_, 3, v___f_922_);
lean_ctor_set(v___x_914_, 2, v___f_923_);
lean_ctor_set(v___x_914_, 1, v___f_916_);
lean_ctor_set(v___x_914_, 0, v___x_920_);
v___x_925_ = v___x_914_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_920_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v___f_916_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v___f_923_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v___f_922_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v___f_921_);
v___x_925_ = v_reuseFailAlloc_950_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_object* v___x_927_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 1, v___f_917_);
lean_ctor_set(v___x_907_, 0, v___x_925_);
v___x_927_ = v___x_907_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_925_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___f_917_);
v___x_927_ = v_reuseFailAlloc_949_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_928_ = l_StateRefT_x27_instMonad___redArg(v___x_927_);
v___x_929_ = lean_array_get_size(v_acc_881_);
v___x_930_ = lean_array_get_size(v_declInfos_878_);
v___x_931_ = lean_nat_dec_lt(v___x_929_, v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; 
lean_dec_ref(v___x_928_);
lean_dec_ref(v_declInfos_878_);
lean_inc(v___y_886_);
lean_inc_ref(v___y_885_);
lean_inc(v___y_884_);
lean_inc_ref(v___y_883_);
lean_inc(v___y_882_);
v___x_932_ = lean_apply_7(v_k_879_, v_acc_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, lean_box(0));
return v___x_932_;
}
else
{
lean_object* v___f_933_; lean_object* v___x_934_; uint8_t v___x_935_; lean_object* v___f_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v_snd_941_; lean_object* v_fst_942_; lean_object* v_fst_943_; lean_object* v_snd_944_; lean_object* v___x_945_; 
v___f_933_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___lam__0___boxed), 8, 1);
lean_closure_set(v___f_933_, 0, v___x_928_);
v___x_934_ = lean_box(0);
v___x_935_ = 0;
v___f_936_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_936_, 0, v___f_933_);
v___x_937_ = lean_box(v___x_935_);
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v___f_936_);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_934_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = lean_array_get(v___x_939_, v_declInfos_878_, v___x_929_);
lean_dec_ref_known(v___x_939_, 2);
v_snd_941_ = lean_ctor_get(v___x_940_, 1);
lean_inc(v_snd_941_);
v_fst_942_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_fst_942_);
lean_dec(v___x_940_);
v_fst_943_ = lean_ctor_get(v_snd_941_, 0);
lean_inc(v_fst_943_);
v_snd_944_ = lean_ctor_get(v_snd_941_, 1);
lean_inc(v_snd_944_);
lean_dec(v_snd_941_);
lean_inc(v___y_886_);
lean_inc_ref(v___y_885_);
lean_inc(v___y_884_);
lean_inc_ref(v___y_883_);
lean_inc(v___y_882_);
lean_inc_ref(v_acc_881_);
v___x_945_ = lean_apply_7(v_snd_944_, v_acc_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, lean_box(0));
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; uint8_t v___x_947_; lean_object* v___x_948_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
lean_dec_ref_known(v___x_945_, 1);
v___x_947_ = lean_unbox(v_fst_943_);
lean_dec(v_fst_943_);
v___x_948_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34(v_acc_881_, v_declInfos_878_, v_k_879_, v_kind_880_, v_fst_942_, v___x_947_, v_a_946_, v_kind_880_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
return v___x_948_;
}
else
{
lean_dec(v_fst_943_);
lean_dec(v_fst_942_);
lean_dec_ref(v_acc_881_);
lean_dec_ref(v_k_879_);
lean_dec_ref(v_declInfos_878_);
return v___x_945_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___lam__0(lean_object* v_acc_955_, lean_object* v_declInfos_956_, lean_object* v_k_957_, uint8_t v_kind_958_, lean_object* v___y_959_, lean_object* v_b_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_array_push(v_acc_955_, v_b_960_);
v___x_967_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(v_declInfos_956_, v_k_957_, v_kind_958_, v___x_966_, v___y_959_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___boxed(lean_object* v_acc_968_, lean_object* v_declInfos_969_, lean_object* v_k_970_, lean_object* v_kind_971_, lean_object* v_name_972_, lean_object* v_bi_973_, lean_object* v_type_974_, lean_object* v_kind_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
uint8_t v_kind_boxed_982_; uint8_t v_bi_boxed_983_; uint8_t v_kind_boxed_984_; lean_object* v_res_985_; 
v_kind_boxed_982_ = lean_unbox(v_kind_971_);
v_bi_boxed_983_ = lean_unbox(v_bi_973_);
v_kind_boxed_984_ = lean_unbox(v_kind_975_);
v_res_985_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34(v_acc_968_, v_declInfos_969_, v_k_970_, v_kind_boxed_982_, v_name_972_, v_bi_boxed_983_, v_type_974_, v_kind_boxed_984_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___boxed(lean_object* v_declInfos_986_, lean_object* v_k_987_, lean_object* v_kind_988_, lean_object* v_acc_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
uint8_t v_kind_boxed_996_; lean_object* v_res_997_; 
v_kind_boxed_996_ = lean_unbox(v_kind_988_);
v_res_997_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(v_declInfos_986_, v_k_987_, v_kind_boxed_996_, v_acc_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14(lean_object* v_declInfos_1000_, lean_object* v_k_1001_, uint8_t v_kind_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___closed__0));
v___x_1010_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(v_declInfos_1000_, v_k_1001_, v_kind_1002_, v___x_1009_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___boxed(lean_object* v_declInfos_1011_, lean_object* v_k_1012_, lean_object* v_kind_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
uint8_t v_kind_boxed_1020_; lean_object* v_res_1021_; 
v_kind_boxed_1020_ = lean_unbox(v_kind_1013_);
v_res_1021_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14(v_declInfos_1011_, v_k_1012_, v_kind_boxed_1020_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10(lean_object* v_declInfos_1022_, lean_object* v_k_1023_, uint8_t v_kind_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
size_t v_sz_1031_; size_t v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_sz_1031_ = lean_array_size(v_declInfos_1022_);
v___x_1032_ = ((size_t)0ULL);
v___x_1033_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(v_sz_1031_, v___x_1032_, v_declInfos_1022_);
v___x_1034_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14(v___x_1033_, v_k_1023_, v_kind_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___boxed(lean_object* v_declInfos_1035_, lean_object* v_k_1036_, lean_object* v_kind_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
uint8_t v_kind_boxed_1044_; lean_object* v_res_1045_; 
v_kind_boxed_1044_ = lean_unbox(v_kind_1037_);
v_res_1045_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10(v_declInfos_1035_, v_k_1036_, v_kind_boxed_1044_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0(lean_object* v_snd_1046_, lean_object* v_x_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v_snd_1046_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0___boxed(lean_object* v_snd_1055_, lean_object* v_x_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0(v_snd_1055_, v_x_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v_x_1056_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9(size_t v_sz_1064_, size_t v_i_1065_, lean_object* v_bs_1066_){
_start:
{
uint8_t v___x_1067_; 
v___x_1067_ = lean_usize_dec_lt(v_i_1065_, v_sz_1064_);
if (v___x_1067_ == 0)
{
return v_bs_1066_;
}
else
{
lean_object* v_v_1068_; lean_object* v_fst_1069_; lean_object* v_snd_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1084_; 
v_v_1068_ = lean_array_uget(v_bs_1066_, v_i_1065_);
v_fst_1069_ = lean_ctor_get(v_v_1068_, 0);
v_snd_1070_ = lean_ctor_get(v_v_1068_, 1);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_v_1068_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1072_ = v_v_1068_;
v_isShared_1073_ = v_isSharedCheck_1084_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_snd_1070_);
lean_inc(v_fst_1069_);
lean_dec(v_v_1068_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1084_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v_bs_x27_1075_; lean_object* v___f_1076_; lean_object* v___x_1078_; 
v___x_1074_ = lean_unsigned_to_nat(0u);
v_bs_x27_1075_ = lean_array_uset(v_bs_1066_, v_i_1065_, v___x_1074_);
v___f_1076_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1076_, 0, v_snd_1070_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 1, v___f_1076_);
v___x_1078_ = v___x_1072_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_fst_1069_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v___f_1076_);
v___x_1078_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
size_t v___x_1079_; size_t v___x_1080_; lean_object* v___x_1081_; 
v___x_1079_ = ((size_t)1ULL);
v___x_1080_ = lean_usize_add(v_i_1065_, v___x_1079_);
v___x_1081_ = lean_array_uset(v_bs_x27_1075_, v_i_1065_, v___x_1078_);
v_i_1065_ = v___x_1080_;
v_bs_1066_ = v___x_1081_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___boxed(lean_object* v_sz_1085_, lean_object* v_i_1086_, lean_object* v_bs_1087_){
_start:
{
size_t v_sz_boxed_1088_; size_t v_i_boxed_1089_; lean_object* v_res_1090_; 
v_sz_boxed_1088_ = lean_unbox_usize(v_sz_1085_);
lean_dec(v_sz_1085_);
v_i_boxed_1089_ = lean_unbox_usize(v_i_1086_);
lean_dec(v_i_1086_);
v_res_1090_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9(v_sz_boxed_1088_, v_i_boxed_1089_, v_bs_1087_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5(lean_object* v_declInfos_1091_, lean_object* v_k_1092_, uint8_t v_kind_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
size_t v_sz_1100_; size_t v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_sz_1100_ = lean_array_size(v_declInfos_1091_);
v___x_1101_ = ((size_t)0ULL);
v___x_1102_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9(v_sz_1100_, v___x_1101_, v_declInfos_1091_);
v___x_1103_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10(v___x_1102_, v_k_1092_, v_kind_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5___boxed(lean_object* v_declInfos_1104_, lean_object* v_k_1105_, lean_object* v_kind_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
uint8_t v_kind_boxed_1113_; lean_object* v_res_1114_; 
v_kind_boxed_1113_ = lean_unbox(v_kind_1106_);
v_res_1114_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5(v_declInfos_1104_, v_k_1105_, v_kind_boxed_1113_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4(lean_object* v___x_1118_, size_t v_sz_1119_, size_t v_i_1120_, lean_object* v_bs_1121_){
_start:
{
uint8_t v___x_1122_; 
v___x_1122_ = lean_usize_dec_lt(v_i_1120_, v_sz_1119_);
if (v___x_1122_ == 0)
{
lean_dec_ref(v___x_1118_);
return v_bs_1121_;
}
else
{
lean_object* v___x_1123_; lean_object* v_bs_x27_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; size_t v___x_1127_; size_t v___x_1128_; lean_object* v___x_1129_; 
v___x_1123_ = lean_unsigned_to_nat(0u);
v_bs_x27_1124_ = lean_array_uset(v_bs_1121_, v_i_1120_, v___x_1123_);
v___x_1125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__1));
lean_inc_ref(v___x_1118_);
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
lean_ctor_set(v___x_1126_, 1, v___x_1118_);
v___x_1127_ = ((size_t)1ULL);
v___x_1128_ = lean_usize_add(v_i_1120_, v___x_1127_);
v___x_1129_ = lean_array_uset(v_bs_x27_1124_, v_i_1120_, v___x_1126_);
v_i_1120_ = v___x_1128_;
v_bs_1121_ = v___x_1129_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___boxed(lean_object* v___x_1131_, lean_object* v_sz_1132_, lean_object* v_i_1133_, lean_object* v_bs_1134_){
_start:
{
size_t v_sz_boxed_1135_; size_t v_i_boxed_1136_; lean_object* v_res_1137_; 
v_sz_boxed_1135_ = lean_unbox_usize(v_sz_1132_);
lean_dec(v_sz_1132_);
v_i_boxed_1136_ = lean_unbox_usize(v_i_1133_);
lean_dec(v_i_1133_);
v_res_1137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4(v___x_1131_, v_sz_boxed_1135_, v_i_boxed_1136_, v_bs_1134_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2(lean_object* v___x_1141_, lean_object* v_z_1142_, lean_object* v___y_1143_, size_t v___x_1144_, lean_object* v___f_1145_, lean_object* v___x_1146_, uint8_t v___x_1147_, lean_object* v_other_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; size_t v_sz_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; lean_object* v___x_1161_; 
v___x_1155_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1));
v___x_1156_ = l_Lean_mkConst(v___x_1155_, v___x_1141_);
lean_inc_ref(v_z_1142_);
v___x_1157_ = l_Lean_Expr_app___override(v___x_1156_, v_z_1142_);
v_sz_1158_ = lean_array_size(v___y_1143_);
v___x_1159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4(v___x_1157_, v_sz_1158_, v___x_1144_, v___y_1143_);
v___x_1160_ = 0;
v___x_1161_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5(v___x_1159_, v___f_1145_, v___x_1160_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; uint8_t v___x_1169_; lean_object* v___x_1170_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref_known(v___x_1161_, 1);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___boxed(lean_object* v___x_1196_, lean_object* v_z_1197_, lean_object* v___y_1198_, lean_object* v___x_1199_, lean_object* v___f_1200_, lean_object* v___x_1201_, lean_object* v___x_1202_, lean_object* v_other_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
size_t v___x_21739__boxed_1210_; uint8_t v___x_21742__boxed_1211_; lean_object* v_res_1212_; 
v___x_21739__boxed_1210_ = lean_unbox_usize(v___x_1199_);
lean_dec(v___x_1199_);
v___x_21742__boxed_1211_ = lean_unbox(v___x_1202_);
v_res_1212_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2(v___x_1196_, v_z_1197_, v___y_1198_, v___x_21739__boxed_1210_, v___f_1200_, v___x_1201_, v___x_21742__boxed_1211_, v_other_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___x_1201_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0(lean_object* v_k_1213_, lean_object* v___y_1214_, lean_object* v_b_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0___boxed(lean_object* v_k_1222_, lean_object* v___y_1223_, lean_object* v_b_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0(v_k_1222_, v___y_1223_, v_b_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1223_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(lean_object* v_name_1231_, uint8_t v_bi_1232_, lean_object* v_type_1233_, lean_object* v_k_1234_, uint8_t v_kind_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___f_1242_; lean_object* v___x_1243_; 
lean_inc(v___y_1236_);
v___f_1242_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0___boxed), 8, 2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___boxed(lean_object* v_name_1252_, lean_object* v_bi_1253_, lean_object* v_type_1254_, lean_object* v_k_1255_, lean_object* v_kind_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
uint8_t v_bi_boxed_1263_; uint8_t v_kind_boxed_1264_; lean_object* v_res_1265_; 
v_bi_boxed_1263_ = lean_unbox(v_bi_1253_);
v_kind_boxed_1264_ = lean_unbox(v_kind_1256_);
v_res_1265_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(v_name_1252_, v_bi_boxed_1263_, v_type_1254_, v_k_1255_, v_kind_boxed_1264_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(lean_object* v_name_1266_, lean_object* v_type_1267_, lean_object* v_k_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
uint8_t v___x_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; 
v___x_1275_ = 0;
v___x_1276_ = 0;
v___x_1277_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(v_name_1266_, v___x_1275_, v_type_1267_, v_k_1268_, v___x_1276_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___redArg___boxed(lean_object* v_name_1278_, lean_object* v_type_1279_, lean_object* v_k_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v_name_1278_, v_type_1279_, v_k_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3(lean_object* v___x_1291_, lean_object* v___y_1292_, size_t v___x_1293_, lean_object* v_a_1294_, uint8_t v___x_1295_, lean_object* v_fst_1296_, lean_object* v___x_1297_, lean_object* v_z_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___f_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___f_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1305_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2));
v___x_1306_ = lean_unsigned_to_nat(1u);
v___x_1307_ = lean_box_usize(v___x_1293_);
v___x_1308_ = lean_box(v___x_1295_);
lean_inc_ref(v___y_1292_);
lean_inc_ref_n(v_z_1298_, 2);
lean_inc_n(v___x_1291_, 2);
v___f_1309_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1309_, 0, v___x_1306_);
lean_closure_set(v___f_1309_, 1, v___x_1291_);
lean_closure_set(v___f_1309_, 2, v_z_1298_);
lean_closure_set(v___f_1309_, 3, v___y_1292_);
lean_closure_set(v___f_1309_, 4, v___x_1307_);
lean_closure_set(v___f_1309_, 5, v_a_1294_);
lean_closure_set(v___f_1309_, 6, v___x_1308_);
v___x_1310_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11);
v___x_1311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v___x_1291_);
v___x_1312_ = l_Lean_mkConst(v___x_1305_, v___x_1311_);
v___x_1313_ = l_Lean_mkNatLit(v_fst_1296_);
v___x_1314_ = lean_box_usize(v___x_1293_);
v___x_1315_ = lean_box(v___x_1295_);
lean_inc_ref(v___x_1313_);
v___f_1316_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___boxed), 14, 7);
lean_closure_set(v___f_1316_, 0, v___x_1291_);
lean_closure_set(v___f_1316_, 1, v_z_1298_);
lean_closure_set(v___f_1316_, 2, v___y_1292_);
lean_closure_set(v___f_1316_, 3, v___x_1314_);
lean_closure_set(v___f_1316_, 4, v___f_1309_);
lean_closure_set(v___f_1316_, 5, v___x_1313_);
lean_closure_set(v___f_1316_, 6, v___x_1315_);
v___x_1317_ = l_Lean_mkApp3(v___x_1312_, v___x_1297_, v___x_1313_, v_z_1298_);
v___x_1318_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1));
v___x_1319_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v___x_1318_, v___x_1317_, v___f_1316_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___boxed(lean_object* v___x_1320_, lean_object* v___y_1321_, lean_object* v___x_1322_, lean_object* v_a_1323_, lean_object* v___x_1324_, lean_object* v_fst_1325_, lean_object* v___x_1326_, lean_object* v_z_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
size_t v___x_21952__boxed_1334_; uint8_t v___x_21954__boxed_1335_; lean_object* v_res_1336_; 
v___x_21952__boxed_1334_ = lean_unbox_usize(v___x_1322_);
lean_dec(v___x_1322_);
v___x_21954__boxed_1335_ = lean_unbox(v___x_1324_);
v_res_1336_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3(v___x_1320_, v___y_1321_, v___x_21952__boxed_1334_, v_a_1323_, v___x_21954__boxed_1335_, v_fst_1325_, v___x_1326_, v_z_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__10(lean_object* v_x_1337_, lean_object* v_x_1338_){
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
lean_dec_ref_known(v_x_1338_, 3);
v___x_1341_ = lean_array_push(v_x_1337_, v_key_1339_);
v_x_1337_ = v___x_1341_;
v_x_1338_ = v_tail_1340_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__11(lean_object* v_as_1343_, size_t v_i_1344_, size_t v_stop_1345_, lean_object* v_b_1346_){
_start:
{
uint8_t v___x_1347_; 
v___x_1347_ = lean_usize_dec_eq(v_i_1344_, v_stop_1345_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; size_t v___x_1350_; size_t v___x_1351_; 
v___x_1348_ = lean_array_uget_borrowed(v_as_1343_, v_i_1344_);
lean_inc(v___x_1348_);
v___x_1349_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__10(v_b_1346_, v___x_1348_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__11___boxed(lean_object* v_as_1353_, lean_object* v_i_1354_, lean_object* v_stop_1355_, lean_object* v_b_1356_){
_start:
{
size_t v_i_boxed_1357_; size_t v_stop_boxed_1358_; lean_object* v_res_1359_; 
v_i_boxed_1357_ = lean_unbox_usize(v_i_1354_);
lean_dec(v_i_1354_);
v_stop_boxed_1358_ = lean_unbox_usize(v_stop_1355_);
lean_dec(v_stop_1355_);
v_res_1359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__11(v_as_1353_, v_i_boxed_1357_, v_stop_boxed_1358_, v_b_1356_);
lean_dec_ref(v_as_1353_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(lean_object* v_msgData_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___x_1366_; lean_object* v_env_1367_; lean_object* v___x_1368_; lean_object* v_mctx_1369_; lean_object* v_lctx_1370_; lean_object* v_options_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1366_ = lean_st_ref_get(v___y_1364_);
v_env_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc_ref(v_env_1367_);
lean_dec(v___x_1366_);
v___x_1368_ = lean_st_ref_get(v___y_1362_);
v_mctx_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc_ref(v_mctx_1369_);
lean_dec(v___x_1368_);
v_lctx_1370_ = lean_ctor_get(v___y_1361_, 2);
v_options_1371_ = lean_ctor_get(v___y_1363_, 2);
lean_inc_ref(v_options_1371_);
lean_inc_ref(v_lctx_1370_);
v___x_1372_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1372_, 0, v_env_1367_);
lean_ctor_set(v___x_1372_, 1, v_mctx_1369_);
lean_ctor_set(v___x_1372_, 2, v_lctx_1370_);
lean_ctor_set(v___x_1372_, 3, v_options_1371_);
v___x_1373_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
lean_ctor_set(v___x_1373_, 1, v_msgData_1360_);
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17___boxed(lean_object* v_msgData_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(v_msgData_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(lean_object* v_msg_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_ref_1388_; lean_object* v___x_1389_; lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1398_; 
v_ref_1388_ = lean_ctor_get(v___y_1385_, 5);
v___x_1389_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(v_msg_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1392_ = v___x_1389_;
v_isShared_1393_ = v_isSharedCheck_1398_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1389_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1398_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1396_; 
lean_inc(v_ref_1388_);
v___x_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1394_, 0, v_ref_1388_);
lean_ctor_set(v___x_1394_, 1, v_a_1390_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set_tag(v___x_1392_, 1);
lean_ctor_set(v___x_1392_, 0, v___x_1394_);
v___x_1396_ = v___x_1392_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9___redArg___boxed(lean_object* v_msg_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(v_msg_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__1(size_t v_sz_1406_, size_t v_i_1407_, lean_object* v_bs_1408_){
_start:
{
uint8_t v___x_1409_; 
v___x_1409_ = lean_usize_dec_lt(v_i_1407_, v_sz_1406_);
if (v___x_1409_ == 0)
{
return v_bs_1408_;
}
else
{
lean_object* v_v_1410_; lean_object* v___x_1411_; lean_object* v_bs_x27_1412_; lean_object* v___x_1413_; size_t v___x_1414_; size_t v___x_1415_; lean_object* v___x_1416_; 
v_v_1410_ = lean_array_uget(v_bs_1408_, v_i_1407_);
v___x_1411_ = lean_unsigned_to_nat(0u);
v_bs_x27_1412_ = lean_array_uset(v_bs_1408_, v_i_1407_, v___x_1411_);
v___x_1413_ = l_Lean_mkFVar(v_v_1410_);
v___x_1414_ = ((size_t)1ULL);
v___x_1415_ = lean_usize_add(v_i_1407_, v___x_1414_);
v___x_1416_ = lean_array_uset(v_bs_x27_1412_, v_i_1407_, v___x_1413_);
v_i_1407_ = v___x_1415_;
v_bs_1408_ = v___x_1416_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__1___boxed(lean_object* v_sz_1418_, lean_object* v_i_1419_, lean_object* v_bs_1420_){
_start:
{
size_t v_sz_boxed_1421_; size_t v_i_boxed_1422_; lean_object* v_res_1423_; 
v_sz_boxed_1421_ = lean_unbox_usize(v_sz_1418_);
lean_dec(v_sz_1418_);
v_i_boxed_1422_ = lean_unbox_usize(v_i_1419_);
lean_dec(v_i_1419_);
v_res_1423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__1(v_sz_boxed_1421_, v_i_boxed_1422_, v_bs_1420_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__12(lean_object* v_x_1424_, lean_object* v_x_1425_){
_start:
{
if (lean_obj_tag(v_x_1425_) == 0)
{
return v_x_1424_;
}
else
{
lean_object* v_key_1426_; lean_object* v_tail_1427_; lean_object* v___x_1428_; 
v_key_1426_ = lean_ctor_get(v_x_1425_, 0);
lean_inc(v_key_1426_);
v_tail_1427_ = lean_ctor_get(v_x_1425_, 2);
lean_inc(v_tail_1427_);
lean_dec_ref_known(v_x_1425_, 3);
v___x_1428_ = lean_array_push(v_x_1424_, v_key_1426_);
v_x_1424_ = v___x_1428_;
v_x_1425_ = v_tail_1427_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__13(lean_object* v_as_1430_, size_t v_i_1431_, size_t v_stop_1432_, lean_object* v_b_1433_){
_start:
{
uint8_t v___x_1434_; 
v___x_1434_ = lean_usize_dec_eq(v_i_1431_, v_stop_1432_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1436_; size_t v___x_1437_; size_t v___x_1438_; 
v___x_1435_ = lean_array_uget_borrowed(v_as_1430_, v_i_1431_);
lean_inc(v___x_1435_);
v___x_1436_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__12(v_b_1433_, v___x_1435_);
v___x_1437_ = ((size_t)1ULL);
v___x_1438_ = lean_usize_add(v_i_1431_, v___x_1437_);
v_i_1431_ = v___x_1438_;
v_b_1433_ = v___x_1436_;
goto _start;
}
else
{
return v_b_1433_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__13___boxed(lean_object* v_as_1440_, lean_object* v_i_1441_, lean_object* v_stop_1442_, lean_object* v_b_1443_){
_start:
{
size_t v_i_boxed_1444_; size_t v_stop_boxed_1445_; lean_object* v_res_1446_; 
v_i_boxed_1444_ = lean_unbox_usize(v_i_1441_);
lean_dec(v_i_1441_);
v_stop_boxed_1445_ = lean_unbox_usize(v_stop_1442_);
lean_dec(v_stop_1442_);
v_res_1446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__13(v_as_1440_, v_i_boxed_1444_, v_stop_boxed_1445_, v_b_1443_);
lean_dec_ref(v_as_1440_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__8(size_t v_sz_1447_, size_t v_i_1448_, lean_object* v_bs_1449_){
_start:
{
uint8_t v___x_1450_; 
v___x_1450_ = lean_usize_dec_lt(v_i_1448_, v_sz_1447_);
if (v___x_1450_ == 0)
{
return v_bs_1449_;
}
else
{
lean_object* v_v_1451_; lean_object* v___x_1452_; lean_object* v_bs_x27_1453_; lean_object* v___x_1454_; size_t v___x_1455_; size_t v___x_1456_; lean_object* v___x_1457_; 
v_v_1451_ = lean_array_uget(v_bs_1449_, v_i_1448_);
v___x_1452_ = lean_unsigned_to_nat(0u);
v_bs_x27_1453_ = lean_array_uset(v_bs_1449_, v_i_1448_, v___x_1452_);
v___x_1454_ = l_Lean_Expr_fvarId_x21(v_v_1451_);
lean_dec(v_v_1451_);
v___x_1455_ = ((size_t)1ULL);
v___x_1456_ = lean_usize_add(v_i_1448_, v___x_1455_);
v___x_1457_ = lean_array_uset(v_bs_x27_1453_, v_i_1448_, v___x_1454_);
v_i_1448_ = v___x_1456_;
v_bs_1449_ = v___x_1457_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__8___boxed(lean_object* v_sz_1459_, lean_object* v_i_1460_, lean_object* v_bs_1461_){
_start:
{
size_t v_sz_boxed_1462_; size_t v_i_boxed_1463_; lean_object* v_res_1464_; 
v_sz_boxed_1462_ = lean_unbox_usize(v_sz_1459_);
lean_dec(v_sz_1459_);
v_i_boxed_1463_ = lean_unbox_usize(v_i_1460_);
lean_dec(v_i_1460_);
v_res_1464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__8(v_sz_boxed_1462_, v_i_boxed_1463_, v_bs_1461_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32___redArg(lean_object* v_x_1465_, lean_object* v_x_1466_, lean_object* v_x_1467_, lean_object* v_x_1468_){
_start:
{
lean_object* v_ks_1469_; lean_object* v_vs_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1494_; 
v_ks_1469_ = lean_ctor_get(v_x_1465_, 0);
v_vs_1470_ = lean_ctor_get(v_x_1465_, 1);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_x_1465_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1472_ = v_x_1465_;
v_isShared_1473_ = v_isSharedCheck_1494_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_vs_1470_);
lean_inc(v_ks_1469_);
lean_dec(v_x_1465_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1494_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; uint8_t v___x_1475_; 
v___x_1474_ = lean_array_get_size(v_ks_1469_);
v___x_1475_ = lean_nat_dec_lt(v_x_1466_, v___x_1474_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
lean_dec(v_x_1466_);
v___x_1476_ = lean_array_push(v_ks_1469_, v_x_1467_);
v___x_1477_ = lean_array_push(v_vs_1470_, v_x_1468_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 1, v___x_1477_);
lean_ctor_set(v___x_1472_, 0, v___x_1476_);
v___x_1479_ = v___x_1472_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
else
{
lean_object* v_k_x27_1481_; uint8_t v___x_1482_; 
v_k_x27_1481_ = lean_array_fget_borrowed(v_ks_1469_, v_x_1466_);
v___x_1482_ = l_Lean_instBEqMVarId_beq(v_x_1467_, v_k_x27_1481_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1484_; 
if (v_isShared_1473_ == 0)
{
v___x_1484_ = v___x_1472_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_ks_1469_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_vs_1470_);
v___x_1484_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = lean_unsigned_to_nat(1u);
v___x_1486_ = lean_nat_add(v_x_1466_, v___x_1485_);
lean_dec(v_x_1466_);
v_x_1465_ = v___x_1484_;
v_x_1466_ = v___x_1486_;
goto _start;
}
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1489_ = lean_array_fset(v_ks_1469_, v_x_1466_, v_x_1467_);
v___x_1490_ = lean_array_fset(v_vs_1470_, v_x_1466_, v_x_1468_);
lean_dec(v_x_1466_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 1, v___x_1490_);
lean_ctor_set(v___x_1472_, 0, v___x_1489_);
v___x_1492_ = v___x_1472_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30___redArg(lean_object* v_n_1495_, lean_object* v_k_1496_, lean_object* v_v_1497_){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = lean_unsigned_to_nat(0u);
v___x_1499_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32___redArg(v_n_1495_, v___x_1498_, v_k_1496_, v_v_1497_);
return v___x_1499_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(lean_object* v_x_1501_, size_t v_x_1502_, size_t v_x_1503_, lean_object* v_x_1504_, lean_object* v_x_1505_){
_start:
{
if (lean_obj_tag(v_x_1501_) == 0)
{
lean_object* v_es_1506_; size_t v___x_1507_; size_t v___x_1508_; lean_object* v_j_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
v_es_1506_ = lean_ctor_get(v_x_1501_, 0);
v___x_1507_ = ((size_t)31ULL);
v___x_1508_ = lean_usize_land(v_x_1502_, v___x_1507_);
v_j_1509_ = lean_usize_to_nat(v___x_1508_);
v___x_1510_ = lean_array_get_size(v_es_1506_);
v___x_1511_ = lean_nat_dec_lt(v_j_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_dec(v_j_1509_);
lean_dec(v_x_1505_);
lean_dec(v_x_1504_);
return v_x_1501_;
}
else
{
lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1550_; 
lean_inc_ref(v_es_1506_);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_x_1501_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v_x_1501_, 0);
lean_dec(v_unused_1551_);
v___x_1513_ = v_x_1501_;
v_isShared_1514_ = v_isSharedCheck_1550_;
goto v_resetjp_1512_;
}
else
{
lean_dec(v_x_1501_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1550_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v_v_1515_; lean_object* v___x_1516_; lean_object* v_xs_x27_1517_; lean_object* v___y_1519_; 
v_v_1515_ = lean_array_fget(v_es_1506_, v_j_1509_);
v___x_1516_ = lean_box(0);
v_xs_x27_1517_ = lean_array_fset(v_es_1506_, v_j_1509_, v___x_1516_);
switch(lean_obj_tag(v_v_1515_))
{
case 0:
{
lean_object* v_key_1524_; lean_object* v_val_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1535_; 
v_key_1524_ = lean_ctor_get(v_v_1515_, 0);
v_val_1525_ = lean_ctor_get(v_v_1515_, 1);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_v_1515_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1527_ = v_v_1515_;
v_isShared_1528_ = v_isSharedCheck_1535_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_val_1525_);
lean_inc(v_key_1524_);
lean_dec(v_v_1515_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1535_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
uint8_t v___x_1529_; 
v___x_1529_ = l_Lean_instBEqMVarId_beq(v_x_1504_, v_key_1524_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_del_object(v___x_1527_);
v___x_1530_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1524_, v_val_1525_, v_x_1504_, v_x_1505_);
v___x_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
v___y_1519_ = v___x_1531_;
goto v___jp_1518_;
}
else
{
lean_object* v___x_1533_; 
lean_dec(v_val_1525_);
lean_dec(v_key_1524_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 1, v_x_1505_);
lean_ctor_set(v___x_1527_, 0, v_x_1504_);
v___x_1533_ = v___x_1527_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_x_1504_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_x_1505_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
v___y_1519_ = v___x_1533_;
goto v___jp_1518_;
}
}
}
}
case 1:
{
lean_object* v_node_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1548_; 
v_node_1536_ = lean_ctor_get(v_v_1515_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_v_1515_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1538_ = v_v_1515_;
v_isShared_1539_ = v_isSharedCheck_1548_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_node_1536_);
lean_dec(v_v_1515_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1548_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
size_t v___x_1540_; size_t v___x_1541_; size_t v___x_1542_; size_t v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1540_ = ((size_t)5ULL);
v___x_1541_ = lean_usize_shift_right(v_x_1502_, v___x_1540_);
v___x_1542_ = ((size_t)1ULL);
v___x_1543_ = lean_usize_add(v_x_1503_, v___x_1542_);
v___x_1544_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_node_1536_, v___x_1541_, v___x_1543_, v_x_1504_, v_x_1505_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1544_);
v___x_1546_ = v___x_1538_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
v___y_1519_ = v___x_1546_;
goto v___jp_1518_;
}
}
}
default: 
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v_x_1504_);
lean_ctor_set(v___x_1549_, 1, v_x_1505_);
v___y_1519_ = v___x_1549_;
goto v___jp_1518_;
}
}
v___jp_1518_:
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1520_ = lean_array_fset(v_xs_x27_1517_, v_j_1509_, v___y_1519_);
lean_dec(v_j_1509_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___x_1520_);
v___x_1522_ = v___x_1513_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
}
else
{
lean_object* v_ks_1552_; lean_object* v_vs_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1573_; 
v_ks_1552_ = lean_ctor_get(v_x_1501_, 0);
v_vs_1553_ = lean_ctor_get(v_x_1501_, 1);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_x_1501_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1555_ = v_x_1501_;
v_isShared_1556_ = v_isSharedCheck_1573_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_vs_1553_);
lean_inc(v_ks_1552_);
lean_dec(v_x_1501_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1573_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_ks_1552_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_vs_1553_);
v___x_1558_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v_newNode_1559_; uint8_t v___y_1561_; size_t v___x_1567_; uint8_t v___x_1568_; 
v_newNode_1559_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30___redArg(v___x_1558_, v_x_1504_, v_x_1505_);
v___x_1567_ = ((size_t)7ULL);
v___x_1568_ = lean_usize_dec_le(v___x_1567_, v_x_1503_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1569_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1559_);
v___x_1570_ = lean_unsigned_to_nat(4u);
v___x_1571_ = lean_nat_dec_lt(v___x_1569_, v___x_1570_);
lean_dec(v___x_1569_);
v___y_1561_ = v___x_1571_;
goto v___jp_1560_;
}
else
{
v___y_1561_ = v___x_1568_;
goto v___jp_1560_;
}
v___jp_1560_:
{
if (v___y_1561_ == 0)
{
lean_object* v_ks_1562_; lean_object* v_vs_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_ks_1562_ = lean_ctor_get(v_newNode_1559_, 0);
lean_inc_ref(v_ks_1562_);
v_vs_1563_ = lean_ctor_get(v_newNode_1559_, 1);
lean_inc_ref(v_vs_1563_);
lean_dec_ref(v_newNode_1559_);
v___x_1564_ = lean_unsigned_to_nat(0u);
v___x_1565_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0);
v___x_1566_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(v_x_1503_, v_ks_1562_, v_vs_1563_, v___x_1564_, v___x_1565_);
lean_dec_ref(v_vs_1563_);
lean_dec_ref(v_ks_1562_);
return v___x_1566_;
}
else
{
return v_newNode_1559_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(size_t v_depth_1574_, lean_object* v_keys_1575_, lean_object* v_vals_1576_, lean_object* v_i_1577_, lean_object* v_entries_1578_){
_start:
{
lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1579_ = lean_array_get_size(v_keys_1575_);
v___x_1580_ = lean_nat_dec_lt(v_i_1577_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_dec(v_i_1577_);
return v_entries_1578_;
}
else
{
lean_object* v_k_1581_; lean_object* v_v_1582_; uint64_t v___x_1583_; size_t v_h_1584_; size_t v___x_1585_; lean_object* v___x_1586_; size_t v___x_1587_; size_t v___x_1588_; size_t v___x_1589_; size_t v_h_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v_k_1581_ = lean_array_fget_borrowed(v_keys_1575_, v_i_1577_);
v_v_1582_ = lean_array_fget_borrowed(v_vals_1576_, v_i_1577_);
v___x_1583_ = l_Lean_instHashableMVarId_hash(v_k_1581_);
v_h_1584_ = lean_uint64_to_usize(v___x_1583_);
v___x_1585_ = ((size_t)5ULL);
v___x_1586_ = lean_unsigned_to_nat(1u);
v___x_1587_ = ((size_t)1ULL);
v___x_1588_ = lean_usize_sub(v_depth_1574_, v___x_1587_);
v___x_1589_ = lean_usize_mul(v___x_1585_, v___x_1588_);
v_h_1590_ = lean_usize_shift_right(v_h_1584_, v___x_1589_);
v___x_1591_ = lean_nat_add(v_i_1577_, v___x_1586_);
lean_dec(v_i_1577_);
lean_inc(v_v_1582_);
lean_inc(v_k_1581_);
v___x_1592_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_entries_1578_, v_h_1590_, v_depth_1574_, v_k_1581_, v_v_1582_);
v_i_1577_ = v___x_1591_;
v_entries_1578_ = v___x_1592_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg___boxed(lean_object* v_depth_1594_, lean_object* v_keys_1595_, lean_object* v_vals_1596_, lean_object* v_i_1597_, lean_object* v_entries_1598_){
_start:
{
size_t v_depth_boxed_1599_; lean_object* v_res_1600_; 
v_depth_boxed_1599_ = lean_unbox_usize(v_depth_1594_);
lean_dec(v_depth_1594_);
v_res_1600_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(v_depth_boxed_1599_, v_keys_1595_, v_vals_1596_, v_i_1597_, v_entries_1598_);
lean_dec_ref(v_vals_1596_);
lean_dec_ref(v_keys_1595_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___boxed(lean_object* v_x_1601_, lean_object* v_x_1602_, lean_object* v_x_1603_, lean_object* v_x_1604_, lean_object* v_x_1605_){
_start:
{
size_t v_x_22238__boxed_1606_; size_t v_x_22239__boxed_1607_; lean_object* v_res_1608_; 
v_x_22238__boxed_1606_ = lean_unbox_usize(v_x_1602_);
lean_dec(v_x_1602_);
v_x_22239__boxed_1607_ = lean_unbox_usize(v_x_1603_);
lean_dec(v_x_1603_);
v_res_1608_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_x_1601_, v_x_22238__boxed_1606_, v_x_22239__boxed_1607_, v_x_1604_, v_x_1605_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(lean_object* v_x_1609_, lean_object* v_x_1610_, lean_object* v_x_1611_){
_start:
{
uint64_t v___x_1612_; size_t v___x_1613_; size_t v___x_1614_; lean_object* v___x_1615_; 
v___x_1612_ = l_Lean_instHashableMVarId_hash(v_x_1610_);
v___x_1613_ = lean_uint64_to_usize(v___x_1612_);
v___x_1614_ = ((size_t)1ULL);
v___x_1615_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_x_1609_, v___x_1613_, v___x_1614_, v_x_1610_, v_x_1611_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(lean_object* v_mvarId_1616_, lean_object* v_val_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v___x_1620_; lean_object* v_mctx_1621_; lean_object* v_cache_1622_; lean_object* v_zetaDeltaFVarIds_1623_; lean_object* v_postponed_1624_; lean_object* v_diag_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1653_; 
v___x_1620_ = lean_st_ref_take(v___y_1618_);
v_mctx_1621_ = lean_ctor_get(v___x_1620_, 0);
v_cache_1622_ = lean_ctor_get(v___x_1620_, 1);
v_zetaDeltaFVarIds_1623_ = lean_ctor_get(v___x_1620_, 2);
v_postponed_1624_ = lean_ctor_get(v___x_1620_, 3);
v_diag_1625_ = lean_ctor_get(v___x_1620_, 4);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1627_ = v___x_1620_;
v_isShared_1628_ = v_isSharedCheck_1653_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_diag_1625_);
lean_inc(v_postponed_1624_);
lean_inc(v_zetaDeltaFVarIds_1623_);
lean_inc(v_cache_1622_);
lean_inc(v_mctx_1621_);
lean_dec(v___x_1620_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1653_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v_depth_1629_; lean_object* v_levelAssignDepth_1630_; lean_object* v_lmvarCounter_1631_; lean_object* v_mvarCounter_1632_; lean_object* v_lDecls_1633_; lean_object* v_decls_1634_; lean_object* v_userNames_1635_; lean_object* v_lAssignment_1636_; lean_object* v_eAssignment_1637_; lean_object* v_dAssignment_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1652_; 
v_depth_1629_ = lean_ctor_get(v_mctx_1621_, 0);
v_levelAssignDepth_1630_ = lean_ctor_get(v_mctx_1621_, 1);
v_lmvarCounter_1631_ = lean_ctor_get(v_mctx_1621_, 2);
v_mvarCounter_1632_ = lean_ctor_get(v_mctx_1621_, 3);
v_lDecls_1633_ = lean_ctor_get(v_mctx_1621_, 4);
v_decls_1634_ = lean_ctor_get(v_mctx_1621_, 5);
v_userNames_1635_ = lean_ctor_get(v_mctx_1621_, 6);
v_lAssignment_1636_ = lean_ctor_get(v_mctx_1621_, 7);
v_eAssignment_1637_ = lean_ctor_get(v_mctx_1621_, 8);
v_dAssignment_1638_ = lean_ctor_get(v_mctx_1621_, 9);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_mctx_1621_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1640_ = v_mctx_1621_;
v_isShared_1641_ = v_isSharedCheck_1652_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_dAssignment_1638_);
lean_inc(v_eAssignment_1637_);
lean_inc(v_lAssignment_1636_);
lean_inc(v_userNames_1635_);
lean_inc(v_decls_1634_);
lean_inc(v_lDecls_1633_);
lean_inc(v_mvarCounter_1632_);
lean_inc(v_lmvarCounter_1631_);
lean_inc(v_levelAssignDepth_1630_);
lean_inc(v_depth_1629_);
lean_dec(v_mctx_1621_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1652_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1642_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(v_eAssignment_1637_, v_mvarId_1616_, v_val_1617_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 8, v___x_1642_);
v___x_1644_ = v___x_1640_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_depth_1629_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_levelAssignDepth_1630_);
lean_ctor_set(v_reuseFailAlloc_1651_, 2, v_lmvarCounter_1631_);
lean_ctor_set(v_reuseFailAlloc_1651_, 3, v_mvarCounter_1632_);
lean_ctor_set(v_reuseFailAlloc_1651_, 4, v_lDecls_1633_);
lean_ctor_set(v_reuseFailAlloc_1651_, 5, v_decls_1634_);
lean_ctor_set(v_reuseFailAlloc_1651_, 6, v_userNames_1635_);
lean_ctor_set(v_reuseFailAlloc_1651_, 7, v_lAssignment_1636_);
lean_ctor_set(v_reuseFailAlloc_1651_, 8, v___x_1642_);
lean_ctor_set(v_reuseFailAlloc_1651_, 9, v_dAssignment_1638_);
v___x_1644_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1646_; 
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1644_);
v___x_1646_ = v___x_1627_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1644_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_cache_1622_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_zetaDeltaFVarIds_1623_);
lean_ctor_set(v_reuseFailAlloc_1650_, 3, v_postponed_1624_);
lean_ctor_set(v_reuseFailAlloc_1650_, 4, v_diag_1625_);
v___x_1646_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1647_ = lean_st_ref_set(v___y_1618_, v___x_1646_);
v___x_1648_ = lean_box(0);
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
return v___x_1649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___redArg___boxed(lean_object* v_mvarId_1654_, lean_object* v_val_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(v_mvarId_1654_, v_val_1655_, v___y_1656_);
lean_dec(v___y_1656_);
return v_res_1658_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1665_ = lean_box(0);
v___x_1666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3));
v___x_1667_ = l_Lean_mkConst(v___x_1666_, v___x_1665_);
return v___x_1667_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7(void){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = lean_unsigned_to_nat(0u);
v___x_1673_ = l_Lean_Level_ofNat(v___x_1672_);
return v___x_1673_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1674_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12);
v___x_1675_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7);
v___x_1676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1675_);
lean_ctor_set(v___x_1676_, 1, v___x_1674_);
return v___x_1676_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1677_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8);
v___x_1678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6));
v___x_1679_ = l_Lean_mkConst(v___x_1678_, v___x_1677_);
return v___x_1679_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1680_ = lean_box(0);
v___x_1681_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6));
v___x_1682_ = l_Lean_mkConst(v___x_1681_, v___x_1680_);
return v___x_1682_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11(void){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = lean_box(0);
v___x_1684_ = lean_unsigned_to_nat(16u);
v___x_1685_ = lean_mk_array(v___x_1684_, v___x_1683_);
return v___x_1685_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11);
v___x_1687_ = lean_unsigned_to_nat(0u);
v___x_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
lean_ctor_set(v___x_1688_, 1, v___x_1686_);
return v___x_1688_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13));
v___x_1691_ = l_Lean_stringToMessageData(v___x_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4(lean_object* v_fst_1692_, lean_object* v_snd_1693_, lean_object* v_goal_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
size_t v___y_1702_; uint8_t v___y_1703_; lean_object* v___y_1704_; size_t v___y_1705_; lean_object* v___y_1706_; lean_object* v_a_1707_; size_t v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___x_1897_; lean_object* v___y_1899_; lean_object* v_relevantHyps_1916_; lean_object* v_size_1917_; lean_object* v_buckets_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; 
v___x_1897_ = lean_st_ref_get(v___y_1695_);
v_relevantHyps_1916_ = lean_ctor_get(v___x_1897_, 1);
lean_inc_ref(v_relevantHyps_1916_);
lean_dec(v___x_1897_);
v_size_1917_ = lean_ctor_get(v_relevantHyps_1916_, 0);
lean_inc(v_size_1917_);
v_buckets_1918_ = lean_ctor_get(v_relevantHyps_1916_, 1);
lean_inc_ref(v_buckets_1918_);
lean_dec_ref(v_relevantHyps_1916_);
v___x_1919_ = lean_mk_empty_array_with_capacity(v_size_1917_);
lean_dec(v_size_1917_);
v___x_1920_ = lean_unsigned_to_nat(0u);
v___x_1921_ = lean_array_get_size(v_buckets_1918_);
v___x_1922_ = lean_nat_dec_lt(v___x_1920_, v___x_1921_);
if (v___x_1922_ == 0)
{
lean_dec_ref(v_buckets_1918_);
v___y_1899_ = v___x_1919_;
goto v___jp_1898_;
}
else
{
uint8_t v___x_1923_; 
v___x_1923_ = lean_nat_dec_le(v___x_1921_, v___x_1921_);
if (v___x_1923_ == 0)
{
if (v___x_1922_ == 0)
{
lean_dec_ref(v_buckets_1918_);
v___y_1899_ = v___x_1919_;
goto v___jp_1898_;
}
else
{
size_t v___x_1924_; size_t v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = ((size_t)0ULL);
v___x_1925_ = lean_usize_of_nat(v___x_1921_);
v___x_1926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__13(v_buckets_1918_, v___x_1924_, v___x_1925_, v___x_1919_);
lean_dec_ref(v_buckets_1918_);
v___y_1899_ = v___x_1926_;
goto v___jp_1898_;
}
}
else
{
size_t v___x_1927_; size_t v___x_1928_; lean_object* v___x_1929_; 
v___x_1927_ = ((size_t)0ULL);
v___x_1928_ = lean_usize_of_nat(v___x_1921_);
v___x_1929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__13(v_buckets_1918_, v___x_1927_, v___x_1928_, v___x_1919_);
lean_dec_ref(v_buckets_1918_);
v___y_1899_ = v___x_1929_;
goto v___jp_1898_;
}
}
v___jp_1701_:
{
lean_object* v_fst_1708_; lean_object* v_snd_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v_fst_1708_ = lean_ctor_get(v_a_1707_, 0);
lean_inc(v_fst_1708_);
v_snd_1709_ = lean_ctor_get(v_a_1707_, 1);
lean_inc(v_snd_1709_);
lean_dec_ref(v_a_1707_);
v___x_1710_ = l_Lean_Expr_getAppFn(v_fst_1708_);
lean_dec(v_fst_1708_);
v___x_1711_ = l_Lean_Expr_mvarId_x21(v___x_1710_);
lean_dec_ref(v___x_1710_);
v___x_1712_ = l_Lean_MVarId_getType(v___x_1711_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___f_1719_; lean_object* v___x_1720_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___x_1712_, 1);
v___x_1714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1));
v___x_1715_ = lean_box(0);
v___x_1716_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4);
v___x_1717_ = lean_box_usize(v___y_1702_);
v___x_1718_ = lean_box(v___y_1703_);
lean_inc(v_fst_1692_);
v___f_1719_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___boxed), 14, 7);
lean_closure_set(v___f_1719_, 0, v___x_1715_);
lean_closure_set(v___f_1719_, 1, v___y_1704_);
lean_closure_set(v___f_1719_, 2, v___x_1717_);
lean_closure_set(v___f_1719_, 3, v_a_1713_);
lean_closure_set(v___f_1719_, 4, v___x_1718_);
lean_closure_set(v___f_1719_, 5, v_fst_1692_);
lean_closure_set(v___f_1719_, 6, v___x_1716_);
v___x_1720_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v___x_1714_, v___x_1716_, v___f_1719_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v_fst_1722_; lean_object* v_snd_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref_known(v___x_1720_, 1);
v_fst_1722_ = lean_ctor_get(v_a_1721_, 0);
lean_inc(v_fst_1722_);
v_snd_1723_ = lean_ctor_get(v_a_1721_, 1);
lean_inc(v_snd_1723_);
lean_dec(v_a_1721_);
v___x_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1724_, 0, v_snd_1723_);
v___x_1725_ = 0;
v___x_1726_ = lean_box(0);
v___x_1727_ = l_Lean_Meta_mkFreshExprMVar(v___x_1724_, v___x_1725_, v___x_1726_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; size_t v_sz_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1727_, 1);
v___x_1729_ = l_Lean_Expr_mvarId_x21(v_a_1728_);
lean_dec(v_a_1728_);
v___x_1730_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9);
v___x_1731_ = l_Lean_mkNatLit(v_fst_1692_);
v___x_1732_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10);
lean_inc(v___x_1729_);
v___x_1733_ = l_Lean_mkMVar(v___x_1729_);
v___x_1734_ = l_Lean_mkApp6(v___x_1730_, v___x_1716_, v___x_1731_, v_fst_1722_, v___x_1732_, v_snd_1693_, v___x_1733_);
lean_inc_ref(v___y_1706_);
v___x_1735_ = l_Array_append___redArg(v___y_1706_, v_snd_1709_);
v___x_1736_ = l_Lean_mkAppN(v___x_1734_, v___x_1735_);
lean_dec_ref(v___x_1735_);
v___x_1737_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(v_goal_1694_, v___x_1736_, v___y_1697_);
lean_dec_ref(v___x_1737_);
v_sz_1738_ = lean_array_size(v_snd_1709_);
lean_inc(v_snd_1709_);
v___x_1739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__8(v_sz_1738_, v___y_1705_, v_snd_1709_);
v___x_1740_ = l_Lean_MVarId_tryClearMany_x27(v___x_1729_, v___x_1739_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v_fst_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; lean_object* v___x_1747_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref_known(v___x_1740_, 1);
v_fst_1742_ = lean_ctor_get(v_a_1741_, 0);
lean_inc(v_fst_1742_);
lean_dec(v_a_1741_);
v___x_1743_ = lean_array_get_size(v___y_1706_);
lean_dec_ref(v___y_1706_);
v___x_1744_ = lean_array_get_size(v_snd_1709_);
lean_dec(v_snd_1709_);
v___x_1745_ = lean_nat_add(v___x_1743_, v___x_1744_);
v___x_1746_ = 0;
v___x_1747_ = l_Lean_Meta_introNCore(v_fst_1742_, v___x_1745_, v___x_1715_, v___x_1746_, v___x_1746_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1756_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1750_ = v___x_1747_;
v_isShared_1751_ = v_isSharedCheck_1756_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1747_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1756_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v_snd_1752_; lean_object* v___x_1754_; 
v_snd_1752_ = lean_ctor_get(v_a_1748_, 1);
lean_inc(v_snd_1752_);
lean_dec(v_a_1748_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v_snd_1752_);
v___x_1754_ = v___x_1750_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_snd_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
v_a_1757_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1747_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1747_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec(v_snd_1709_);
lean_dec_ref(v___y_1706_);
v_a_1765_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1740_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1740_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec(v_fst_1722_);
lean_dec(v_snd_1709_);
lean_dec_ref(v___y_1706_);
lean_dec(v_goal_1694_);
lean_dec_ref(v_snd_1693_);
lean_dec(v_fst_1692_);
v_a_1773_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1727_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1727_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec(v_snd_1709_);
lean_dec_ref(v___y_1706_);
lean_dec(v_goal_1694_);
lean_dec_ref(v_snd_1693_);
lean_dec(v_fst_1692_);
v_a_1781_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1720_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1720_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec(v_snd_1709_);
lean_dec_ref(v___y_1706_);
lean_dec_ref(v___y_1704_);
lean_dec(v_goal_1694_);
lean_dec_ref(v_snd_1693_);
lean_dec(v_fst_1692_);
v_a_1789_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1712_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1712_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
v___jp_1797_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v_lctx_1804_; lean_object* v_mctx_1805_; lean_object* v_ngen_1806_; lean_object* v_quotContext_1807_; lean_object* v_nextMacroScope_1808_; uint8_t v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1801_ = lean_st_ref_get(v___y_1697_);
v___x_1802_ = lean_st_ref_get(v___y_1699_);
v___x_1803_ = lean_st_ref_get(v___y_1699_);
v_lctx_1804_ = lean_ctor_get(v___y_1696_, 2);
v_mctx_1805_ = lean_ctor_get(v___x_1801_, 0);
lean_inc_ref(v_mctx_1805_);
lean_dec(v___x_1801_);
v_ngen_1806_ = lean_ctor_get(v___x_1802_, 2);
lean_inc_ref(v_ngen_1806_);
lean_dec(v___x_1802_);
v_quotContext_1807_ = lean_ctor_get(v___y_1698_, 10);
v_nextMacroScope_1808_ = lean_ctor_get(v___x_1803_, 1);
lean_inc(v_nextMacroScope_1808_);
lean_dec(v___x_1803_);
v___x_1809_ = 1;
lean_inc_ref(v_lctx_1804_);
lean_inc(v_quotContext_1807_);
v___x_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1810_, 0, v_quotContext_1807_);
lean_ctor_set(v___x_1810_, 1, v_lctx_1804_);
v___x_1811_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12);
v___x_1812_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1812_, 0, v_mctx_1805_);
lean_ctor_set(v___x_1812_, 1, v_nextMacroScope_1808_);
lean_ctor_set(v___x_1812_, 2, v_ngen_1806_);
lean_ctor_set(v___x_1812_, 3, v___x_1811_);
lean_inc(v_goal_1694_);
v___x_1813_ = l_Lean_MetavarContext_revert(v___y_1799_, v_goal_1694_, v___x_1809_, v___x_1810_, v___x_1812_);
lean_dec_ref_known(v___x_1810_, 2);
lean_dec_ref(v___y_1799_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v_a_1815_; lean_object* v___x_1816_; lean_object* v_mctx_1817_; lean_object* v_nextMacroScope_1818_; lean_object* v_ngen_1819_; lean_object* v_cache_1820_; lean_object* v_zetaDeltaFVarIds_1821_; lean_object* v_postponed_1822_; lean_object* v_diag_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1849_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1814_);
v_a_1815_ = lean_ctor_get(v___x_1813_, 1);
lean_inc(v_a_1815_);
lean_dec_ref_known(v___x_1813_, 2);
v___x_1816_ = lean_st_ref_take(v___y_1697_);
v_mctx_1817_ = lean_ctor_get(v_a_1815_, 0);
lean_inc_ref(v_mctx_1817_);
v_nextMacroScope_1818_ = lean_ctor_get(v_a_1815_, 1);
lean_inc(v_nextMacroScope_1818_);
v_ngen_1819_ = lean_ctor_get(v_a_1815_, 2);
lean_inc_ref(v_ngen_1819_);
lean_dec(v_a_1815_);
v_cache_1820_ = lean_ctor_get(v___x_1816_, 1);
v_zetaDeltaFVarIds_1821_ = lean_ctor_get(v___x_1816_, 2);
v_postponed_1822_ = lean_ctor_get(v___x_1816_, 3);
v_diag_1823_ = lean_ctor_get(v___x_1816_, 4);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1849_ == 0)
{
lean_object* v_unused_1850_; 
v_unused_1850_ = lean_ctor_get(v___x_1816_, 0);
lean_dec(v_unused_1850_);
v___x_1825_ = v___x_1816_;
v_isShared_1826_ = v_isSharedCheck_1849_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_diag_1823_);
lean_inc(v_postponed_1822_);
lean_inc(v_zetaDeltaFVarIds_1821_);
lean_inc(v_cache_1820_);
lean_dec(v___x_1816_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1849_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v_mctx_1817_);
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_mctx_1817_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_cache_1820_);
lean_ctor_set(v_reuseFailAlloc_1848_, 2, v_zetaDeltaFVarIds_1821_);
lean_ctor_set(v_reuseFailAlloc_1848_, 3, v_postponed_1822_);
lean_ctor_set(v_reuseFailAlloc_1848_, 4, v_diag_1823_);
v___x_1828_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v_env_1831_; lean_object* v_auxDeclNGen_1832_; lean_object* v_traceState_1833_; lean_object* v_cache_1834_; lean_object* v_messages_1835_; lean_object* v_infoState_1836_; lean_object* v_snapshotTasks_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1845_; 
v___x_1829_ = lean_st_ref_set(v___y_1697_, v___x_1828_);
v___x_1830_ = lean_st_ref_take(v___y_1699_);
v_env_1831_ = lean_ctor_get(v___x_1830_, 0);
v_auxDeclNGen_1832_ = lean_ctor_get(v___x_1830_, 3);
v_traceState_1833_ = lean_ctor_get(v___x_1830_, 4);
v_cache_1834_ = lean_ctor_get(v___x_1830_, 5);
v_messages_1835_ = lean_ctor_get(v___x_1830_, 6);
v_infoState_1836_ = lean_ctor_get(v___x_1830_, 7);
v_snapshotTasks_1837_ = lean_ctor_get(v___x_1830_, 8);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1845_ == 0)
{
lean_object* v_unused_1846_; lean_object* v_unused_1847_; 
v_unused_1846_ = lean_ctor_get(v___x_1830_, 2);
lean_dec(v_unused_1846_);
v_unused_1847_ = lean_ctor_get(v___x_1830_, 1);
lean_dec(v_unused_1847_);
v___x_1839_ = v___x_1830_;
v_isShared_1840_ = v_isSharedCheck_1845_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_snapshotTasks_1837_);
lean_inc(v_infoState_1836_);
lean_inc(v_messages_1835_);
lean_inc(v_cache_1834_);
lean_inc(v_traceState_1833_);
lean_inc(v_auxDeclNGen_1832_);
lean_inc(v_env_1831_);
lean_dec(v___x_1830_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1845_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 2, v_ngen_1819_);
lean_ctor_set(v___x_1839_, 1, v_nextMacroScope_1818_);
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_env_1831_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_nextMacroScope_1818_);
lean_ctor_set(v_reuseFailAlloc_1844_, 2, v_ngen_1819_);
lean_ctor_set(v_reuseFailAlloc_1844_, 3, v_auxDeclNGen_1832_);
lean_ctor_set(v_reuseFailAlloc_1844_, 4, v_traceState_1833_);
lean_ctor_set(v_reuseFailAlloc_1844_, 5, v_cache_1834_);
lean_ctor_set(v_reuseFailAlloc_1844_, 6, v_messages_1835_);
lean_ctor_set(v_reuseFailAlloc_1844_, 7, v_infoState_1836_);
lean_ctor_set(v_reuseFailAlloc_1844_, 8, v_snapshotTasks_1837_);
v___x_1842_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_st_ref_set(v___y_1699_, v___x_1842_);
lean_inc_ref(v___y_1800_);
v___y_1702_ = v___y_1798_;
v___y_1703_ = v___x_1809_;
v___y_1704_ = v___y_1800_;
v___y_1705_ = v___y_1798_;
v___y_1706_ = v___y_1800_;
v_a_1707_ = v_a_1814_;
goto v___jp_1701_;
}
}
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1852_; lean_object* v_mctx_1853_; lean_object* v_nextMacroScope_1854_; lean_object* v_ngen_1855_; lean_object* v_cache_1856_; lean_object* v_zetaDeltaFVarIds_1857_; lean_object* v_postponed_1858_; lean_object* v_diag_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1895_; 
lean_dec_ref(v___y_1800_);
lean_dec(v_goal_1694_);
lean_dec_ref(v_snd_1693_);
lean_dec(v_fst_1692_);
v_a_1851_ = lean_ctor_get(v___x_1813_, 1);
lean_inc(v_a_1851_);
lean_dec_ref_known(v___x_1813_, 2);
v___x_1852_ = lean_st_ref_take(v___y_1697_);
v_mctx_1853_ = lean_ctor_get(v_a_1851_, 0);
lean_inc_ref(v_mctx_1853_);
v_nextMacroScope_1854_ = lean_ctor_get(v_a_1851_, 1);
lean_inc(v_nextMacroScope_1854_);
v_ngen_1855_ = lean_ctor_get(v_a_1851_, 2);
lean_inc_ref(v_ngen_1855_);
lean_dec(v_a_1851_);
v_cache_1856_ = lean_ctor_get(v___x_1852_, 1);
v_zetaDeltaFVarIds_1857_ = lean_ctor_get(v___x_1852_, 2);
v_postponed_1858_ = lean_ctor_get(v___x_1852_, 3);
v_diag_1859_ = lean_ctor_get(v___x_1852_, 4);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1895_ == 0)
{
lean_object* v_unused_1896_; 
v_unused_1896_ = lean_ctor_get(v___x_1852_, 0);
lean_dec(v_unused_1896_);
v___x_1861_ = v___x_1852_;
v_isShared_1862_ = v_isSharedCheck_1895_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_diag_1859_);
lean_inc(v_postponed_1858_);
lean_inc(v_zetaDeltaFVarIds_1857_);
lean_inc(v_cache_1856_);
lean_dec(v___x_1852_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1895_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v_mctx_1853_);
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_mctx_1853_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_cache_1856_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v_zetaDeltaFVarIds_1857_);
lean_ctor_set(v_reuseFailAlloc_1894_, 3, v_postponed_1858_);
lean_ctor_set(v_reuseFailAlloc_1894_, 4, v_diag_1859_);
v___x_1864_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v_env_1867_; lean_object* v_auxDeclNGen_1868_; lean_object* v_traceState_1869_; lean_object* v_cache_1870_; lean_object* v_messages_1871_; lean_object* v_infoState_1872_; lean_object* v_snapshotTasks_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1891_; 
v___x_1865_ = lean_st_ref_set(v___y_1697_, v___x_1864_);
v___x_1866_ = lean_st_ref_take(v___y_1699_);
v_env_1867_ = lean_ctor_get(v___x_1866_, 0);
v_auxDeclNGen_1868_ = lean_ctor_get(v___x_1866_, 3);
v_traceState_1869_ = lean_ctor_get(v___x_1866_, 4);
v_cache_1870_ = lean_ctor_get(v___x_1866_, 5);
v_messages_1871_ = lean_ctor_get(v___x_1866_, 6);
v_infoState_1872_ = lean_ctor_get(v___x_1866_, 7);
v_snapshotTasks_1873_ = lean_ctor_get(v___x_1866_, 8);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1891_ == 0)
{
lean_object* v_unused_1892_; lean_object* v_unused_1893_; 
v_unused_1892_ = lean_ctor_get(v___x_1866_, 2);
lean_dec(v_unused_1892_);
v_unused_1893_ = lean_ctor_get(v___x_1866_, 1);
lean_dec(v_unused_1893_);
v___x_1875_ = v___x_1866_;
v_isShared_1876_ = v_isSharedCheck_1891_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_snapshotTasks_1873_);
lean_inc(v_infoState_1872_);
lean_inc(v_messages_1871_);
lean_inc(v_cache_1870_);
lean_inc(v_traceState_1869_);
lean_inc(v_auxDeclNGen_1868_);
lean_inc(v_env_1867_);
lean_dec(v___x_1866_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1891_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 2, v_ngen_1855_);
lean_ctor_set(v___x_1875_, 1, v_nextMacroScope_1854_);
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_env_1867_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_nextMacroScope_1854_);
lean_ctor_set(v_reuseFailAlloc_1890_, 2, v_ngen_1855_);
lean_ctor_set(v_reuseFailAlloc_1890_, 3, v_auxDeclNGen_1868_);
lean_ctor_set(v_reuseFailAlloc_1890_, 4, v_traceState_1869_);
lean_ctor_set(v_reuseFailAlloc_1890_, 5, v_cache_1870_);
lean_ctor_set(v_reuseFailAlloc_1890_, 6, v_messages_1871_);
lean_ctor_set(v_reuseFailAlloc_1890_, 7, v_infoState_1872_);
lean_ctor_set(v_reuseFailAlloc_1890_, 8, v_snapshotTasks_1873_);
v___x_1878_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
v___x_1879_ = lean_st_ref_set(v___y_1699_, v___x_1878_);
v___x_1880_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14);
v___x_1881_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(v___x_1880_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1881_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1881_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
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
}
}
v___jp_1898_:
{
lean_object* v___x_1900_; lean_object* v_relevantTerms_1901_; lean_object* v_size_1902_; lean_object* v_buckets_1903_; size_t v_sz_1904_; size_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; 
v___x_1900_ = lean_st_ref_get(v___y_1695_);
v_relevantTerms_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc_ref(v_relevantTerms_1901_);
lean_dec(v___x_1900_);
v_size_1902_ = lean_ctor_get(v_relevantTerms_1901_, 0);
lean_inc(v_size_1902_);
v_buckets_1903_ = lean_ctor_get(v_relevantTerms_1901_, 1);
lean_inc_ref(v_buckets_1903_);
lean_dec_ref(v_relevantTerms_1901_);
v_sz_1904_ = lean_array_size(v___y_1899_);
v___x_1905_ = ((size_t)0ULL);
v___x_1906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__1(v_sz_1904_, v___x_1905_, v___y_1899_);
v___x_1907_ = lean_mk_empty_array_with_capacity(v_size_1902_);
lean_dec(v_size_1902_);
v___x_1908_ = lean_unsigned_to_nat(0u);
v___x_1909_ = lean_array_get_size(v_buckets_1903_);
v___x_1910_ = lean_nat_dec_lt(v___x_1908_, v___x_1909_);
if (v___x_1910_ == 0)
{
lean_dec_ref(v_buckets_1903_);
v___y_1798_ = v___x_1905_;
v___y_1799_ = v___x_1906_;
v___y_1800_ = v___x_1907_;
goto v___jp_1797_;
}
else
{
uint8_t v___x_1911_; 
v___x_1911_ = lean_nat_dec_le(v___x_1909_, v___x_1909_);
if (v___x_1911_ == 0)
{
if (v___x_1910_ == 0)
{
lean_dec_ref(v_buckets_1903_);
v___y_1798_ = v___x_1905_;
v___y_1799_ = v___x_1906_;
v___y_1800_ = v___x_1907_;
goto v___jp_1797_;
}
else
{
size_t v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_usize_of_nat(v___x_1909_);
v___x_1913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__11(v_buckets_1903_, v___x_1905_, v___x_1912_, v___x_1907_);
lean_dec_ref(v_buckets_1903_);
v___y_1798_ = v___x_1905_;
v___y_1799_ = v___x_1906_;
v___y_1800_ = v___x_1913_;
goto v___jp_1797_;
}
}
else
{
size_t v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_usize_of_nat(v___x_1909_);
v___x_1915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__11(v_buckets_1903_, v___x_1905_, v___x_1914_, v___x_1907_);
lean_dec_ref(v_buckets_1903_);
v___y_1798_ = v___x_1905_;
v___y_1799_ = v___x_1906_;
v___y_1800_ = v___x_1915_;
goto v___jp_1797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___boxed(lean_object* v_fst_1930_, lean_object* v_snd_1931_, lean_object* v_goal_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4(v_fst_1930_, v_snd_1931_, v_goal_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
return v_res_1939_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0(uint8_t v___y_1948_, uint8_t v_suppressElabErrors_1949_, lean_object* v_x_1950_){
_start:
{
if (lean_obj_tag(v_x_1950_) == 1)
{
lean_object* v_pre_1951_; 
v_pre_1951_ = lean_ctor_get(v_x_1950_, 0);
switch(lean_obj_tag(v_pre_1951_))
{
case 1:
{
lean_object* v_pre_1952_; 
v_pre_1952_ = lean_ctor_get(v_pre_1951_, 0);
switch(lean_obj_tag(v_pre_1952_))
{
case 0:
{
lean_object* v_str_1953_; lean_object* v_str_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v_str_1953_ = lean_ctor_get(v_x_1950_, 1);
v_str_1954_ = lean_ctor_get(v_pre_1951_, 1);
v___x_1955_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0));
v___x_1956_ = lean_string_dec_eq(v_str_1954_, v___x_1955_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; uint8_t v___x_1958_; 
v___x_1957_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1));
v___x_1958_ = lean_string_dec_eq(v_str_1954_, v___x_1957_);
if (v___x_1958_ == 0)
{
return v___y_1948_;
}
else
{
lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1959_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__2));
v___x_1960_ = lean_string_dec_eq(v_str_1953_, v___x_1959_);
if (v___x_1960_ == 0)
{
return v___y_1948_;
}
else
{
return v_suppressElabErrors_1949_;
}
}
}
else
{
lean_object* v___x_1961_; uint8_t v___x_1962_; 
v___x_1961_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__3));
v___x_1962_ = lean_string_dec_eq(v_str_1953_, v___x_1961_);
if (v___x_1962_ == 0)
{
return v___y_1948_;
}
else
{
return v_suppressElabErrors_1949_;
}
}
}
case 1:
{
lean_object* v_pre_1963_; 
v_pre_1963_ = lean_ctor_get(v_pre_1952_, 0);
if (lean_obj_tag(v_pre_1963_) == 0)
{
lean_object* v_str_1964_; lean_object* v_str_1965_; lean_object* v_str_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v_str_1964_ = lean_ctor_get(v_x_1950_, 1);
v_str_1965_ = lean_ctor_get(v_pre_1951_, 1);
v_str_1966_ = lean_ctor_get(v_pre_1952_, 1);
v___x_1967_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4));
v___x_1968_ = lean_string_dec_eq(v_str_1966_, v___x_1967_);
if (v___x_1968_ == 0)
{
return v___y_1948_;
}
else
{
lean_object* v___x_1969_; uint8_t v___x_1970_; 
v___x_1969_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5));
v___x_1970_ = lean_string_dec_eq(v_str_1965_, v___x_1969_);
if (v___x_1970_ == 0)
{
return v___y_1948_;
}
else
{
lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1971_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__6));
v___x_1972_ = lean_string_dec_eq(v_str_1964_, v___x_1971_);
if (v___x_1972_ == 0)
{
return v___y_1948_;
}
else
{
return v_suppressElabErrors_1949_;
}
}
}
}
else
{
return v___y_1948_;
}
}
default: 
{
return v___y_1948_;
}
}
}
case 0:
{
lean_object* v_str_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; 
v_str_1973_ = lean_ctor_get(v_x_1950_, 1);
v___x_1974_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__7));
v___x_1975_ = lean_string_dec_eq(v_str_1973_, v___x_1974_);
if (v___x_1975_ == 0)
{
return v___y_1948_;
}
else
{
return v_suppressElabErrors_1949_;
}
}
default: 
{
return v___y_1948_;
}
}
}
else
{
return v___y_1948_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___boxed(lean_object* v___y_1976_, lean_object* v_suppressElabErrors_1977_, lean_object* v_x_1978_){
_start:
{
uint8_t v___y_22989__boxed_1979_; uint8_t v_suppressElabErrors_boxed_1980_; uint8_t v_res_1981_; lean_object* v_r_1982_; 
v___y_22989__boxed_1979_ = lean_unbox(v___y_1976_);
v_suppressElabErrors_boxed_1980_ = lean_unbox(v_suppressElabErrors_1977_);
v_res_1981_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0(v___y_22989__boxed_1979_, v_suppressElabErrors_boxed_1980_, v_x_1978_);
lean_dec(v_x_1978_);
v_r_1982_ = lean_box(v_res_1981_);
return v_r_1982_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34(lean_object* v_opts_1983_, lean_object* v_opt_1984_){
_start:
{
lean_object* v_name_1985_; lean_object* v_defValue_1986_; lean_object* v_map_1987_; lean_object* v___x_1988_; 
v_name_1985_ = lean_ctor_get(v_opt_1984_, 0);
v_defValue_1986_ = lean_ctor_get(v_opt_1984_, 1);
v_map_1987_ = lean_ctor_get(v_opts_1983_, 0);
v___x_1988_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1987_, v_name_1985_);
if (lean_obj_tag(v___x_1988_) == 0)
{
uint8_t v___x_1989_; 
v___x_1989_ = lean_unbox(v_defValue_1986_);
return v___x_1989_;
}
else
{
lean_object* v_val_1990_; 
v_val_1990_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_val_1990_);
lean_dec_ref_known(v___x_1988_, 1);
if (lean_obj_tag(v_val_1990_) == 1)
{
uint8_t v_v_1991_; 
v_v_1991_ = lean_ctor_get_uint8(v_val_1990_, 0);
lean_dec_ref_known(v_val_1990_, 0);
return v_v_1991_;
}
else
{
uint8_t v___x_1992_; 
lean_dec(v_val_1990_);
v___x_1992_ = lean_unbox(v_defValue_1986_);
return v___x_1992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34___boxed(lean_object* v_opts_1993_, lean_object* v_opt_1994_){
_start:
{
uint8_t v_res_1995_; lean_object* v_r_1996_; 
v_res_1995_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34(v_opts_1993_, v_opt_1994_);
lean_dec_ref(v_opt_1994_);
lean_dec_ref(v_opts_1993_);
v_r_1996_ = lean_box(v_res_1995_);
return v_r_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(lean_object* v_ref_1998_, lean_object* v_msgData_1999_, uint8_t v_severity_2000_, uint8_t v_isSilent_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
uint8_t v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; uint8_t v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2044_; uint8_t v___y_2045_; uint8_t v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; uint8_t v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2069_; uint8_t v___y_2070_; uint8_t v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; uint8_t v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2080_; uint8_t v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; uint8_t v___y_2085_; uint8_t v___y_2086_; uint8_t v___x_2091_; uint8_t v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; uint8_t v___y_2098_; uint8_t v___y_2099_; uint8_t v___y_2101_; uint8_t v___x_2116_; 
v___x_2091_ = 2;
v___x_2116_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2000_, v___x_2091_);
if (v___x_2116_ == 0)
{
v___y_2101_ = v___x_2116_;
goto v___jp_2100_;
}
else
{
uint8_t v___x_2117_; 
lean_inc_ref(v_msgData_1999_);
v___x_2117_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1999_);
v___y_2101_ = v___x_2117_;
goto v___jp_2100_;
}
v___jp_2007_:
{
lean_object* v___x_2017_; lean_object* v_currNamespace_2018_; lean_object* v_openDecls_2019_; lean_object* v_env_2020_; lean_object* v_nextMacroScope_2021_; lean_object* v_ngen_2022_; lean_object* v_auxDeclNGen_2023_; lean_object* v_traceState_2024_; lean_object* v_cache_2025_; lean_object* v_messages_2026_; lean_object* v_infoState_2027_; lean_object* v_snapshotTasks_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2042_; 
v___x_2017_ = lean_st_ref_take(v___y_2016_);
v_currNamespace_2018_ = lean_ctor_get(v___y_2015_, 6);
v_openDecls_2019_ = lean_ctor_get(v___y_2015_, 7);
v_env_2020_ = lean_ctor_get(v___x_2017_, 0);
v_nextMacroScope_2021_ = lean_ctor_get(v___x_2017_, 1);
v_ngen_2022_ = lean_ctor_get(v___x_2017_, 2);
v_auxDeclNGen_2023_ = lean_ctor_get(v___x_2017_, 3);
v_traceState_2024_ = lean_ctor_get(v___x_2017_, 4);
v_cache_2025_ = lean_ctor_get(v___x_2017_, 5);
v_messages_2026_ = lean_ctor_get(v___x_2017_, 6);
v_infoState_2027_ = lean_ctor_get(v___x_2017_, 7);
v_snapshotTasks_2028_ = lean_ctor_get(v___x_2017_, 8);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2030_ = v___x_2017_;
v_isShared_2031_ = v_isSharedCheck_2042_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_snapshotTasks_2028_);
lean_inc(v_infoState_2027_);
lean_inc(v_messages_2026_);
lean_inc(v_cache_2025_);
lean_inc(v_traceState_2024_);
lean_inc(v_auxDeclNGen_2023_);
lean_inc(v_ngen_2022_);
lean_inc(v_nextMacroScope_2021_);
lean_inc(v_env_2020_);
lean_dec(v___x_2017_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2042_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
lean_inc(v_openDecls_2019_);
lean_inc(v_currNamespace_2018_);
v___x_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2032_, 0, v_currNamespace_2018_);
lean_ctor_set(v___x_2032_, 1, v_openDecls_2019_);
v___x_2033_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
lean_ctor_set(v___x_2033_, 1, v___y_2010_);
lean_inc_ref(v___y_2011_);
lean_inc_ref(v___y_2014_);
v___x_2034_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2034_, 0, v___y_2014_);
lean_ctor_set(v___x_2034_, 1, v___y_2009_);
lean_ctor_set(v___x_2034_, 2, v___y_2013_);
lean_ctor_set(v___x_2034_, 3, v___y_2011_);
lean_ctor_set(v___x_2034_, 4, v___x_2033_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*5, v___y_2012_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*5 + 1, v___y_2008_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*5 + 2, v_isSilent_2001_);
v___x_2035_ = l_Lean_MessageLog_add(v___x_2034_, v_messages_2026_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 6, v___x_2035_);
v___x_2037_ = v___x_2030_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_env_2020_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_nextMacroScope_2021_);
lean_ctor_set(v_reuseFailAlloc_2041_, 2, v_ngen_2022_);
lean_ctor_set(v_reuseFailAlloc_2041_, 3, v_auxDeclNGen_2023_);
lean_ctor_set(v_reuseFailAlloc_2041_, 4, v_traceState_2024_);
lean_ctor_set(v_reuseFailAlloc_2041_, 5, v_cache_2025_);
lean_ctor_set(v_reuseFailAlloc_2041_, 6, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2041_, 7, v_infoState_2027_);
lean_ctor_set(v_reuseFailAlloc_2041_, 8, v_snapshotTasks_2028_);
v___x_2037_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2038_ = lean_st_ref_set(v___y_2016_, v___x_2037_);
v___x_2039_ = lean_box(0);
v___x_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
return v___x_2040_;
}
}
}
v___jp_2043_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2067_; 
v___x_2052_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1999_);
v___x_2053_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(v___x_2052_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2056_ = v___x_2053_;
v_isShared_2057_ = v_isSharedCheck_2067_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2053_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2067_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
lean_inc_ref_n(v___y_2048_, 2);
v___x_2058_ = l_Lean_FileMap_toPosition(v___y_2048_, v___y_2047_);
lean_dec(v___y_2047_);
v___x_2059_ = l_Lean_FileMap_toPosition(v___y_2048_, v___y_2051_);
lean_dec(v___y_2051_);
v___x_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
v___x_2061_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0));
if (v___y_2045_ == 0)
{
lean_del_object(v___x_2056_);
lean_dec_ref(v___y_2044_);
v___y_2008_ = v___y_2046_;
v___y_2009_ = v___x_2058_;
v___y_2010_ = v_a_2054_;
v___y_2011_ = v___x_2061_;
v___y_2012_ = v___y_2050_;
v___y_2013_ = v___x_2060_;
v___y_2014_ = v___y_2049_;
v___y_2015_ = v___y_2004_;
v___y_2016_ = v___y_2005_;
goto v___jp_2007_;
}
else
{
uint8_t v___x_2062_; 
lean_inc(v_a_2054_);
v___x_2062_ = l_Lean_MessageData_hasTag(v___y_2044_, v_a_2054_);
if (v___x_2062_ == 0)
{
lean_object* v___x_2063_; lean_object* v___x_2065_; 
lean_dec_ref_known(v___x_2060_, 1);
lean_dec_ref(v___x_2058_);
lean_dec(v_a_2054_);
v___x_2063_ = lean_box(0);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 0, v___x_2063_);
v___x_2065_ = v___x_2056_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
else
{
lean_del_object(v___x_2056_);
v___y_2008_ = v___y_2046_;
v___y_2009_ = v___x_2058_;
v___y_2010_ = v_a_2054_;
v___y_2011_ = v___x_2061_;
v___y_2012_ = v___y_2050_;
v___y_2013_ = v___x_2060_;
v___y_2014_ = v___y_2049_;
v___y_2015_ = v___y_2004_;
v___y_2016_ = v___y_2005_;
goto v___jp_2007_;
}
}
}
}
v___jp_2068_:
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_Syntax_getTailPos_x3f(v___y_2072_, v___y_2074_);
lean_dec(v___y_2072_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_inc(v___y_2076_);
v___y_2044_ = v___y_2069_;
v___y_2045_ = v___y_2071_;
v___y_2046_ = v___y_2070_;
v___y_2047_ = v___y_2076_;
v___y_2048_ = v___y_2073_;
v___y_2049_ = v___y_2075_;
v___y_2050_ = v___y_2074_;
v___y_2051_ = v___y_2076_;
goto v___jp_2043_;
}
else
{
lean_object* v_val_2078_; 
v_val_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_val_2078_);
lean_dec_ref_known(v___x_2077_, 1);
v___y_2044_ = v___y_2069_;
v___y_2045_ = v___y_2071_;
v___y_2046_ = v___y_2070_;
v___y_2047_ = v___y_2076_;
v___y_2048_ = v___y_2073_;
v___y_2049_ = v___y_2075_;
v___y_2050_ = v___y_2074_;
v___y_2051_ = v_val_2078_;
goto v___jp_2043_;
}
}
v___jp_2079_:
{
lean_object* v_ref_2087_; lean_object* v___x_2088_; 
v_ref_2087_ = l_Lean_replaceRef(v_ref_1998_, v___y_2082_);
v___x_2088_ = l_Lean_Syntax_getPos_x3f(v_ref_2087_, v___y_2085_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v___x_2089_; 
v___x_2089_ = lean_unsigned_to_nat(0u);
v___y_2069_ = v___y_2080_;
v___y_2070_ = v___y_2086_;
v___y_2071_ = v___y_2081_;
v___y_2072_ = v_ref_2087_;
v___y_2073_ = v___y_2083_;
v___y_2074_ = v___y_2085_;
v___y_2075_ = v___y_2084_;
v___y_2076_ = v___x_2089_;
goto v___jp_2068_;
}
else
{
lean_object* v_val_2090_; 
v_val_2090_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_val_2090_);
lean_dec_ref_known(v___x_2088_, 1);
v___y_2069_ = v___y_2080_;
v___y_2070_ = v___y_2086_;
v___y_2071_ = v___y_2081_;
v___y_2072_ = v_ref_2087_;
v___y_2073_ = v___y_2083_;
v___y_2074_ = v___y_2085_;
v___y_2075_ = v___y_2084_;
v___y_2076_ = v_val_2090_;
goto v___jp_2068_;
}
}
v___jp_2092_:
{
if (v___y_2099_ == 0)
{
v___y_2080_ = v___y_2094_;
v___y_2081_ = v___y_2093_;
v___y_2082_ = v___y_2095_;
v___y_2083_ = v___y_2096_;
v___y_2084_ = v___y_2097_;
v___y_2085_ = v___y_2098_;
v___y_2086_ = v_severity_2000_;
goto v___jp_2079_;
}
else
{
v___y_2080_ = v___y_2094_;
v___y_2081_ = v___y_2093_;
v___y_2082_ = v___y_2095_;
v___y_2083_ = v___y_2096_;
v___y_2084_ = v___y_2097_;
v___y_2085_ = v___y_2098_;
v___y_2086_ = v___x_2091_;
goto v___jp_2079_;
}
}
v___jp_2100_:
{
if (v___y_2101_ == 0)
{
lean_object* v_fileName_2102_; lean_object* v_fileMap_2103_; lean_object* v_options_2104_; lean_object* v_ref_2105_; uint8_t v_suppressElabErrors_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___f_2109_; uint8_t v___x_2110_; uint8_t v___x_2111_; 
v_fileName_2102_ = lean_ctor_get(v___y_2004_, 0);
v_fileMap_2103_ = lean_ctor_get(v___y_2004_, 1);
v_options_2104_ = lean_ctor_get(v___y_2004_, 2);
v_ref_2105_ = lean_ctor_get(v___y_2004_, 5);
v_suppressElabErrors_2106_ = lean_ctor_get_uint8(v___y_2004_, sizeof(void*)*14 + 1);
v___x_2107_ = lean_box(v___y_2101_);
v___x_2108_ = lean_box(v_suppressElabErrors_2106_);
v___f_2109_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2109_, 0, v___x_2107_);
lean_closure_set(v___f_2109_, 1, v___x_2108_);
v___x_2110_ = 1;
v___x_2111_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2000_, v___x_2110_);
if (v___x_2111_ == 0)
{
v___y_2093_ = v_suppressElabErrors_2106_;
v___y_2094_ = v___f_2109_;
v___y_2095_ = v_ref_2105_;
v___y_2096_ = v_fileMap_2103_;
v___y_2097_ = v_fileName_2102_;
v___y_2098_ = v___y_2101_;
v___y_2099_ = v___x_2111_;
goto v___jp_2092_;
}
else
{
lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2112_ = l_Lean_warningAsError;
v___x_2113_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34(v_options_2104_, v___x_2112_);
v___y_2093_ = v_suppressElabErrors_2106_;
v___y_2094_ = v___f_2109_;
v___y_2095_ = v_ref_2105_;
v___y_2096_ = v_fileMap_2103_;
v___y_2097_ = v_fileName_2102_;
v___y_2098_ = v___y_2101_;
v___y_2099_ = v___x_2113_;
goto v___jp_2092_;
}
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
lean_dec_ref(v_msgData_1999_);
v___x_2114_ = lean_box(0);
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
return v___x_2115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___boxed(lean_object* v_ref_2118_, lean_object* v_msgData_2119_, lean_object* v_severity_2120_, lean_object* v_isSilent_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
uint8_t v_severity_boxed_2127_; uint8_t v_isSilent_boxed_2128_; lean_object* v_res_2129_; 
v_severity_boxed_2127_ = lean_unbox(v_severity_2120_);
v_isSilent_boxed_2128_ = lean_unbox(v_isSilent_2121_);
v_res_2129_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(v_ref_2118_, v_msgData_2119_, v_severity_boxed_2127_, v_isSilent_boxed_2128_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v_ref_2118_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(lean_object* v_msgData_2130_, uint8_t v_severity_2131_, uint8_t v_isSilent_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_ref_2139_; lean_object* v___x_2140_; 
v_ref_2139_ = lean_ctor_get(v___y_2136_, 5);
v___x_2140_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(v_ref_2139_, v_msgData_2130_, v_severity_2131_, v_isSilent_2132_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24___boxed(lean_object* v_msgData_2141_, lean_object* v_severity_2142_, lean_object* v_isSilent_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
uint8_t v_severity_boxed_2150_; uint8_t v_isSilent_boxed_2151_; lean_object* v_res_2152_; 
v_severity_boxed_2150_ = lean_unbox(v_severity_2142_);
v_isSilent_boxed_2151_ = lean_unbox(v_isSilent_2143_);
v_res_2152_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(v_msgData_2141_, v_severity_boxed_2150_, v_isSilent_boxed_2151_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15(lean_object* v_msgData_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
uint8_t v___x_2160_; uint8_t v___x_2161_; lean_object* v___x_2162_; 
v___x_2160_ = 1;
v___x_2161_ = 0;
v___x_2162_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(v_msgData_2153_, v___x_2160_, v___x_2161_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15___boxed(lean_object* v_msgData_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15(v_msgData_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
return v_res_2170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__1(void){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__0));
v___x_2173_ = l_Lean_stringToMessageData(v___x_2172_);
return v___x_2173_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__4(void){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2179_ = lean_box(0);
v___x_2180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3));
v___x_2181_ = l_Lean_mkConst(v___x_2180_, v___x_2179_);
return v___x_2181_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__5(void){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__4);
v___x_2183_ = l_Lean_MessageData_ofExpr(v___x_2182_);
return v___x_2183_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__6(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2184_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__5);
v___x_2185_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__1);
v___x_2186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
lean_ctor_set(v___x_2186_, 1, v___x_2184_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize(lean_object* v_goal_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v___x_2194_; 
lean_inc(v_goal_2187_);
v___x_2194_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq(v_goal_2187_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
if (lean_obj_tag(v_a_2195_) == 1)
{
lean_object* v_val_2196_; lean_object* v_fst_2197_; lean_object* v_snd_2198_; lean_object* v___f_2199_; lean_object* v___x_2200_; 
v_val_2196_ = lean_ctor_get(v_a_2195_, 0);
lean_inc(v_val_2196_);
lean_dec_ref_known(v_a_2195_, 1);
v_fst_2197_ = lean_ctor_get(v_val_2196_, 0);
lean_inc(v_fst_2197_);
v_snd_2198_ = lean_ctor_get(v_val_2196_, 1);
lean_inc(v_snd_2198_);
lean_dec(v_val_2196_);
lean_inc(v_goal_2187_);
v___f_2199_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___boxed), 9, 3);
lean_closure_set(v___f_2199_, 0, v_fst_2197_);
lean_closure_set(v___f_2199_, 1, v_snd_2198_);
lean_closure_set(v___f_2199_, 2, v_goal_2187_);
v___x_2200_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_goal_2187_, v___f_2199_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_);
return v___x_2200_;
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec(v_a_2195_);
v___x_2201_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__6);
v___x_2202_ = l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15(v___x_2201_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2209_ == 0)
{
lean_object* v_unused_2210_; 
v_unused_2210_ = lean_ctor_get(v___x_2202_, 0);
lean_dec(v_unused_2210_);
v___x_2204_ = v___x_2202_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_dec(v___x_2202_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v_goal_2187_);
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_goal_2187_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec(v_goal_2187_);
v_a_2211_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2202_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2202_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
lean_dec(v_goal_2187_);
v_a_2219_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2194_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2194_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___boxed(lean_object* v_goal_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize(v_goal_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
lean_dec(v_a_2228_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0(lean_object* v_00_u03b2_2235_, lean_object* v_m_2236_, lean_object* v_a_2237_, lean_object* v_b_2238_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(v_m_2236_, v_a_2237_, v_b_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2(lean_object* v_as_2240_, size_t v_sz_2241_, size_t v_i_2242_, lean_object* v_b_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(v_as_2240_, v_sz_2241_, v_i_2242_, v_b_2243_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2___boxed(lean_object* v_as_2251_, lean_object* v_sz_2252_, lean_object* v_i_2253_, lean_object* v_b_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
size_t v_sz_boxed_2261_; size_t v_i_boxed_2262_; lean_object* v_res_2263_; 
v_sz_boxed_2261_ = lean_unbox_usize(v_sz_2252_);
lean_dec(v_sz_2252_);
v_i_boxed_2262_ = lean_unbox_usize(v_i_2253_);
lean_dec(v_i_2253_);
v_res_2263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2(v_as_2251_, v_sz_boxed_2261_, v_i_boxed_2262_, v_b_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v_as_2251_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3(lean_object* v_00_u03b2_2264_, lean_object* v_m_2265_, lean_object* v_a_2266_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(v_m_2265_, v_a_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3___boxed(lean_object* v_00_u03b2_2268_, lean_object* v_m_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3(v_00_u03b2_2268_, v_m_2269_, v_a_2270_);
lean_dec_ref(v_a_2270_);
lean_dec_ref(v_m_2269_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12(lean_object* v_00_u03b1_2272_, lean_object* v_name_2273_, uint8_t v_bi_2274_, lean_object* v_type_2275_, lean_object* v_k_2276_, uint8_t v_kind_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(v_name_2273_, v_bi_2274_, v_type_2275_, v_k_2276_, v_kind_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___boxed(lean_object* v_00_u03b1_2285_, lean_object* v_name_2286_, lean_object* v_bi_2287_, lean_object* v_type_2288_, lean_object* v_k_2289_, lean_object* v_kind_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
uint8_t v_bi_boxed_2297_; uint8_t v_kind_boxed_2298_; lean_object* v_res_2299_; 
v_bi_boxed_2297_ = lean_unbox(v_bi_2287_);
v_kind_boxed_2298_ = lean_unbox(v_kind_2290_);
v_res_2299_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12(v_00_u03b1_2285_, v_name_2286_, v_bi_boxed_2297_, v_type_2288_, v_k_2289_, v_kind_boxed_2298_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6(lean_object* v_00_u03b1_2300_, lean_object* v_name_2301_, lean_object* v_type_2302_, lean_object* v_k_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v_name_2301_, v_type_2302_, v_k_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___boxed(lean_object* v_00_u03b1_2311_, lean_object* v_name_2312_, lean_object* v_type_2313_, lean_object* v_k_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6(v_00_u03b1_2311_, v_name_2312_, v_type_2313_, v_k_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7(lean_object* v_mvarId_2322_, lean_object* v_val_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(v_mvarId_2322_, v_val_2323_, v___y_2326_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___boxed(lean_object* v_mvarId_2331_, lean_object* v_val_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7(v_mvarId_2331_, v_val_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9(lean_object* v_00_u03b1_2340_, lean_object* v_msg_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(v_msg_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9___boxed(lean_object* v_00_u03b1_2348_, lean_object* v_msg_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9(v_00_u03b1_2348_, v_msg_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
return v_res_2355_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0(lean_object* v_00_u03b2_2356_, lean_object* v_a_2357_, lean_object* v_x_2358_){
_start:
{
uint8_t v___x_2359_; 
v___x_2359_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_2357_, v_x_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2360_, lean_object* v_a_2361_, lean_object* v_x_2362_){
_start:
{
uint8_t v_res_2363_; lean_object* v_r_2364_; 
v_res_2363_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0(v_00_u03b2_2360_, v_a_2361_, v_x_2362_);
lean_dec(v_x_2362_);
lean_dec_ref(v_a_2361_);
v_r_2364_ = lean_box(v_res_2363_);
return v_r_2364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1(lean_object* v_00_u03b2_2365_, lean_object* v_data_2366_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(v_data_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2(lean_object* v_00_u03b2_2368_, lean_object* v_a_2369_, lean_object* v_b_2370_, lean_object* v_x_2371_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(v_a_2369_, v_b_2370_, v_x_2371_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6(lean_object* v_00_u03b2_2373_, lean_object* v_a_2374_, lean_object* v_x_2375_){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(v_a_2374_, v_x_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2377_, lean_object* v_a_2378_, lean_object* v_x_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6(v_00_u03b2_2377_, v_a_2378_, v_x_2379_);
lean_dec(v_x_2379_);
lean_dec_ref(v_a_2378_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14(lean_object* v_00_u03b2_2381_, lean_object* v_x_2382_, lean_object* v_x_2383_, lean_object* v_x_2384_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(v_x_2382_, v_x_2383_, v_x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2386_, lean_object* v_i_2387_, lean_object* v_source_2388_, lean_object* v_target_2389_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3___redArg(v_i_2387_, v_source_2388_, v_target_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19(lean_object* v_00_u03b2_2391_, lean_object* v_x_2392_, size_t v_x_2393_, size_t v_x_2394_, lean_object* v_x_2395_, lean_object* v_x_2396_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_x_2392_, v_x_2393_, v_x_2394_, v_x_2395_, v_x_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___boxed(lean_object* v_00_u03b2_2398_, lean_object* v_x_2399_, lean_object* v_x_2400_, lean_object* v_x_2401_, lean_object* v_x_2402_, lean_object* v_x_2403_){
_start:
{
size_t v_x_23570__boxed_2404_; size_t v_x_23571__boxed_2405_; lean_object* v_res_2406_; 
v_x_23570__boxed_2404_ = lean_unbox_usize(v_x_2400_);
lean_dec(v_x_2400_);
v_x_23571__boxed_2405_ = lean_unbox_usize(v_x_2401_);
lean_dec(v_x_2401_);
v_res_2406_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19(v_00_u03b2_2398_, v_x_2399_, v_x_23570__boxed_2404_, v_x_23571__boxed_2405_, v_x_2402_, v_x_2403_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29(lean_object* v_ref_2407_, lean_object* v_msgData_2408_, uint8_t v_severity_2409_, uint8_t v_isSilent_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(v_ref_2407_, v_msgData_2408_, v_severity_2409_, v_isSilent_2410_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___boxed(lean_object* v_ref_2418_, lean_object* v_msgData_2419_, lean_object* v_severity_2420_, lean_object* v_isSilent_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
uint8_t v_severity_boxed_2428_; uint8_t v_isSilent_boxed_2429_; lean_object* v_res_2430_; 
v_severity_boxed_2428_ = lean_unbox(v_severity_2420_);
v_isSilent_boxed_2429_ = lean_unbox(v_isSilent_2421_);
v_res_2430_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29(v_ref_2418_, v_msgData_2419_, v_severity_boxed_2428_, v_isSilent_boxed_2429_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec(v_ref_2418_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20(lean_object* v_00_u03b2_2431_, lean_object* v_x_2432_, lean_object* v_x_2433_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20___redArg(v_x_2432_, v_x_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30(lean_object* v_00_u03b2_2435_, lean_object* v_n_2436_, lean_object* v_k_2437_, lean_object* v_v_2438_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30___redArg(v_n_2436_, v_k_2437_, v_v_2438_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31(lean_object* v_00_u03b2_2440_, size_t v_depth_2441_, lean_object* v_keys_2442_, lean_object* v_vals_2443_, lean_object* v_heq_2444_, lean_object* v_i_2445_, lean_object* v_entries_2446_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(v_depth_2441_, v_keys_2442_, v_vals_2443_, v_i_2445_, v_entries_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___boxed(lean_object* v_00_u03b2_2448_, lean_object* v_depth_2449_, lean_object* v_keys_2450_, lean_object* v_vals_2451_, lean_object* v_heq_2452_, lean_object* v_i_2453_, lean_object* v_entries_2454_){
_start:
{
size_t v_depth_boxed_2455_; lean_object* v_res_2456_; 
v_depth_boxed_2455_ = lean_unbox_usize(v_depth_2449_);
lean_dec(v_depth_2449_);
v_res_2456_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31(v_00_u03b2_2448_, v_depth_boxed_2455_, v_keys_2450_, v_vals_2451_, v_heq_2452_, v_i_2453_, v_entries_2454_);
lean_dec_ref(v_vals_2451_);
lean_dec_ref(v_keys_2450_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32(lean_object* v_00_u03b2_2457_, lean_object* v_x_2458_, lean_object* v_x_2459_, lean_object* v_x_2460_, lean_object* v_x_2461_){
_start:
{
lean_object* v___x_2462_; 
v___x_2462_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32___redArg(v_x_2458_, v_x_2459_, v_x_2460_, v_x_2461_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___redArg(lean_object* v_e_2463_, lean_object* v___y_2464_){
_start:
{
uint8_t v___x_2466_; 
v___x_2466_ = l_Lean_Expr_hasMVar(v_e_2463_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; 
v___x_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2467_, 0, v_e_2463_);
return v___x_2467_;
}
else
{
lean_object* v___x_2468_; lean_object* v_mctx_2469_; lean_object* v___x_2470_; lean_object* v_fst_2471_; lean_object* v_snd_2472_; lean_object* v___x_2473_; lean_object* v_cache_2474_; lean_object* v_zetaDeltaFVarIds_2475_; lean_object* v_postponed_2476_; lean_object* v_diag_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2486_; 
v___x_2468_ = lean_st_ref_get(v___y_2464_);
v_mctx_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc_ref(v_mctx_2469_);
lean_dec(v___x_2468_);
v___x_2470_ = l_Lean_instantiateMVarsCore(v_mctx_2469_, v_e_2463_);
v_fst_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_fst_2471_);
v_snd_2472_ = lean_ctor_get(v___x_2470_, 1);
lean_inc(v_snd_2472_);
lean_dec_ref(v___x_2470_);
v___x_2473_ = lean_st_ref_take(v___y_2464_);
v_cache_2474_ = lean_ctor_get(v___x_2473_, 1);
v_zetaDeltaFVarIds_2475_ = lean_ctor_get(v___x_2473_, 2);
v_postponed_2476_ = lean_ctor_get(v___x_2473_, 3);
v_diag_2477_ = lean_ctor_get(v___x_2473_, 4);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2486_ == 0)
{
lean_object* v_unused_2487_; 
v_unused_2487_ = lean_ctor_get(v___x_2473_, 0);
lean_dec(v_unused_2487_);
v___x_2479_ = v___x_2473_;
v_isShared_2480_ = v_isSharedCheck_2486_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_diag_2477_);
lean_inc(v_postponed_2476_);
lean_inc(v_zetaDeltaFVarIds_2475_);
lean_inc(v_cache_2474_);
lean_dec(v___x_2473_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2486_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 0, v_snd_2472_);
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_snd_2472_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v_cache_2474_);
lean_ctor_set(v_reuseFailAlloc_2485_, 2, v_zetaDeltaFVarIds_2475_);
lean_ctor_set(v_reuseFailAlloc_2485_, 3, v_postponed_2476_);
lean_ctor_set(v_reuseFailAlloc_2485_, 4, v_diag_2477_);
v___x_2482_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = lean_st_ref_set(v___y_2464_, v___x_2482_);
v___x_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2484_, 0, v_fst_2471_);
return v___x_2484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___redArg___boxed(lean_object* v_e_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___redArg(v_e_2488_, v___y_2489_);
lean_dec(v___y_2489_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2(lean_object* v_e_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___redArg(v_e_2492_, v___y_2495_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___boxed(lean_object* v_e_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2(v_e_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__0___redArg(lean_object* v_m_2508_, lean_object* v_a_2509_, lean_object* v_b_2510_){
_start:
{
lean_object* v_size_2511_; lean_object* v_buckets_2512_; lean_object* v___x_2513_; uint64_t v___x_2514_; uint64_t v___x_2515_; uint64_t v___x_2516_; uint64_t v_fold_2517_; uint64_t v___x_2518_; uint64_t v___x_2519_; uint64_t v___x_2520_; size_t v___x_2521_; size_t v___x_2522_; size_t v___x_2523_; size_t v___x_2524_; size_t v___x_2525_; lean_object* v_bkt_2526_; uint8_t v___x_2527_; 
v_size_2511_ = lean_ctor_get(v_m_2508_, 0);
v_buckets_2512_ = lean_ctor_get(v_m_2508_, 1);
v___x_2513_ = lean_array_get_size(v_buckets_2512_);
v___x_2514_ = l_Lean_Expr_hash(v_a_2509_);
v___x_2515_ = 32ULL;
v___x_2516_ = lean_uint64_shift_right(v___x_2514_, v___x_2515_);
v_fold_2517_ = lean_uint64_xor(v___x_2514_, v___x_2516_);
v___x_2518_ = 16ULL;
v___x_2519_ = lean_uint64_shift_right(v_fold_2517_, v___x_2518_);
v___x_2520_ = lean_uint64_xor(v_fold_2517_, v___x_2519_);
v___x_2521_ = lean_uint64_to_usize(v___x_2520_);
v___x_2522_ = lean_usize_of_nat(v___x_2513_);
v___x_2523_ = ((size_t)1ULL);
v___x_2524_ = lean_usize_sub(v___x_2522_, v___x_2523_);
v___x_2525_ = lean_usize_land(v___x_2521_, v___x_2524_);
v_bkt_2526_ = lean_array_uget_borrowed(v_buckets_2512_, v___x_2525_);
v___x_2527_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_2509_, v_bkt_2526_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2548_; 
lean_inc_ref(v_buckets_2512_);
lean_inc(v_size_2511_);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_m_2508_);
if (v_isSharedCheck_2548_ == 0)
{
lean_object* v_unused_2549_; lean_object* v_unused_2550_; 
v_unused_2549_ = lean_ctor_get(v_m_2508_, 1);
lean_dec(v_unused_2549_);
v_unused_2550_ = lean_ctor_get(v_m_2508_, 0);
lean_dec(v_unused_2550_);
v___x_2529_ = v_m_2508_;
v_isShared_2530_ = v_isSharedCheck_2548_;
goto v_resetjp_2528_;
}
else
{
lean_dec(v_m_2508_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2548_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2531_; lean_object* v_size_x27_2532_; lean_object* v___x_2533_; lean_object* v_buckets_x27_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2531_ = lean_unsigned_to_nat(1u);
v_size_x27_2532_ = lean_nat_add(v_size_2511_, v___x_2531_);
lean_dec(v_size_2511_);
lean_inc(v_bkt_2526_);
v___x_2533_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2533_, 0, v_a_2509_);
lean_ctor_set(v___x_2533_, 1, v_b_2510_);
lean_ctor_set(v___x_2533_, 2, v_bkt_2526_);
v_buckets_x27_2534_ = lean_array_uset(v_buckets_2512_, v___x_2525_, v___x_2533_);
v___x_2535_ = lean_unsigned_to_nat(4u);
v___x_2536_ = lean_nat_mul(v_size_x27_2532_, v___x_2535_);
v___x_2537_ = lean_unsigned_to_nat(3u);
v___x_2538_ = lean_nat_div(v___x_2536_, v___x_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_array_get_size(v_buckets_x27_2534_);
v___x_2540_ = lean_nat_dec_le(v___x_2538_, v___x_2539_);
lean_dec(v___x_2538_);
if (v___x_2540_ == 0)
{
lean_object* v_val_2541_; lean_object* v___x_2543_; 
v_val_2541_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(v_buckets_x27_2534_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 1, v_val_2541_);
lean_ctor_set(v___x_2529_, 0, v_size_x27_2532_);
v___x_2543_ = v___x_2529_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_size_x27_2532_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v_val_2541_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
else
{
lean_object* v___x_2546_; 
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 1, v_buckets_x27_2534_);
lean_ctor_set(v___x_2529_, 0, v_size_x27_2532_);
v___x_2546_ = v___x_2529_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_size_x27_2532_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v_buckets_x27_2534_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
else
{
lean_dec(v_b_2510_);
lean_dec_ref(v_a_2509_);
return v_m_2508_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(lean_object* v_a_2551_, lean_object* v_x_2552_){
_start:
{
if (lean_obj_tag(v_x_2552_) == 0)
{
uint8_t v___x_2553_; 
v___x_2553_ = 0;
return v___x_2553_;
}
else
{
lean_object* v_key_2554_; lean_object* v_tail_2555_; uint8_t v___x_2556_; 
v_key_2554_ = lean_ctor_get(v_x_2552_, 0);
v_tail_2555_ = lean_ctor_get(v_x_2552_, 2);
v___x_2556_ = l_Lean_instBEqFVarId_beq(v_key_2554_, v_a_2551_);
if (v___x_2556_ == 0)
{
v_x_2552_ = v_tail_2555_;
goto _start;
}
else
{
return v___x_2556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg___boxed(lean_object* v_a_2558_, lean_object* v_x_2559_){
_start:
{
uint8_t v_res_2560_; lean_object* v_r_2561_; 
v_res_2560_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(v_a_2558_, v_x_2559_);
lean_dec(v_x_2559_);
lean_dec(v_a_2558_);
v_r_2561_ = lean_box(v_res_2560_);
return v_r_2561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_2562_, lean_object* v_x_2563_){
_start:
{
if (lean_obj_tag(v_x_2563_) == 0)
{
return v_x_2562_;
}
else
{
lean_object* v_key_2564_; lean_object* v_value_2565_; lean_object* v_tail_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2589_; 
v_key_2564_ = lean_ctor_get(v_x_2563_, 0);
v_value_2565_ = lean_ctor_get(v_x_2563_, 1);
v_tail_2566_ = lean_ctor_get(v_x_2563_, 2);
v_isSharedCheck_2589_ = !lean_is_exclusive(v_x_2563_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2568_ = v_x_2563_;
v_isShared_2569_ = v_isSharedCheck_2589_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_tail_2566_);
lean_inc(v_value_2565_);
lean_inc(v_key_2564_);
lean_dec(v_x_2563_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2589_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2570_; uint64_t v___x_2571_; uint64_t v___x_2572_; uint64_t v___x_2573_; uint64_t v_fold_2574_; uint64_t v___x_2575_; uint64_t v___x_2576_; uint64_t v___x_2577_; size_t v___x_2578_; size_t v___x_2579_; size_t v___x_2580_; size_t v___x_2581_; size_t v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2585_; 
v___x_2570_ = lean_array_get_size(v_x_2562_);
v___x_2571_ = l_Lean_instHashableFVarId_hash(v_key_2564_);
v___x_2572_ = 32ULL;
v___x_2573_ = lean_uint64_shift_right(v___x_2571_, v___x_2572_);
v_fold_2574_ = lean_uint64_xor(v___x_2571_, v___x_2573_);
v___x_2575_ = 16ULL;
v___x_2576_ = lean_uint64_shift_right(v_fold_2574_, v___x_2575_);
v___x_2577_ = lean_uint64_xor(v_fold_2574_, v___x_2576_);
v___x_2578_ = lean_uint64_to_usize(v___x_2577_);
v___x_2579_ = lean_usize_of_nat(v___x_2570_);
v___x_2580_ = ((size_t)1ULL);
v___x_2581_ = lean_usize_sub(v___x_2579_, v___x_2580_);
v___x_2582_ = lean_usize_land(v___x_2578_, v___x_2581_);
v___x_2583_ = lean_array_uget_borrowed(v_x_2562_, v___x_2582_);
lean_inc(v___x_2583_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 2, v___x_2583_);
v___x_2585_ = v___x_2568_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_key_2564_);
lean_ctor_set(v_reuseFailAlloc_2588_, 1, v_value_2565_);
lean_ctor_set(v_reuseFailAlloc_2588_, 2, v___x_2583_);
v___x_2585_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_array_uset(v_x_2562_, v___x_2582_, v___x_2585_);
v_x_2562_ = v___x_2586_;
v_x_2563_ = v_tail_2566_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4___redArg(lean_object* v_i_2590_, lean_object* v_source_2591_, lean_object* v_target_2592_){
_start:
{
lean_object* v___x_2593_; uint8_t v___x_2594_; 
v___x_2593_ = lean_array_get_size(v_source_2591_);
v___x_2594_ = lean_nat_dec_lt(v_i_2590_, v___x_2593_);
if (v___x_2594_ == 0)
{
lean_dec_ref(v_source_2591_);
lean_dec(v_i_2590_);
return v_target_2592_;
}
else
{
lean_object* v_es_2595_; lean_object* v___x_2596_; lean_object* v_source_2597_; lean_object* v_target_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v_es_2595_ = lean_array_fget(v_source_2591_, v_i_2590_);
v___x_2596_ = lean_box(0);
v_source_2597_ = lean_array_fset(v_source_2591_, v_i_2590_, v___x_2596_);
v_target_2598_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(v_target_2592_, v_es_2595_);
v___x_2599_ = lean_unsigned_to_nat(1u);
v___x_2600_ = lean_nat_add(v_i_2590_, v___x_2599_);
lean_dec(v_i_2590_);
v_i_2590_ = v___x_2600_;
v_source_2591_ = v_source_2597_;
v_target_2592_ = v_target_2598_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2___redArg(lean_object* v_data_2602_){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v_nbuckets_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2603_ = lean_array_get_size(v_data_2602_);
v___x_2604_ = lean_unsigned_to_nat(2u);
v_nbuckets_2605_ = lean_nat_mul(v___x_2603_, v___x_2604_);
v___x_2606_ = lean_unsigned_to_nat(0u);
v___x_2607_ = lean_box(0);
v___x_2608_ = lean_mk_array(v_nbuckets_2605_, v___x_2607_);
v___x_2609_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4___redArg(v___x_2606_, v_data_2602_, v___x_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1___redArg(lean_object* v_m_2610_, lean_object* v_a_2611_, lean_object* v_b_2612_){
_start:
{
lean_object* v_size_2613_; lean_object* v_buckets_2614_; lean_object* v___x_2615_; uint64_t v___x_2616_; uint64_t v___x_2617_; uint64_t v___x_2618_; uint64_t v_fold_2619_; uint64_t v___x_2620_; uint64_t v___x_2621_; uint64_t v___x_2622_; size_t v___x_2623_; size_t v___x_2624_; size_t v___x_2625_; size_t v___x_2626_; size_t v___x_2627_; lean_object* v_bkt_2628_; uint8_t v___x_2629_; 
v_size_2613_ = lean_ctor_get(v_m_2610_, 0);
v_buckets_2614_ = lean_ctor_get(v_m_2610_, 1);
v___x_2615_ = lean_array_get_size(v_buckets_2614_);
v___x_2616_ = l_Lean_instHashableFVarId_hash(v_a_2611_);
v___x_2617_ = 32ULL;
v___x_2618_ = lean_uint64_shift_right(v___x_2616_, v___x_2617_);
v_fold_2619_ = lean_uint64_xor(v___x_2616_, v___x_2618_);
v___x_2620_ = 16ULL;
v___x_2621_ = lean_uint64_shift_right(v_fold_2619_, v___x_2620_);
v___x_2622_ = lean_uint64_xor(v_fold_2619_, v___x_2621_);
v___x_2623_ = lean_uint64_to_usize(v___x_2622_);
v___x_2624_ = lean_usize_of_nat(v___x_2615_);
v___x_2625_ = ((size_t)1ULL);
v___x_2626_ = lean_usize_sub(v___x_2624_, v___x_2625_);
v___x_2627_ = lean_usize_land(v___x_2623_, v___x_2626_);
v_bkt_2628_ = lean_array_uget_borrowed(v_buckets_2614_, v___x_2627_);
v___x_2629_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(v_a_2611_, v_bkt_2628_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2650_; 
lean_inc_ref(v_buckets_2614_);
lean_inc(v_size_2613_);
v_isSharedCheck_2650_ = !lean_is_exclusive(v_m_2610_);
if (v_isSharedCheck_2650_ == 0)
{
lean_object* v_unused_2651_; lean_object* v_unused_2652_; 
v_unused_2651_ = lean_ctor_get(v_m_2610_, 1);
lean_dec(v_unused_2651_);
v_unused_2652_ = lean_ctor_get(v_m_2610_, 0);
lean_dec(v_unused_2652_);
v___x_2631_ = v_m_2610_;
v_isShared_2632_ = v_isSharedCheck_2650_;
goto v_resetjp_2630_;
}
else
{
lean_dec(v_m_2610_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2650_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2633_; lean_object* v_size_x27_2634_; lean_object* v___x_2635_; lean_object* v_buckets_x27_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2633_ = lean_unsigned_to_nat(1u);
v_size_x27_2634_ = lean_nat_add(v_size_2613_, v___x_2633_);
lean_dec(v_size_2613_);
lean_inc(v_bkt_2628_);
v___x_2635_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2635_, 0, v_a_2611_);
lean_ctor_set(v___x_2635_, 1, v_b_2612_);
lean_ctor_set(v___x_2635_, 2, v_bkt_2628_);
v_buckets_x27_2636_ = lean_array_uset(v_buckets_2614_, v___x_2627_, v___x_2635_);
v___x_2637_ = lean_unsigned_to_nat(4u);
v___x_2638_ = lean_nat_mul(v_size_x27_2634_, v___x_2637_);
v___x_2639_ = lean_unsigned_to_nat(3u);
v___x_2640_ = lean_nat_div(v___x_2638_, v___x_2639_);
lean_dec(v___x_2638_);
v___x_2641_ = lean_array_get_size(v_buckets_x27_2636_);
v___x_2642_ = lean_nat_dec_le(v___x_2640_, v___x_2641_);
lean_dec(v___x_2640_);
if (v___x_2642_ == 0)
{
lean_object* v_val_2643_; lean_object* v___x_2645_; 
v_val_2643_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2___redArg(v_buckets_x27_2636_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 1, v_val_2643_);
lean_ctor_set(v___x_2631_, 0, v_size_x27_2634_);
v___x_2645_ = v___x_2631_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_size_x27_2634_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v_val_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
else
{
lean_object* v___x_2648_; 
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 1, v_buckets_x27_2636_);
lean_ctor_set(v___x_2631_, 0, v_size_x27_2634_);
v___x_2648_ = v___x_2631_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_size_x27_2634_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v_buckets_x27_2636_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
else
{
lean_dec(v_b_2612_);
lean_dec(v_a_2611_);
return v_m_2610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__1(lean_object* v___x_2653_, lean_object* v_a_2654_, lean_object* v_e_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v___x_2662_; lean_object* v_relevantTerms_2663_; lean_object* v_relevantHyps_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2686_; 
v___x_2662_ = lean_st_ref_take(v___y_2656_);
v_relevantTerms_2663_ = lean_ctor_get(v___x_2662_, 0);
v_relevantHyps_2664_ = lean_ctor_get(v___x_2662_, 1);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2666_ = v___x_2662_;
v_isShared_2667_ = v_isSharedCheck_2686_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_relevantHyps_2664_);
lean_inc(v_relevantTerms_2663_);
lean_dec(v___x_2662_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2686_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2668_; lean_object* v___x_2670_; 
v___x_2668_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__0___redArg(v_relevantTerms_2663_, v_e_2655_, v___x_2653_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v___x_2668_);
v___x_2670_ = v___x_2666_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_relevantHyps_2664_);
v___x_2670_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v_relevantTerms_2673_; lean_object* v_relevantHyps_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2684_; 
v___x_2671_ = lean_st_ref_set(v___y_2656_, v___x_2670_);
v___x_2672_ = lean_st_ref_take(v___y_2656_);
v_relevantTerms_2673_ = lean_ctor_get(v___x_2672_, 0);
v_relevantHyps_2674_ = lean_ctor_get(v___x_2672_, 1);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2676_ = v___x_2672_;
v_isShared_2677_ = v_isSharedCheck_2684_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_relevantHyps_2674_);
lean_inc(v_relevantTerms_2673_);
lean_dec(v___x_2672_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2684_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2678_; lean_object* v___x_2680_; 
v___x_2678_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1___redArg(v_relevantHyps_2674_, v_a_2654_, v___x_2653_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 1, v___x_2678_);
v___x_2680_ = v___x_2676_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_relevantTerms_2673_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v___x_2678_);
v___x_2680_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2681_ = lean_st_ref_set(v___y_2656_, v___x_2680_);
v___x_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2653_);
return v___x_2682_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__1___boxed(lean_object* v___x_2687_, lean_object* v_a_2688_, lean_object* v_e_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__1(v___x_2687_, v_a_2688_, v_e_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
return v_res_2696_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0(lean_object* v_e_2706_){
_start:
{
uint8_t v___y_2708_; lean_object* v___x_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; 
v___x_2711_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2));
v___x_2712_ = lean_unsigned_to_nat(1u);
v___x_2713_ = l_Lean_Expr_isAppOfArity(v_e_2706_, v___x_2711_, v___x_2712_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; uint8_t v___x_2715_; 
v___x_2714_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4));
v___x_2715_ = l_Lean_Expr_isAppOfArity(v_e_2706_, v___x_2714_, v___x_2712_);
v___y_2708_ = v___x_2715_;
goto v___jp_2707_;
}
else
{
v___y_2708_ = v___x_2713_;
goto v___jp_2707_;
}
v___jp_2707_:
{
if (v___y_2708_ == 0)
{
return v___y_2708_;
}
else
{
uint8_t v___x_2709_; 
v___x_2709_ = l_Lean_Expr_hasLooseBVars(v_e_2706_);
if (v___x_2709_ == 0)
{
return v___y_2708_;
}
else
{
uint8_t v___x_2710_; 
v___x_2710_ = 0;
return v___x_2710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___boxed(lean_object* v_e_2716_){
_start:
{
uint8_t v_res_2717_; lean_object* v_r_2718_; 
v_res_2717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0(v_e_2716_);
lean_dec_ref(v_e_2716_);
v_r_2718_ = lean_box(v_res_2717_);
return v_r_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(lean_object* v_e_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v___x_2722_; lean_object* v_visited_2723_; size_t v___x_2724_; size_t v___x_2725_; size_t v___x_2726_; lean_object* v___x_2727_; size_t v___x_2728_; uint8_t v___x_2729_; 
v___x_2722_ = lean_st_ref_get(v_a_2720_);
v_visited_2723_ = lean_ctor_get(v___x_2722_, 0);
lean_inc_ref(v_visited_2723_);
lean_dec(v___x_2722_);
v___x_2724_ = lean_ptr_addr(v_e_2719_);
v___x_2725_ = ((size_t)8191ULL);
v___x_2726_ = lean_usize_mod(v___x_2724_, v___x_2725_);
v___x_2727_ = lean_array_uget(v_visited_2723_, v___x_2726_);
lean_dec_ref(v_visited_2723_);
v___x_2728_ = lean_ptr_addr(v___x_2727_);
lean_dec(v___x_2727_);
v___x_2729_ = lean_usize_dec_eq(v___x_2728_, v___x_2724_);
if (v___x_2729_ == 0)
{
lean_object* v___x_2730_; lean_object* v_visited_2731_; lean_object* v_checked_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2743_; 
v___x_2730_ = lean_st_ref_take(v_a_2720_);
v_visited_2731_ = lean_ctor_get(v___x_2730_, 0);
v_checked_2732_ = lean_ctor_get(v___x_2730_, 1);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2734_ = v___x_2730_;
v_isShared_2735_ = v_isSharedCheck_2743_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_checked_2732_);
lean_inc(v_visited_2731_);
lean_dec(v___x_2730_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2743_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2736_; lean_object* v___x_2738_; 
v___x_2736_ = lean_array_uset(v_visited_2731_, v___x_2726_, v_e_2719_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 0, v___x_2736_);
v___x_2738_ = v___x_2734_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v_checked_2732_);
v___x_2738_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2739_ = lean_st_ref_set(v_a_2720_, v___x_2738_);
v___x_2740_ = lean_box(v___x_2729_);
v___x_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
return v___x_2741_;
}
}
}
else
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
lean_dec_ref(v_e_2719_);
v___x_2744_ = lean_box(v___x_2729_);
v___x_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
return v___x_2745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_e_2746_, lean_object* v_a_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(v_e_2746_, v_a_2747_);
lean_dec(v_a_2747_);
return v_res_2749_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(lean_object* v_m_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_buckets_2752_; lean_object* v___x_2753_; uint64_t v___x_2754_; uint64_t v___x_2755_; uint64_t v___x_2756_; uint64_t v_fold_2757_; uint64_t v___x_2758_; uint64_t v___x_2759_; uint64_t v___x_2760_; size_t v___x_2761_; size_t v___x_2762_; size_t v___x_2763_; size_t v___x_2764_; size_t v___x_2765_; lean_object* v___x_2766_; uint8_t v___x_2767_; 
v_buckets_2752_ = lean_ctor_get(v_m_2750_, 1);
v___x_2753_ = lean_array_get_size(v_buckets_2752_);
v___x_2754_ = l_Lean_Expr_hash(v_a_2751_);
v___x_2755_ = 32ULL;
v___x_2756_ = lean_uint64_shift_right(v___x_2754_, v___x_2755_);
v_fold_2757_ = lean_uint64_xor(v___x_2754_, v___x_2756_);
v___x_2758_ = 16ULL;
v___x_2759_ = lean_uint64_shift_right(v_fold_2757_, v___x_2758_);
v___x_2760_ = lean_uint64_xor(v_fold_2757_, v___x_2759_);
v___x_2761_ = lean_uint64_to_usize(v___x_2760_);
v___x_2762_ = lean_usize_of_nat(v___x_2753_);
v___x_2763_ = ((size_t)1ULL);
v___x_2764_ = lean_usize_sub(v___x_2762_, v___x_2763_);
v___x_2765_ = lean_usize_land(v___x_2761_, v___x_2764_);
v___x_2766_ = lean_array_uget_borrowed(v_buckets_2752_, v___x_2765_);
v___x_2767_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_2751_, v___x_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg___boxed(lean_object* v_m_2768_, lean_object* v_a_2769_){
_start:
{
uint8_t v_res_2770_; lean_object* v_r_2771_; 
v_res_2770_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(v_m_2768_, v_a_2769_);
lean_dec_ref(v_a_2769_);
lean_dec_ref(v_m_2768_);
v_r_2771_ = lean_box(v_res_2770_);
return v_r_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(lean_object* v_e_2772_, lean_object* v_a_2773_){
_start:
{
lean_object* v___x_2775_; lean_object* v_checked_2776_; uint8_t v___x_2777_; 
v___x_2775_ = lean_st_ref_get(v_a_2773_);
v_checked_2776_ = lean_ctor_get(v___x_2775_, 1);
lean_inc_ref(v_checked_2776_);
lean_dec(v___x_2775_);
v___x_2777_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(v_checked_2776_, v_e_2772_);
lean_dec_ref(v_checked_2776_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; lean_object* v_visited_2779_; lean_object* v_checked_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2792_; 
v___x_2778_ = lean_st_ref_take(v_a_2773_);
v_visited_2779_ = lean_ctor_get(v___x_2778_, 0);
v_checked_2780_ = lean_ctor_get(v___x_2778_, 1);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2782_ = v___x_2778_;
v_isShared_2783_ = v_isSharedCheck_2792_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_checked_2780_);
lean_inc(v_visited_2779_);
lean_dec(v___x_2778_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2792_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2784_ = lean_box(0);
v___x_2785_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__0___redArg(v_checked_2780_, v_e_2772_, v___x_2784_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 1, v___x_2785_);
v___x_2787_ = v___x_2782_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_visited_2779_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2788_ = lean_st_ref_set(v_a_2773_, v___x_2787_);
v___x_2789_ = lean_box(v___x_2777_);
v___x_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
return v___x_2790_;
}
}
}
else
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
lean_dec_ref(v_e_2772_);
v___x_2793_ = lean_box(v___x_2777_);
v___x_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
return v___x_2794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_e_2795_, lean_object* v_a_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(v_e_2795_, v_a_2796_);
lean_dec(v_a_2796_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(lean_object* v_p_2799_, lean_object* v_f_2800_, uint8_t v_stopWhenVisited_2801_, lean_object* v_e_2802_, lean_object* v_a_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v_d_2816_; lean_object* v_b_2817_; lean_object* v___y_2818_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___x_2848_; 
lean_inc_ref(v_e_2802_);
v___x_2848_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(v_e_2802_, v_a_2803_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2881_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2851_ = v___x_2848_;
v_isShared_2852_ = v_isSharedCheck_2881_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2848_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2881_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
uint8_t v___x_2853_; 
v___x_2853_ = lean_unbox(v_a_2849_);
lean_dec(v_a_2849_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; uint8_t v___x_2855_; 
lean_del_object(v___x_2851_);
lean_inc_ref(v_p_2799_);
lean_inc_ref(v_e_2802_);
v___x_2854_ = lean_apply_1(v_p_2799_, v_e_2802_);
v___x_2855_ = lean_unbox(v___x_2854_);
if (v___x_2855_ == 0)
{
v___y_2822_ = v_a_2803_;
v___y_2823_ = v___y_2804_;
v___y_2824_ = v___y_2805_;
v___y_2825_ = v___y_2806_;
v___y_2826_ = v___y_2807_;
v___y_2827_ = v___y_2808_;
goto v___jp_2821_;
}
else
{
lean_object* v___x_2856_; 
lean_inc_ref(v_e_2802_);
v___x_2856_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(v_e_2802_, v_a_2803_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; uint8_t v___x_2858_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2857_);
lean_dec_ref_known(v___x_2856_, 1);
v___x_2858_ = lean_unbox(v_a_2857_);
lean_dec(v_a_2857_);
if (v___x_2858_ == 0)
{
lean_object* v___x_2859_; 
lean_inc_ref(v_f_2800_);
lean_inc(v___y_2808_);
lean_inc_ref(v___y_2807_);
lean_inc(v___y_2806_);
lean_inc_ref(v___y_2805_);
lean_inc(v___y_2804_);
lean_inc_ref(v_e_2802_);
v___x_2859_ = lean_apply_7(v_f_2800_, v_e_2802_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, lean_box(0));
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2867_; 
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2867_ == 0)
{
lean_object* v_unused_2868_; 
v_unused_2868_ = lean_ctor_get(v___x_2859_, 0);
lean_dec(v_unused_2868_);
v___x_2861_ = v___x_2859_;
v_isShared_2862_ = v_isSharedCheck_2867_;
goto v_resetjp_2860_;
}
else
{
lean_dec(v___x_2859_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2867_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
if (v_stopWhenVisited_2801_ == 0)
{
lean_del_object(v___x_2861_);
v___y_2822_ = v_a_2803_;
v___y_2823_ = v___y_2804_;
v___y_2824_ = v___y_2805_;
v___y_2825_ = v___y_2806_;
v___y_2826_ = v___y_2807_;
v___y_2827_ = v___y_2808_;
goto v___jp_2821_;
}
else
{
lean_object* v___x_2863_; lean_object* v___x_2865_; 
lean_dec_ref(v_e_2802_);
lean_dec_ref(v_f_2800_);
lean_dec_ref(v_p_2799_);
v___x_2863_ = lean_box(0);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 0, v___x_2863_);
v___x_2865_ = v___x_2861_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2863_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
else
{
lean_dec_ref(v_e_2802_);
lean_dec_ref(v_f_2800_);
lean_dec_ref(v_p_2799_);
return v___x_2859_;
}
}
else
{
v___y_2822_ = v_a_2803_;
v___y_2823_ = v___y_2804_;
v___y_2824_ = v___y_2805_;
v___y_2825_ = v___y_2806_;
v___y_2826_ = v___y_2807_;
v___y_2827_ = v___y_2808_;
goto v___jp_2821_;
}
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
lean_dec_ref(v_e_2802_);
lean_dec_ref(v_f_2800_);
lean_dec_ref(v_p_2799_);
v_a_2869_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2856_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2856_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
}
else
{
lean_object* v___x_2877_; lean_object* v___x_2879_; 
lean_dec_ref(v_e_2802_);
lean_dec_ref(v_f_2800_);
lean_dec_ref(v_p_2799_);
v___x_2877_ = lean_box(0);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 0, v___x_2877_);
v___x_2879_ = v___x_2851_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2877_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec_ref(v_e_2802_);
lean_dec_ref(v_f_2800_);
lean_dec_ref(v_p_2799_);
v_a_2882_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2848_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2848_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
v___jp_2810_:
{
lean_object* v___x_2819_; 
lean_inc_ref(v_f_2800_);
lean_inc_ref(v_p_2799_);
v___x_2819_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2799_, v_f_2800_, v_stopWhenVisited_2801_, v_d_2816_, v___y_2818_, v___y_2814_, v___y_2813_, v___y_2811_, v___y_2815_, v___y_2812_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_dec_ref_known(v___x_2819_, 1);
v_e_2802_ = v_b_2817_;
v_a_2803_ = v___y_2818_;
v___y_2804_ = v___y_2814_;
v___y_2805_ = v___y_2813_;
v___y_2806_ = v___y_2811_;
v___y_2807_ = v___y_2815_;
v___y_2808_ = v___y_2812_;
goto _start;
}
else
{
lean_dec_ref(v_b_2817_);
lean_dec_ref(v_f_2800_);
lean_dec_ref(v_p_2799_);
return v___x_2819_;
}
}
v___jp_2821_:
{
switch(lean_obj_tag(v_e_2802_))
{
case 7:
{
lean_object* v_binderType_2828_; lean_object* v_body_2829_; 
v_binderType_2828_ = lean_ctor_get(v_e_2802_, 1);
lean_inc_ref(v_binderType_2828_);
v_body_2829_ = lean_ctor_get(v_e_2802_, 2);
lean_inc_ref(v_body_2829_);
lean_dec_ref_known(v_e_2802_, 3);
v___y_2811_ = v___y_2825_;
v___y_2812_ = v___y_2827_;
v___y_2813_ = v___y_2824_;
v___y_2814_ = v___y_2823_;
v___y_2815_ = v___y_2826_;
v_d_2816_ = v_binderType_2828_;
v_b_2817_ = v_body_2829_;
v___y_2818_ = v___y_2822_;
goto v___jp_2810_;
}
case 6:
{
lean_object* v_binderType_2830_; lean_object* v_body_2831_; 
v_binderType_2830_ = lean_ctor_get(v_e_2802_, 1);
lean_inc_ref(v_binderType_2830_);
v_body_2831_ = lean_ctor_get(v_e_2802_, 2);
lean_inc_ref(v_body_2831_);
lean_dec_ref_known(v_e_2802_, 3);
v___y_2811_ = v___y_2825_;
v___y_2812_ = v___y_2827_;
v___y_2813_ = v___y_2824_;
v___y_2814_ = v___y_2823_;
v___y_2815_ = v___y_2826_;
v_d_2816_ = v_binderType_2830_;
v_b_2817_ = v_body_2831_;
v___y_2818_ = v___y_2822_;
goto v___jp_2810_;
}
case 8:
{
lean_object* v_type_2832_; lean_object* v_value_2833_; lean_object* v_body_2834_; lean_object* v___x_2835_; 
v_type_2832_ = lean_ctor_get(v_e_2802_, 1);
lean_inc_ref(v_type_2832_);
v_value_2833_ = lean_ctor_get(v_e_2802_, 2);
lean_inc_ref(v_value_2833_);
v_body_2834_ = lean_ctor_get(v_e_2802_, 3);
lean_inc_ref(v_body_2834_);
lean_dec_ref_known(v_e_2802_, 4);
lean_inc_ref(v_f_2800_);
lean_inc_ref(v_p_2799_);
v___x_2835_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2799_, v_f_2800_, v_stopWhenVisited_2801_, v_type_2832_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v___x_2836_; 
lean_dec_ref_known(v___x_2835_, 1);
lean_inc_ref(v_f_2800_);
lean_inc_ref(v_p_2799_);
v___x_2836_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2799_, v_f_2800_, v_stopWhenVisited_2801_, v_value_2833_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_dec_ref_known(v___x_2836_, 1);
v_e_2802_ = v_body_2834_;
v_a_2803_ = v___y_2822_;
v___y_2804_ = v___y_2823_;
v___y_2805_ = v___y_2824_;
v___y_2806_ = v___y_2825_;
v___y_2807_ = v___y_2826_;
v___y_2808_ = v___y_2827_;
goto _start;
}
else
{
lean_dec_ref(v_body_2834_);
lean_dec_ref(v_f_2800_);
lean_dec_ref(v_p_2799_);
return v___x_2836_;
}
}
else
{
lean_dec_ref(v_body_2834_);
lean_dec_ref(v_value_2833_);
lean_dec_ref(v_f_2800_);
lean_dec_ref(v_p_2799_);
return v___x_2835_;
}
}
case 5:
{
lean_object* v_fn_2838_; lean_object* v_arg_2839_; lean_object* v___x_2840_; 
v_fn_2838_ = lean_ctor_get(v_e_2802_, 0);
lean_inc_ref(v_fn_2838_);
v_arg_2839_ = lean_ctor_get(v_e_2802_, 1);
lean_inc_ref(v_arg_2839_);
lean_dec_ref_known(v_e_2802_, 2);
lean_inc_ref(v_f_2800_);
lean_inc_ref(v_p_2799_);
v___x_2840_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2799_, v_f_2800_, v_stopWhenVisited_2801_, v_fn_2838_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_dec_ref_known(v___x_2840_, 1);
v_e_2802_ = v_arg_2839_;
v_a_2803_ = v___y_2822_;
v___y_2804_ = v___y_2823_;
v___y_2805_ = v___y_2824_;
v___y_2806_ = v___y_2825_;
v___y_2807_ = v___y_2826_;
v___y_2808_ = v___y_2827_;
goto _start;
}
else
{
lean_dec_ref(v_arg_2839_);
lean_dec_ref(v_f_2800_);
lean_dec_ref(v_p_2799_);
return v___x_2840_;
}
}
case 10:
{
lean_object* v_expr_2842_; 
v_expr_2842_ = lean_ctor_get(v_e_2802_, 1);
lean_inc_ref(v_expr_2842_);
lean_dec_ref_known(v_e_2802_, 2);
v_e_2802_ = v_expr_2842_;
v_a_2803_ = v___y_2822_;
v___y_2804_ = v___y_2823_;
v___y_2805_ = v___y_2824_;
v___y_2806_ = v___y_2825_;
v___y_2807_ = v___y_2826_;
v___y_2808_ = v___y_2827_;
goto _start;
}
case 11:
{
lean_object* v_struct_2844_; 
v_struct_2844_ = lean_ctor_get(v_e_2802_, 2);
lean_inc_ref(v_struct_2844_);
lean_dec_ref_known(v_e_2802_, 3);
v_e_2802_ = v_struct_2844_;
v_a_2803_ = v___y_2822_;
v___y_2804_ = v___y_2823_;
v___y_2805_ = v___y_2824_;
v___y_2806_ = v___y_2825_;
v___y_2807_ = v___y_2826_;
v___y_2808_ = v___y_2827_;
goto _start;
}
default: 
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
lean_dec_ref(v_e_2802_);
lean_dec_ref(v_f_2800_);
lean_dec_ref(v_p_2799_);
v___x_2846_ = lean_box(0);
v___x_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
return v___x_2847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5___boxed(lean_object* v_p_2890_, lean_object* v_f_2891_, lean_object* v_stopWhenVisited_2892_, lean_object* v_e_2893_, lean_object* v_a_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
uint8_t v_stopWhenVisited_boxed_2901_; lean_object* v_res_2902_; 
v_stopWhenVisited_boxed_2901_ = lean_unbox(v_stopWhenVisited_2892_);
v_res_2902_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2890_, v_f_2891_, v_stopWhenVisited_boxed_2901_, v_e_2893_, v_a_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec(v_a_2894_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3(lean_object* v_p_2903_, lean_object* v_f_2904_, lean_object* v_e_2905_, uint8_t v_stopWhenVisited_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2913_ = l_Lean_ForEachExprWhere_initCache;
v___x_2914_ = lean_st_mk_ref(v___x_2913_);
v___x_2915_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2903_, v_f_2904_, v_stopWhenVisited_2906_, v_e_2905_, v___x_2914_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2924_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2918_ = v___x_2915_;
v_isShared_2919_ = v_isSharedCheck_2924_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2915_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2924_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2920_; lean_object* v___x_2922_; 
v___x_2920_ = lean_st_ref_get(v___x_2914_);
lean_dec(v___x_2914_);
lean_dec(v___x_2920_);
if (v_isShared_2919_ == 0)
{
v___x_2922_ = v___x_2918_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2916_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
else
{
lean_dec(v___x_2914_);
return v___x_2915_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3___boxed(lean_object* v_p_2925_, lean_object* v_f_2926_, lean_object* v_e_2927_, lean_object* v_stopWhenVisited_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
uint8_t v_stopWhenVisited_boxed_2935_; lean_object* v_res_2936_; 
v_stopWhenVisited_boxed_2935_ = lean_unbox(v_stopWhenVisited_2928_);
v_res_2936_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3(v_p_2925_, v_f_2926_, v_e_2927_, v_stopWhenVisited_boxed_2935_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4(lean_object* v_as_2938_, size_t v_sz_2939_, size_t v_i_2940_, lean_object* v_b_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
uint8_t v___x_2948_; 
v___x_2948_ = lean_usize_dec_lt(v_i_2940_, v_sz_2939_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; 
v___x_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2949_, 0, v_b_2941_);
return v___x_2949_;
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2951_; 
v_a_2950_ = lean_array_uget_borrowed(v_as_2938_, v_i_2940_);
lean_inc(v_a_2950_);
v___x_2951_ = l_Lean_FVarId_getType___redArg(v_a_2950_, v___y_2943_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2953_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref_known(v___x_2951_, 1);
v___x_2953_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___redArg(v_a_2952_, v___y_2944_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v___f_2955_; lean_object* v___x_2956_; lean_object* v___f_2957_; lean_object* v___x_2958_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2953_, 1);
v___f_2955_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___closed__0));
v___x_2956_ = lean_box(0);
lean_inc(v_a_2950_);
v___f_2957_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__1___boxed), 9, 2);
lean_closure_set(v___f_2957_, 0, v___x_2956_);
lean_closure_set(v___f_2957_, 1, v_a_2950_);
v___x_2958_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3(v___f_2955_, v___f_2957_, v_a_2954_, v___x_2948_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_2958_) == 0)
{
size_t v___x_2959_; size_t v___x_2960_; 
lean_dec_ref_known(v___x_2958_, 1);
v___x_2959_ = ((size_t)1ULL);
v___x_2960_ = lean_usize_add(v_i_2940_, v___x_2959_);
v_i_2940_ = v___x_2960_;
v_b_2941_ = v___x_2956_;
goto _start;
}
else
{
return v___x_2958_;
}
}
else
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
v_a_2962_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2953_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2953_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2967_; 
if (v_isShared_2965_ == 0)
{
v___x_2967_ = v___x_2964_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2962_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
v_a_2970_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2951_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2951_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___boxed(lean_object* v_as_2978_, lean_object* v_sz_2979_, lean_object* v_i_2980_, lean_object* v_b_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
size_t v_sz_boxed_2988_; size_t v_i_boxed_2989_; lean_object* v_res_2990_; 
v_sz_boxed_2988_ = lean_unbox_usize(v_sz_2979_);
lean_dec(v_sz_2979_);
v_i_boxed_2989_ = lean_unbox_usize(v_i_2980_);
lean_dec(v_i_2980_);
v_res_2990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4(v_as_2978_, v_sz_boxed_2988_, v_i_boxed_2989_, v_b_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v_as_2978_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___lam__0(lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Lean_Meta_getPropHyps(v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_2999_; size_t v_sz_3000_; size_t v___x_3001_; lean_object* v___x_3002_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v___x_2997_, 1);
v___x_2999_ = lean_box(0);
v_sz_3000_ = lean_array_size(v_a_2998_);
v___x_3001_ = ((size_t)0ULL);
v___x_3002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4(v_a_2998_, v_sz_3000_, v___x_3001_, v___x_2999_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
lean_dec(v_a_2998_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3021_; 
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3021_ == 0)
{
lean_object* v_unused_3022_; 
v_unused_3022_ = lean_ctor_get(v___x_3002_, 0);
lean_dec(v_unused_3022_);
v___x_3004_ = v___x_3002_;
v_isShared_3005_ = v_isSharedCheck_3021_;
goto v_resetjp_3003_;
}
else
{
lean_dec(v___x_3002_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3021_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3006_; lean_object* v_relevantTerms_3007_; lean_object* v_size_3008_; lean_object* v___x_3009_; uint8_t v___x_3010_; 
v___x_3006_ = lean_st_ref_get(v___y_2991_);
v_relevantTerms_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc_ref(v_relevantTerms_3007_);
lean_dec(v___x_3006_);
v_size_3008_ = lean_ctor_get(v_relevantTerms_3007_, 0);
lean_inc(v_size_3008_);
lean_dec_ref(v_relevantTerms_3007_);
v___x_3009_ = lean_unsigned_to_nat(0u);
v___x_3010_ = lean_nat_dec_eq(v_size_3008_, v___x_3009_);
lean_dec(v_size_3008_);
if (v___x_3010_ == 0)
{
uint8_t v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3014_; 
v___x_3011_ = 1;
v___x_3012_ = lean_box(v___x_3011_);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 0, v___x_3012_);
v___x_3014_ = v___x_3004_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_3012_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
else
{
uint8_t v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3019_; 
v___x_3016_ = 0;
v___x_3017_ = lean_box(v___x_3016_);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 0, v___x_3017_);
v___x_3019_ = v___x_3004_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3017_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
v_a_3023_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_3002_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3002_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
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
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
v_a_3031_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_2997_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_2997_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___lam__0___boxed(lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___lam__0(v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize(lean_object* v_goal_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_){
_start:
{
lean_object* v___f_3054_; lean_object* v___x_3055_; 
v___f_3054_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___closed__0));
v___x_3055_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_goal_3047_, v___f_3054_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___boxed(lean_object* v_goal_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize(v_goal_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec_ref(v_a_3058_);
lean_dec(v_a_3057_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__0(lean_object* v_00_u03b2_3064_, lean_object* v_m_3065_, lean_object* v_a_3066_, lean_object* v_b_3067_){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__0___redArg(v_m_3065_, v_a_3066_, v_b_3067_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1(lean_object* v_00_u03b2_3069_, lean_object* v_m_3070_, lean_object* v_a_3071_, lean_object* v_b_3072_){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1___redArg(v_m_3070_, v_a_3071_, v_b_3072_);
return v___x_3073_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1(lean_object* v_00_u03b2_3074_, lean_object* v_a_3075_, lean_object* v_x_3076_){
_start:
{
uint8_t v___x_3077_; 
v___x_3077_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(v_a_3075_, v_x_3076_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3078_, lean_object* v_a_3079_, lean_object* v_x_3080_){
_start:
{
uint8_t v_res_3081_; lean_object* v_r_3082_; 
v_res_3081_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1(v_00_u03b2_3078_, v_a_3079_, v_x_3080_);
lean_dec(v_x_3080_);
lean_dec(v_a_3079_);
v_r_3082_ = lean_box(v_res_3081_);
return v_r_3082_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2(lean_object* v_00_u03b2_3083_, lean_object* v_data_3084_){
_start:
{
lean_object* v___x_3085_; 
v___x_3085_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2___redArg(v_data_3084_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7(lean_object* v_e_3086_, lean_object* v_a_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v___x_3094_; 
v___x_3094_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(v_e_3086_, v_a_3087_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___boxed(lean_object* v_e_3095_, lean_object* v_a_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7(v_e_3095_, v_a_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec(v_a_3096_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3104_, lean_object* v_i_3105_, lean_object* v_source_3106_, lean_object* v_target_3107_){
_start:
{
lean_object* v___x_3108_; 
v___x_3108_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4___redArg(v_i_3105_, v_source_3106_, v_target_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8(lean_object* v_e_3109_, lean_object* v_a_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(v_e_3109_, v_a_3110_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___boxed(lean_object* v_e_3118_, lean_object* v_a_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8(v_e_3118_, v_a_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec(v_a_3119_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_3127_, lean_object* v_x_3128_, lean_object* v_x_3129_){
_start:
{
lean_object* v___x_3130_; 
v___x_3130_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(v_x_3128_, v_x_3129_);
return v___x_3130_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11(lean_object* v_00_u03b2_3131_, lean_object* v_m_3132_, lean_object* v_a_3133_){
_start:
{
uint8_t v___x_3134_; 
v___x_3134_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(v_m_3132_, v_a_3133_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___boxed(lean_object* v_00_u03b2_3135_, lean_object* v_m_3136_, lean_object* v_a_3137_){
_start:
{
uint8_t v_res_3138_; lean_object* v_r_3139_; 
v_res_3138_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11(v_00_u03b2_3135_, v_m_3136_, v_a_3137_);
lean_dec_ref(v_a_3137_);
lean_dec_ref(v_m_3136_);
v_r_3139_ = lean_box(v_res_3138_);
return v_r_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_handleSize(lean_object* v_goal_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v___x_3147_; 
lean_inc(v_goal_3140_);
v___x_3147_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize(v_goal_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3157_; 
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3150_ = v___x_3147_;
v_isShared_3151_ = v_isSharedCheck_3157_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3147_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3157_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
uint8_t v___x_3152_; 
v___x_3152_ = lean_unbox(v_a_3148_);
lean_dec(v_a_3148_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3154_; 
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 0, v_goal_3140_);
v___x_3154_ = v___x_3150_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_goal_3140_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
else
{
lean_object* v___x_3156_; 
lean_del_object(v___x_3150_);
v___x_3156_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize(v_goal_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
return v___x_3156_;
}
}
}
else
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_dec(v_goal_3140_);
v_a_3158_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3147_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3147_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_handleSize___boxed(lean_object* v_goal_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_handleSize(v_goal_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_);
lean_dec(v_a_3171_);
lean_dec_ref(v_a_3170_);
lean_dec(v_a_3169_);
lean_dec_ref(v_a_3168_);
lean_dec(v_a_3167_);
return v_res_3173_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3176_; 
v___x_3176_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3176_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__1);
v___x_3178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
return v___x_3178_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3179_ = lean_unsigned_to_nat(0u);
v___x_3180_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2);
v___x_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
lean_ctor_set(v___x_3181_, 1, v___x_3179_);
return v___x_3181_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3182_ = lean_unsigned_to_nat(32u);
v___x_3183_ = lean_mk_empty_array_with_capacity(v___x_3182_);
v___x_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
return v___x_3184_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__5(void){
_start:
{
size_t v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3185_ = ((size_t)5ULL);
v___x_3186_ = lean_unsigned_to_nat(0u);
v___x_3187_ = lean_unsigned_to_nat(32u);
v___x_3188_ = lean_mk_empty_array_with_capacity(v___x_3187_);
v___x_3189_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__4);
v___x_3190_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
lean_ctor_set(v___x_3190_, 1, v___x_3188_);
lean_ctor_set(v___x_3190_, 2, v___x_3186_);
lean_ctor_set(v___x_3190_, 3, v___x_3186_);
lean_ctor_set_usize(v___x_3190_, 4, v___x_3185_);
return v___x_3190_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3191_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__5);
v___x_3192_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2);
v___x_3193_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3192_);
lean_ctor_set(v___x_3193_, 1, v___x_3192_);
lean_ctor_set(v___x_3193_, 2, v___x_3192_);
lean_ctor_set(v___x_3193_, 3, v___x_3191_);
return v___x_3193_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3194_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__6);
v___x_3195_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__3);
v___x_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3195_);
lean_ctor_set(v___x_3196_, 1, v___x_3194_);
return v___x_3196_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3197_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12);
v___x_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3197_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0(lean_object* v_goal_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3207_ = l_Lean_Meta_Tactic_BVDecide_intToBitVecExt;
v___x_3208_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_3207_, v___y_3205_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3210_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
lean_inc(v_a_3209_);
lean_dec_ref_known(v___x_3208_, 1);
v___x_3210_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_3205_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v_maxSteps_3212_; lean_object* v___x_3213_; uint8_t v___x_3214_; uint8_t v___x_3215_; uint8_t v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
lean_dec_ref_known(v___x_3210_, 1);
v_maxSteps_3212_ = lean_ctor_get(v___y_3200_, 1);
v___x_3213_ = lean_unsigned_to_nat(2u);
v___x_3214_ = 0;
v___x_3215_ = 1;
v___x_3216_ = 0;
v___x_3217_ = lean_box(0);
lean_inc(v_maxSteps_3212_);
v___x_3218_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_3218_, 0, v_maxSteps_3212_);
lean_ctor_set(v___x_3218_, 1, v___x_3213_);
lean_ctor_set(v___x_3218_, 2, v___x_3217_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3, v___x_3214_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 1, v___x_3215_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 2, v___x_3214_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 3, v___x_3215_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 4, v___x_3215_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 5, v___x_3215_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 6, v___x_3216_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 7, v___x_3215_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 8, v___x_3215_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 9, v___x_3214_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 10, v___x_3214_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 11, v___x_3214_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 12, v___x_3215_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 13, v___x_3214_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 14, v___x_3214_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 15, v___x_3214_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 16, v___x_3215_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 17, v___x_3215_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 18, v___x_3214_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 19, v___x_3215_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 20, v___x_3215_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 21, v___x_3215_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 22, v___x_3215_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 23, v___x_3215_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 24, v___x_3215_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 25, v___x_3215_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 26, v___x_3214_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 27, v___x_3214_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 28, v___x_3215_);
v___x_3219_ = lean_unsigned_to_nat(1u);
v___x_3220_ = lean_mk_empty_array_with_capacity(v___x_3219_);
v___x_3221_ = lean_array_push(v___x_3220_, v_a_3209_);
v___x_3222_ = l_Lean_Options_empty;
v___x_3223_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_3218_, v___x_3221_, v_a_3211_, v___x_3222_, v___y_3202_, v___y_3204_, v___y_3205_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v___x_3225_; 
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_a_3224_);
lean_dec_ref_known(v___x_3223_, 1);
lean_inc(v_goal_3199_);
v___x_3225_ = l_Lean_MVarId_getNondepPropHyps(v_goal_3199_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_a_3226_);
lean_dec_ref_known(v___x_3225_, 1);
v___x_3227_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__0));
v___x_3228_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__7);
v___x_3229_ = l_Lean_Meta_simpGoal(v_goal_3199_, v_a_3224_, v___x_3227_, v___x_3217_, v___x_3215_, v_a_3226_, v___x_3228_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3267_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3232_ = v___x_3229_;
v_isShared_3233_ = v_isSharedCheck_3267_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3229_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3267_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v_fst_3234_; 
v_fst_3234_ = lean_ctor_get(v_a_3230_, 0);
lean_inc(v_fst_3234_);
lean_dec(v_a_3230_);
if (lean_obj_tag(v_fst_3234_) == 1)
{
lean_object* v_val_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3263_; 
lean_del_object(v___x_3232_);
v_val_3235_ = lean_ctor_get(v_fst_3234_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_fst_3234_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3237_ = v_fst_3234_;
v_isShared_3238_ = v_isSharedCheck_3263_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_val_3235_);
lean_dec(v_fst_3234_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3263_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v_snd_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v_snd_3239_ = lean_ctor_get(v_val_3235_, 1);
lean_inc(v_snd_3239_);
lean_dec(v_val_3235_);
v___x_3240_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__8);
v___x_3241_ = lean_st_mk_ref(v___x_3240_);
v___x_3242_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_handleSize(v_snd_3239_, v___x_3241_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3254_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3245_ = v___x_3242_;
v_isShared_3246_ = v_isSharedCheck_3254_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3242_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3254_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3247_; lean_object* v___x_3249_; 
v___x_3247_ = lean_st_ref_get(v___x_3241_);
lean_dec(v___x_3241_);
lean_dec(v___x_3247_);
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 0, v_a_3243_);
v___x_3249_ = v___x_3237_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3243_);
v___x_3249_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
lean_object* v___x_3251_; 
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 0, v___x_3249_);
v___x_3251_ = v___x_3245_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3249_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec(v___x_3241_);
lean_del_object(v___x_3237_);
v_a_3255_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3242_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3242_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
}
else
{
lean_object* v___x_3265_; 
lean_dec(v_fst_3234_);
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 0, v___x_3217_);
v___x_3265_ = v___x_3232_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3217_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
else
{
lean_object* v_a_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3275_; 
v_a_3268_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3270_ = v___x_3229_;
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_a_3268_);
lean_dec(v___x_3229_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3268_);
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
lean_dec(v_a_3224_);
lean_dec(v_goal_3199_);
v_a_3276_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3278_ = v___x_3225_;
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3225_);
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
lean_dec(v_goal_3199_);
v_a_3284_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3223_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3223_);
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
lean_dec(v_a_3209_);
lean_dec(v_goal_3199_);
v_a_3292_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3294_ = v___x_3210_;
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_a_3292_);
lean_dec(v___x_3210_);
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
lean_dec(v_goal_3199_);
v_a_3300_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3208_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3208_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___boxed(lean_object* v_goal_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0(v_goal_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
return v_res_3316_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
}
#ifdef __cplusplus
}
#endif
