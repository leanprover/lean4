// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.EPR.BitVec
// Imports: public import Lean.Meta.Tactic.BVDecide.EPR.Basic public import Std.Tactic.BVDecide.Syntax import Std.Tactic.BVDecide.EPR.BitVec import Std.Tactic.BVDecide.Normalize.Prop import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.Sym.AbstractS import Lean.Meta.AppBuilder import Init.Data.Range.Polymorphic.Iterators
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Tactic_BVDecide_EPR_BitVec_toBvPredPropDecls;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Tactic_BVDecide_EPR_BitVec_toBvPredBoolDecls;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Std_Tactic_BVDecide_EPR_BitVec_maxToBvPredArity;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
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
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* lean_nat_log2(lean_object*);
lean_object* l_Lean_Meta_mkListLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedQuantifiedFact_default;
lean_object* l_instInhabitedReaderT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_insert(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkIff(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkForallFVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash___boxed(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instDecidableEqSortId___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0_spec__1(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__0___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__1_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__2;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__3;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__4;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__5_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__6 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__6_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__7;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__8 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__8_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__9_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__9 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__9_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofProp"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__3_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__5_value_aux_2),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(189, 0, 62, 153, 37, 253, 54, 88)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__4_value),LEAN_SCALAR_PTR_LITERAL(153, 71, 30, 209, 57, 12, 129, 48)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "eq_ofProp_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__3_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__8_value_aux_2),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(189, 0, 62, 153, 37, 253, 54, 88)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__7_value),LEAN_SCALAR_PTR_LITERAL(156, 23, 81, 111, 11, 180, 107, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "EPR"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toBvAux"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__3_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__13_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__10_value),LEAN_SCALAR_PTR_LITERAL(194, 239, 89, 128, 83, 215, 9, 208)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__13_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__13_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__11_value),LEAN_SCALAR_PTR_LITERAL(169, 219, 99, 232, 185, 85, 134, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__13_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__12_value),LEAN_SCALAR_PTR_LITERAL(169, 44, 27, 80, 162, 73, 229, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__11_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__15;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "eq_eq_toBvAux_eq_of_mem"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__3_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__10_value),LEAN_SCALAR_PTR_LITERAL(194, 239, 89, 128, 83, 215, 9, 208)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__17_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__17_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__11_value),LEAN_SCALAR_PTR_LITERAL(169, 219, 99, 232, 185, 85, 134, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__17_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__16_value),LEAN_SCALAR_PTR_LITERAL(157, 224, 42, 173, 68, 188, 168, 108)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "propext"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__18_value),LEAN_SCALAR_PTR_LITERAL(53, 150, 49, 30, 125, 3, 39, 172)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__19_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__20;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eq_iff_iff"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__21_value),LEAN_SCALAR_PTR_LITERAL(31, 202, 150, 50, 184, 133, 187, 239)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__22_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__23;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_withVarMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_withVarMap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_withVarMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_withVarMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp_takeSimpCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp_takeSimpCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp_takeSimpCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp_takeSimpCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateGround(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateGround___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Simplifying "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " made no progress"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Membership"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mem"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__4_value),LEAN_SCALAR_PTR_LITERAL(205, 217, 109, 94, 255, 55, 82, 109)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(224, 90, 126, 237, 128, 148, 153, 69)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__6_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeNone___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mpr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__8_value),LEAN_SCALAR_PTR_LITERAL(146, 109, 21, 40, 70, 113, 251, 6)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__10;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__11;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "mem_iff_toBvAux_mem_map_toBvAux"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__3_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__10_value),LEAN_SCALAR_PTR_LITERAL(194, 239, 89, 128, 83, 215, 9, 208)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__14_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__14_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__11_value),LEAN_SCALAR_PTR_LITERAL(169, 219, 99, 232, 185, 85, 134, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__14_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__13_value),LEAN_SCALAR_PTR_LITERAL(34, 44, 254, 195, 246, 55, 44, 27)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mem_map_nil"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__3_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__16_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__10_value),LEAN_SCALAR_PTR_LITERAL(194, 239, 89, 128, 83, 215, 9, 208)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__16_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__16_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__11_value),LEAN_SCALAR_PTR_LITERAL(169, 219, 99, 232, 185, 85, 134, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__16_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__15_value),LEAN_SCALAR_PTR_LITERAL(216, 117, 112, 88, 165, 190, 156, 27)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "mem_map_cons_cons"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__3_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__18_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__10_value),LEAN_SCALAR_PTR_LITERAL(194, 239, 89, 128, 83, 215, 9, 208)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__18_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__18_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__11_value),LEAN_SCALAR_PTR_LITERAL(169, 219, 99, 232, 185, 85, 134, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__18_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__17_value),LEAN_SCALAR_PTR_LITERAL(63, 229, 18, 224, 74, 124, 189, 77)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "mem_map_singleton"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__3_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__20_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__10_value),LEAN_SCALAR_PTR_LITERAL(194, 239, 89, 128, 83, 215, 9, 208)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__20_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__20_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__11_value),LEAN_SCALAR_PTR_LITERAL(169, 219, 99, 232, 185, 85, 134, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__20_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__19_value),LEAN_SCALAR_PTR_LITERAL(238, 135, 121, 52, 198, 41, 231, 24)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__1_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__3___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__11(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14_spec__15___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14_spec__15___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14_spec__15___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Meta.Tactic.BVDecide.EPR.BitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 98, .m_capacity = 98, .m_length = 97, .m_data = "_private.Lean.Meta.Tactic.BVDecide.EPR.BitVec.0.Lean.Meta.Tactic.BVDecide.EPR.translateQuantified"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "assertion violation: args.size == hyp.boundSorts.size\n    "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__3;
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___boxed__const__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__1_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14_spec__15(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__0 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__0_value;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "EPR predicates should not have arity 0"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__1 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__1_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__2;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "EPR predicates with more than "};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__3 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__3_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__4;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__5;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__6;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__7;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__8;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = " arguments are not supported yet: "};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__9 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__9_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__10;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__11;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__1___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "toBvAux_ne_of_toBvAux_lt"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__2___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__2___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "toBvAux_le_ofNat_of_getElem_eq"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__2___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__2___boxed(lean_object**);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "eagerReduce"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(238, 243, 67, 12, 220, 84, 120, 222)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "mem_of_getElem"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(82, 30, 238, 95, 18, 206, 11, 137)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "toBvAux_lt_ofNat_length_of_mem"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__6_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__3_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__10_value),LEAN_SCALAR_PTR_LITERAL(194, 239, 89, 128, 83, 215, 9, 208)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__7_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__7_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__11_value),LEAN_SCALAR_PTR_LITERAL(169, 219, 99, 232, 185, 85, 134, 115)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__7_value_aux_4),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(57, 217, 250, 121, 113, 23, 57, 247)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___boxed(lean_object**);
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "length"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__0 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__0_value;
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__1_value_aux_0),((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 95, 29, 103, 198, 8, 79, 225)}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__1 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__1_value;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "toSortAux"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__2 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__2_value;
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__3_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__10_value),LEAN_SCALAR_PTR_LITERAL(194, 239, 89, 128, 83, 215, 9, 208)}};
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__11_value),LEAN_SCALAR_PTR_LITERAL(169, 219, 99, 232, 185, 85, 134, 115)}};
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__3_value_aux_4),((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 184, 98, 131, 154, 113, 52, 106)}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__3 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec___lam__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default___closed__2, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default___closed__2);
v___x_8_ = lean_unsigned_to_nat(0u);
v___x_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
lean_ctor_set(v___x_9_, 1, v___x_7_);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default___closed__3, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default___closed__3);
return v___x_10_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default;
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0_spec__0___redArg(lean_object* v_a_12_, lean_object* v_x_13_){
_start:
{
if (lean_obj_tag(v_x_13_) == 0)
{
lean_object* v___x_14_; 
v___x_14_ = lean_box(0);
return v___x_14_;
}
else
{
lean_object* v_key_15_; lean_object* v_value_16_; lean_object* v_tail_17_; uint8_t v___x_18_; 
v_key_15_ = lean_ctor_get(v_x_13_, 0);
v_value_16_ = lean_ctor_get(v_x_13_, 1);
v_tail_17_ = lean_ctor_get(v_x_13_, 2);
v___x_18_ = lean_expr_eqv(v_key_15_, v_a_12_);
if (v___x_18_ == 0)
{
v_x_13_ = v_tail_17_;
goto _start;
}
else
{
lean_object* v___x_20_; 
lean_inc(v_value_16_);
v___x_20_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_20_, 0, v_value_16_);
return v___x_20_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_21_, lean_object* v_x_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0_spec__0___redArg(v_a_21_, v_x_22_);
lean_dec(v_x_22_);
lean_dec_ref(v_a_21_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0___redArg(lean_object* v_m_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_buckets_26_; lean_object* v___x_27_; uint64_t v___x_28_; uint64_t v___x_29_; uint64_t v___x_30_; uint64_t v_fold_31_; uint64_t v___x_32_; uint64_t v___x_33_; uint64_t v___x_34_; size_t v___x_35_; size_t v___x_36_; size_t v___x_37_; size_t v___x_38_; size_t v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v_buckets_26_ = lean_ctor_get(v_m_24_, 1);
v___x_27_ = lean_array_get_size(v_buckets_26_);
v___x_28_ = l_Lean_Expr_hash(v_a_25_);
v___x_29_ = 32ULL;
v___x_30_ = lean_uint64_shift_right(v___x_28_, v___x_29_);
v_fold_31_ = lean_uint64_xor(v___x_28_, v___x_30_);
v___x_32_ = 16ULL;
v___x_33_ = lean_uint64_shift_right(v_fold_31_, v___x_32_);
v___x_34_ = lean_uint64_xor(v_fold_31_, v___x_33_);
v___x_35_ = lean_uint64_to_usize(v___x_34_);
v___x_36_ = lean_usize_of_nat(v___x_27_);
v___x_37_ = ((size_t)1ULL);
v___x_38_ = lean_usize_sub(v___x_36_, v___x_37_);
v___x_39_ = lean_usize_land(v___x_35_, v___x_38_);
v___x_40_ = lean_array_uget_borrowed(v_buckets_26_, v___x_39_);
v___x_41_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0_spec__0___redArg(v_a_25_, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0___redArg___boxed(lean_object* v_m_42_, lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0___redArg(v_m_42_, v_a_43_);
lean_dec_ref(v_a_43_);
lean_dec_ref(v_m_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f(lean_object* v_ctx_45_, lean_object* v_e_46_){
_start:
{
lean_object* v_sortMap_47_; lean_object* v_varMap_48_; lean_object* v___x_49_; 
v_sortMap_47_ = lean_ctor_get(v_ctx_45_, 2);
v_varMap_48_ = lean_ctor_get(v_ctx_45_, 3);
v___x_49_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0___redArg(v_sortMap_47_, v_e_46_);
if (lean_obj_tag(v___x_49_) == 1)
{
return v___x_49_;
}
else
{
lean_object* v___x_50_; 
lean_dec(v___x_49_);
v___x_50_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0___redArg(v_varMap_48_, v_e_46_);
if (lean_obj_tag(v___x_50_) == 0)
{
lean_object* v___x_51_; 
v___x_51_ = lean_box(0);
return v___x_51_;
}
else
{
lean_object* v_val_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_60_; 
v_val_52_ = lean_ctor_get(v___x_50_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_60_ == 0)
{
v___x_54_ = v___x_50_;
v_isShared_55_ = v_isSharedCheck_60_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_val_52_);
lean_dec(v___x_50_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_60_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v_sort_56_; lean_object* v___x_58_; 
v_sort_56_ = lean_ctor_get(v_val_52_, 0);
lean_inc(v_sort_56_);
lean_dec(v_val_52_);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v_sort_56_);
v___x_58_ = v___x_54_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_sort_56_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f___boxed(lean_object* v_ctx_61_, lean_object* v_e_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f(v_ctx_61_, v_e_62_);
lean_dec_ref(v_e_62_);
lean_dec_ref(v_ctx_61_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0(lean_object* v_00_u03b2_64_, lean_object* v_m_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0___redArg(v_m_65_, v_a_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0___boxed(lean_object* v_00_u03b2_68_, lean_object* v_m_69_, lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0(v_00_u03b2_68_, v_m_69_, v_a_70_);
lean_dec_ref(v_a_70_);
lean_dec_ref(v_m_69_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0_spec__0(lean_object* v_00_u03b2_72_, lean_object* v_a_73_, lean_object* v_x_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0_spec__0___redArg(v_a_73_, v_x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_76_, lean_object* v_a_77_, lean_object* v_x_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0_spec__0(v_00_u03b2_76_, v_a_77_, v_x_78_);
lean_dec(v_x_78_);
lean_dec_ref(v_a_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0_spec__1(lean_object* v_msg_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default;
v___x_82_ = lean_panic_fn_borrowed(v___x_81_, v_msg_80_);
return v___x_82_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_86_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0___closed__2));
v___x_87_ = lean_unsigned_to_nat(11u);
v___x_88_ = lean_unsigned_to_nat(163u);
v___x_89_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0___closed__1));
v___x_90_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0___closed__0));
v___x_91_ = l_mkPanicMessageWithDecl(v___x_90_, v___x_89_, v___x_88_, v___x_87_, v___x_86_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0(lean_object* v_a_92_, lean_object* v_x_93_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0___closed__3);
v___x_95_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0_spec__1(v___x_94_);
return v___x_95_;
}
else
{
lean_object* v_key_96_; lean_object* v_value_97_; lean_object* v_tail_98_; uint8_t v___x_99_; 
v_key_96_ = lean_ctor_get(v_x_93_, 0);
v_value_97_ = lean_ctor_get(v_x_93_, 1);
v_tail_98_ = lean_ctor_get(v_x_93_, 2);
v___x_99_ = lean_nat_dec_eq(v_key_96_, v_a_92_);
if (v___x_99_ == 0)
{
v_x_93_ = v_tail_98_;
goto _start;
}
else
{
lean_inc(v_value_97_);
return v_value_97_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0___boxed(lean_object* v_a_101_, lean_object* v_x_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0(v_a_101_, v_x_102_);
lean_dec(v_x_102_);
lean_dec(v_a_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0(lean_object* v_m_104_, lean_object* v_a_105_){
_start:
{
lean_object* v_buckets_106_; lean_object* v___x_107_; uint64_t v___x_108_; uint64_t v___x_109_; uint64_t v___x_110_; uint64_t v_fold_111_; uint64_t v___x_112_; uint64_t v___x_113_; uint64_t v___x_114_; size_t v___x_115_; size_t v___x_116_; size_t v___x_117_; size_t v___x_118_; size_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_buckets_106_ = lean_ctor_get(v_m_104_, 1);
v___x_107_ = lean_array_get_size(v_buckets_106_);
v___x_108_ = l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash(v_a_105_);
v___x_109_ = 32ULL;
v___x_110_ = lean_uint64_shift_right(v___x_108_, v___x_109_);
v_fold_111_ = lean_uint64_xor(v___x_108_, v___x_110_);
v___x_112_ = 16ULL;
v___x_113_ = lean_uint64_shift_right(v_fold_111_, v___x_112_);
v___x_114_ = lean_uint64_xor(v_fold_111_, v___x_113_);
v___x_115_ = lean_uint64_to_usize(v___x_114_);
v___x_116_ = lean_usize_of_nat(v___x_107_);
v___x_117_ = ((size_t)1ULL);
v___x_118_ = lean_usize_sub(v___x_116_, v___x_117_);
v___x_119_ = lean_usize_land(v___x_115_, v___x_118_);
v___x_120_ = lean_array_uget_borrowed(v_buckets_106_, v___x_119_);
v___x_121_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0_spec__0(v_a_105_, v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0___boxed(lean_object* v_m_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0(v_m_122_, v_a_123_);
lean_dec(v_a_123_);
lean_dec_ref(v_m_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f(lean_object* v_ctx_125_, lean_object* v_e_126_){
_start:
{
lean_object* v_sortInfo_127_; lean_object* v_sortMap_128_; lean_object* v_varMap_129_; lean_object* v___x_130_; 
v_sortInfo_127_ = lean_ctor_get(v_ctx_125_, 1);
v_sortMap_128_ = lean_ctor_get(v_ctx_125_, 2);
v_varMap_129_ = lean_ctor_get(v_ctx_125_, 3);
v___x_130_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0___redArg(v_varMap_129_, v_e_126_);
if (lean_obj_tag(v___x_130_) == 1)
{
lean_object* v_val_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_139_; 
v_val_131_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_139_ == 0)
{
v___x_133_ = v___x_130_;
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_val_131_);
lean_dec(v___x_130_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v_memElemsProof_135_; lean_object* v___x_137_; 
v_memElemsProof_135_ = lean_ctor_get(v_val_131_, 1);
lean_inc_ref(v_memElemsProof_135_);
lean_dec(v_val_131_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v_memElemsProof_135_);
v___x_137_ = v___x_133_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_memElemsProof_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
else
{
lean_object* v___x_140_; 
lean_dec(v___x_130_);
v___x_140_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0___redArg(v_sortMap_128_, v_e_126_);
if (lean_obj_tag(v___x_140_) == 1)
{
lean_object* v_val_141_; lean_object* v___x_142_; lean_object* v_elemListMemProofs_143_; lean_object* v___x_144_; 
v_val_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_val_141_);
lean_dec_ref_known(v___x_140_, 1);
v___x_142_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0(v_sortInfo_127_, v_val_141_);
lean_dec(v_val_141_);
v_elemListMemProofs_143_ = lean_ctor_get(v___x_142_, 6);
lean_inc_ref(v_elemListMemProofs_143_);
lean_dec_ref(v___x_142_);
v___x_144_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0___redArg(v_elemListMemProofs_143_, v_e_126_);
lean_dec_ref(v_elemListMemProofs_143_);
return v___x_144_;
}
else
{
lean_object* v___x_145_; 
lean_dec(v___x_140_);
v___x_145_ = lean_box(0);
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f___boxed(lean_object* v_ctx_146_, lean_object* v_e_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f(v_ctx_146_, v_e_147_);
lean_dec_ref(v_e_147_);
lean_dec_ref(v_ctx_146_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__0___redArg(lean_object* v_ctx_149_, uint8_t v___x_150_, lean_object* v_as_151_, size_t v_sz_152_, size_t v_i_153_, lean_object* v_b_154_){
_start:
{
uint8_t v___x_156_; 
v___x_156_ = lean_usize_dec_lt(v_i_153_, v_sz_152_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; 
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v_b_154_);
return v___x_157_;
}
else
{
lean_object* v_snd_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_237_; 
v_snd_158_ = lean_ctor_get(v_b_154_, 1);
v_isSharedCheck_237_ = !lean_is_exclusive(v_b_154_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; 
v_unused_238_ = lean_ctor_get(v_b_154_, 0);
lean_dec(v_unused_238_);
v___x_160_ = v_b_154_;
v_isShared_161_ = v_isSharedCheck_237_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_snd_158_);
lean_dec(v_b_154_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_237_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v_snd_162_; lean_object* v_snd_163_; lean_object* v_fst_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_235_; 
v_snd_162_ = lean_ctor_get(v_snd_158_, 1);
lean_inc(v_snd_162_);
v_snd_163_ = lean_ctor_get(v_snd_162_, 1);
lean_inc(v_snd_163_);
v_fst_164_ = lean_ctor_get(v_snd_158_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v_snd_158_);
if (v_isSharedCheck_235_ == 0)
{
lean_object* v_unused_236_; 
v_unused_236_ = lean_ctor_get(v_snd_158_, 1);
lean_dec(v_unused_236_);
v___x_166_ = v_snd_158_;
v_isShared_167_ = v_isSharedCheck_235_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_fst_164_);
lean_dec(v_snd_158_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_235_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v_fst_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_233_; 
v_fst_168_ = lean_ctor_get(v_snd_162_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v_snd_162_);
if (v_isSharedCheck_233_ == 0)
{
lean_object* v_unused_234_; 
v_unused_234_ = lean_ctor_get(v_snd_162_, 1);
lean_dec(v_unused_234_);
v___x_170_ = v_snd_162_;
v_isShared_171_ = v_isSharedCheck_233_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_fst_168_);
lean_dec(v_snd_162_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_233_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v_array_172_; lean_object* v_start_173_; lean_object* v_stop_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v_array_172_ = lean_ctor_get(v_snd_163_, 0);
v_start_173_ = lean_ctor_get(v_snd_163_, 1);
v_stop_174_ = lean_ctor_get(v_snd_163_, 2);
v___x_175_ = lean_box(0);
v___x_176_ = lean_nat_dec_lt(v_start_173_, v_stop_174_);
if (v___x_176_ == 0)
{
lean_object* v___x_178_; 
if (v_isShared_171_ == 0)
{
v___x_178_ = v___x_170_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_fst_168_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_snd_163_);
v___x_178_ = v_reuseFailAlloc_186_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_180_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_178_);
v___x_180_ = v___x_166_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_fst_164_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v___x_178_);
v___x_180_ = v_reuseFailAlloc_185_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_182_; 
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_180_);
lean_ctor_set(v___x_160_, 0, v___x_175_);
v___x_182_ = v___x_160_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_175_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v___x_180_);
v___x_182_ = v_reuseFailAlloc_184_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_183_; 
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
}
}
else
{
lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_229_; 
lean_inc(v_stop_174_);
lean_inc(v_start_173_);
lean_inc_ref(v_array_172_);
v_isSharedCheck_229_ = !lean_is_exclusive(v_snd_163_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; lean_object* v_unused_231_; lean_object* v_unused_232_; 
v_unused_230_ = lean_ctor_get(v_snd_163_, 2);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_snd_163_, 1);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v_snd_163_, 0);
lean_dec(v_unused_232_);
v___x_188_ = v_snd_163_;
v_isShared_189_ = v_isSharedCheck_229_;
goto v_resetjp_187_;
}
else
{
lean_dec(v_snd_163_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_229_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v_a_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_195_; 
v_a_190_ = lean_array_uget_borrowed(v_as_151_, v_i_153_);
v___x_191_ = lean_array_fget(v_array_172_, v_start_173_);
v___x_192_ = lean_unsigned_to_nat(1u);
v___x_193_ = lean_nat_add(v_start_173_, v___x_192_);
lean_dec(v_start_173_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 1, v___x_193_);
v___x_195_ = v___x_188_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_array_172_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_stop_174_);
v___x_195_ = v_reuseFailAlloc_228_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_196_; 
v___x_196_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f(v_ctx_149_, v_a_190_);
if (lean_obj_tag(v___x_196_) == 1)
{
lean_object* v_val_197_; lean_object* v_sortInfo_198_; lean_object* v___x_199_; lean_object* v_toBv_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
v_val_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_val_197_);
lean_dec_ref_known(v___x_196_, 1);
v_sortInfo_198_ = lean_ctor_get(v_ctx_149_, 1);
v___x_199_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0(v_sortInfo_198_, v___x_191_);
lean_dec(v___x_191_);
v_toBv_200_ = lean_ctor_get(v___x_199_, 2);
lean_inc_ref(v_toBv_200_);
lean_dec_ref(v___x_199_);
lean_inc_n(v_a_190_, 2);
v___x_201_ = l_Lean_Expr_app___override(v_toBv_200_, v_a_190_);
v___x_202_ = l_Lean_Expr_app___override(v_fst_164_, v___x_201_);
v___x_203_ = l_Lean_mkAppB(v_fst_168_, v_a_190_, v_val_197_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 1, v___x_195_);
lean_ctor_set(v___x_170_, 0, v___x_203_);
v___x_205_ = v___x_170_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___x_195_);
v___x_205_ = v_reuseFailAlloc_215_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_207_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_205_);
lean_ctor_set(v___x_166_, 0, v___x_202_);
v___x_207_ = v___x_166_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v___x_205_);
v___x_207_ = v_reuseFailAlloc_214_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_209_; 
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_207_);
lean_ctor_set(v___x_160_, 0, v___x_175_);
v___x_209_ = v___x_160_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_175_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v___x_207_);
v___x_209_ = v_reuseFailAlloc_213_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
size_t v___x_210_; size_t v___x_211_; 
v___x_210_ = ((size_t)1ULL);
v___x_211_ = lean_usize_add(v_i_153_, v___x_210_);
v_i_153_ = v___x_211_;
v_b_154_ = v___x_209_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_219_; 
lean_dec(v___x_196_);
lean_dec(v___x_191_);
v___x_216_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_216_, 0, v___x_150_);
lean_ctor_set_uint8(v___x_216_, 1, v___x_150_);
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 1, v___x_195_);
v___x_219_ = v___x_170_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_fst_168_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v___x_195_);
v___x_219_ = v_reuseFailAlloc_227_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v___x_221_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_219_);
v___x_221_ = v___x_166_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_fst_164_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v___x_219_);
v___x_221_ = v_reuseFailAlloc_226_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_223_; 
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_221_);
lean_ctor_set(v___x_160_, 0, v___x_217_);
v___x_223_ = v___x_160_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v___x_221_);
v___x_223_ = v_reuseFailAlloc_225_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_224_; 
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__0___redArg___boxed(lean_object* v_ctx_239_, lean_object* v___x_240_, lean_object* v_as_241_, lean_object* v_sz_242_, lean_object* v_i_243_, lean_object* v_b_244_, lean_object* v___y_245_){
_start:
{
uint8_t v___x_22261__boxed_246_; size_t v_sz_boxed_247_; size_t v_i_boxed_248_; lean_object* v_res_249_; 
v___x_22261__boxed_246_ = lean_unbox(v___x_240_);
v_sz_boxed_247_ = lean_unbox_usize(v_sz_242_);
lean_dec(v_sz_242_);
v_i_boxed_248_ = lean_unbox_usize(v_i_243_);
lean_dec(v_i_243_);
v_res_249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__0___redArg(v_ctx_239_, v___x_22261__boxed_246_, v_as_241_, v_sz_boxed_247_, v_i_boxed_248_, v_b_244_);
lean_dec_ref(v_as_241_);
lean_dec_ref(v_ctx_239_);
return v_res_249_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__2(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = l_Lean_Level_ofNat(v___x_253_);
return v___x_254_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__3(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_255_ = lean_box(0);
v___x_256_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__2, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__2);
v___x_257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v___x_255_);
return v___x_257_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__4(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_258_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__3);
v___x_259_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__1));
v___x_260_ = l_Lean_mkConst(v___x_259_, v___x_258_);
return v___x_260_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__7(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = lean_box(0);
v___x_265_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__6));
v___x_266_ = l_Lean_mkConst(v___x_265_, v___x_264_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__10(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_box(0);
v___x_272_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__9));
v___x_273_ = l_Lean_mkConst(v___x_272_, v___x_271_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1(lean_object* v_ctx_274_, uint8_t v___x_275_, lean_object* v_x_276_, lean_object* v_x_277_, lean_object* v_x_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
if (lean_obj_tag(v_x_276_) == 5)
{
lean_object* v_fn_289_; lean_object* v_arg_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_fn_289_ = lean_ctor_get(v_x_276_, 0);
lean_inc_ref(v_fn_289_);
v_arg_290_ = lean_ctor_get(v_x_276_, 1);
lean_inc_ref(v_arg_290_);
lean_dec_ref_known(v_x_276_, 2);
v___x_291_ = lean_array_set(v_x_277_, v_x_278_, v_arg_290_);
v___x_292_ = lean_unsigned_to_nat(1u);
v___x_293_ = lean_nat_sub(v_x_278_, v___x_292_);
lean_dec(v_x_278_);
v_x_276_ = v_fn_289_;
v_x_277_ = v___x_291_;
v_x_278_ = v___x_293_;
goto _start;
}
else
{
lean_object* v_predInfo_295_; lean_object* v___x_296_; 
lean_dec(v_x_278_);
v_predInfo_295_ = lean_ctor_get(v_ctx_274_, 0);
v___x_296_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f_spec__0___redArg(v_predInfo_295_, v_x_276_);
lean_dec_ref(v_x_276_);
if (lean_obj_tag(v___x_296_) == 1)
{
lean_object* v_val_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_367_; 
v_val_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_367_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_367_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_val_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_367_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v_toPredInfo_301_; lean_object* v_bvPred_302_; lean_object* v_eqThm_303_; lean_object* v_argumentSorts_304_; uint8_t v_encoding_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_toPredInfo_301_ = lean_ctor_get(v_val_297_, 0);
lean_inc_ref(v_toPredInfo_301_);
v_bvPred_302_ = lean_ctor_get(v_val_297_, 1);
lean_inc_ref(v_bvPred_302_);
v_eqThm_303_ = lean_ctor_get(v_val_297_, 2);
lean_inc_ref(v_eqThm_303_);
lean_dec(v_val_297_);
v_argumentSorts_304_ = lean_ctor_get(v_toPredInfo_301_, 0);
lean_inc_ref(v_argumentSorts_304_);
v_encoding_305_ = lean_ctor_get_uint8(v_toPredInfo_301_, sizeof(void*)*1);
lean_dec_ref(v_toPredInfo_301_);
v___x_306_ = lean_array_get_size(v_x_277_);
v___x_307_ = lean_array_get_size(v_argumentSorts_304_);
v___x_308_ = lean_nat_dec_eq(v___x_306_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_311_; 
lean_dec_ref(v_argumentSorts_304_);
lean_dec_ref(v_eqThm_303_);
lean_dec_ref(v_bvPred_302_);
lean_dec_ref(v_x_277_);
v___x_309_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_309_, 0, v___x_275_);
lean_ctor_set_uint8(v___x_309_, 1, v___x_275_);
if (v_isShared_300_ == 0)
{
lean_ctor_set_tag(v___x_299_, 0);
lean_ctor_set(v___x_299_, 0, v___x_309_);
v___x_311_ = v___x_299_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; size_t v_sz_319_; size_t v___x_320_; lean_object* v___x_321_; 
lean_del_object(v___x_299_);
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = l_Array_toSubarray___redArg(v_argumentSorts_304_, v___x_313_, v___x_307_);
v___x_315_ = lean_box(0);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v_eqThm_303_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v_bvPred_302_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_315_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v_sz_319_ = lean_array_size(v_x_277_);
v___x_320_ = ((size_t)0ULL);
v___x_321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__0___redArg(v_ctx_274_, v___x_275_, v_x_277_, v_sz_319_, v___x_320_, v___x_318_);
lean_dec_ref(v_x_277_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_358_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_358_ == 0)
{
v___x_324_ = v___x_321_;
v_isShared_325_ = v_isSharedCheck_358_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_321_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_358_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v_fst_326_; 
v_fst_326_ = lean_ctor_get(v_a_322_, 0);
if (lean_obj_tag(v_fst_326_) == 0)
{
lean_object* v_snd_327_; lean_object* v_snd_328_; lean_object* v_fst_329_; lean_object* v_fst_330_; lean_object* v_resExpr_332_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_snd_327_ = lean_ctor_get(v_a_322_, 1);
lean_inc(v_snd_327_);
lean_dec(v_a_322_);
v_snd_328_ = lean_ctor_get(v_snd_327_, 1);
lean_inc(v_snd_328_);
v_fst_329_ = lean_ctor_get(v_snd_327_, 0);
lean_inc(v_fst_329_);
lean_dec(v_snd_327_);
v_fst_330_ = lean_ctor_get(v_snd_328_, 0);
lean_inc(v_fst_330_);
lean_dec(v_snd_328_);
v___x_337_ = lean_box(v_encoding_305_);
v___x_338_ = lean_obj_tag_nat(v___x_337_);
lean_dec(v___x_337_);
v___x_339_ = lean_nat_dec_eq(v___x_338_, v___x_313_);
if (v___x_339_ == 0)
{
v_resExpr_332_ = v_fst_329_;
goto v___jp_331_;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_340_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__4, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__4);
v___x_341_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__7, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__7);
v___x_342_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__10, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__10);
v___x_343_ = l_Lean_mkApp3(v___x_340_, v___x_341_, v_fst_329_, v___x_342_);
v___x_344_ = l_Lean_Meta_Sym_shareCommonInc(v___x_343_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_344_, 1);
v_resExpr_332_ = v_a_345_;
goto v___jp_331_;
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec(v_fst_330_);
lean_del_object(v___x_324_);
v_a_346_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_344_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_344_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
v___jp_331_:
{
lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_333_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_333_, 0, v_resExpr_332_);
lean_ctor_set(v___x_333_, 1, v_fst_330_);
lean_ctor_set_uint8(v___x_333_, sizeof(void*)*2, v___x_308_);
lean_ctor_set_uint8(v___x_333_, sizeof(void*)*2 + 1, v___x_275_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v___x_333_);
v___x_335_ = v___x_324_;
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
else
{
lean_object* v_val_354_; lean_object* v___x_356_; 
lean_inc_ref(v_fst_326_);
lean_dec(v_a_322_);
v_val_354_ = lean_ctor_get(v_fst_326_, 0);
lean_inc(v_val_354_);
lean_dec_ref_known(v_fst_326_, 1);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v_val_354_);
v___x_356_ = v___x_324_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_val_354_);
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
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
v_a_359_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_321_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_321_);
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
}
}
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; 
lean_dec(v___x_296_);
lean_dec_ref(v_x_277_);
v___x_368_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_368_, 0, v___x_275_);
lean_ctor_set_uint8(v___x_368_, 1, v___x_275_);
v___x_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
return v___x_369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___boxed(lean_object* v_ctx_370_, lean_object* v___x_371_, lean_object* v_x_372_, lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
uint8_t v___x_22459__boxed_385_; lean_object* v_res_386_; 
v___x_22459__boxed_385_ = lean_unbox(v___x_371_);
v_res_386_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1(v_ctx_370_, v___x_22459__boxed_385_, v_x_372_, v_x_373_, v_x_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v_ctx_370_);
return v_res_386_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__0(void){
_start:
{
lean_object* v___x_387_; lean_object* v_dummy_388_; 
v___x_387_ = lean_box(0);
v_dummy_388_ = l_Lean_Expr_sort___override(v___x_387_);
return v_dummy_388_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__6(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_399_ = lean_box(0);
v___x_400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__5));
v___x_401_ = l_Lean_mkConst(v___x_400_, v___x_399_);
return v___x_401_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__9(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = lean_box(0);
v___x_410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__8));
v___x_411_ = l_Lean_mkConst(v___x_410_, v___x_409_);
return v___x_411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__15(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_box(0);
v___x_425_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__14));
v___x_426_ = l_Lean_mkConst(v___x_425_, v___x_424_);
return v___x_426_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__20(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = lean_box(0);
v___x_439_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__19));
v___x_440_ = l_Lean_mkConst(v___x_439_, v___x_438_);
return v___x_440_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__23(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_box(0);
v___x_445_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__22));
v___x_446_ = l_Lean_mkConst(v___x_445_, v___x_444_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom(lean_object* v_ctx_447_, lean_object* v_e_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___x_523_; 
lean_inc_ref(v_e_448_);
v___x_523_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_448_, v_a_455_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_637_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_637_ == 0)
{
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_637_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_637_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_528_ = l_Lean_Expr_cleanupAnnotations(v_a_524_);
lean_dec(v_a_524_);
v___x_529_ = l_Lean_Expr_isApp(v___x_528_);
if (v___x_529_ == 0)
{
lean_dec_ref(v___x_528_);
lean_del_object(v___x_526_);
v___y_460_ = v_a_449_;
v___y_461_ = v_a_450_;
v___y_462_ = v_a_451_;
v___y_463_ = v_a_452_;
v___y_464_ = v_a_453_;
v___y_465_ = v_a_454_;
v___y_466_ = v_a_455_;
v___y_467_ = v_a_456_;
v___y_468_ = v_a_457_;
goto v___jp_459_;
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_530_ = l_Lean_Expr_appFnCleanup___redArg(v___x_528_);
v___x_531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__5));
v___x_532_ = l_Lean_Expr_isConstOf(v___x_530_, v___x_531_);
if (v___x_532_ == 0)
{
uint8_t v___x_533_; 
v___x_533_ = l_Lean_Expr_isApp(v___x_530_);
if (v___x_533_ == 0)
{
lean_dec_ref(v___x_530_);
lean_dec_ref(v___x_528_);
lean_del_object(v___x_526_);
v___y_460_ = v_a_449_;
v___y_461_ = v_a_450_;
v___y_462_ = v_a_451_;
v___y_463_ = v_a_452_;
v___y_464_ = v_a_453_;
v___y_465_ = v_a_454_;
v___y_466_ = v_a_455_;
v___y_467_ = v_a_456_;
v___y_468_ = v_a_457_;
goto v___jp_459_;
}
else
{
lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_534_ = l_Lean_Expr_appFnCleanup___redArg(v___x_530_);
v___x_535_ = l_Lean_Expr_isApp(v___x_534_);
if (v___x_535_ == 0)
{
lean_dec_ref(v___x_534_);
lean_dec_ref(v___x_530_);
lean_dec_ref(v___x_528_);
lean_del_object(v___x_526_);
v___y_460_ = v_a_449_;
v___y_461_ = v_a_450_;
v___y_462_ = v_a_451_;
v___y_463_ = v_a_452_;
v___y_464_ = v_a_453_;
v___y_465_ = v_a_454_;
v___y_466_ = v_a_455_;
v___y_467_ = v_a_456_;
v___y_468_ = v_a_457_;
goto v___jp_459_;
}
else
{
lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_536_ = l_Lean_Expr_appFnCleanup___redArg(v___x_534_);
v___x_537_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__1));
v___x_538_ = l_Lean_Expr_isConstOf(v___x_536_, v___x_537_);
if (v___x_538_ == 0)
{
uint8_t v___x_539_; 
lean_dec_ref(v___x_534_);
lean_dec_ref(v___x_530_);
lean_dec_ref(v___x_528_);
v___x_539_ = l_Lean_Expr_isApp(v___x_536_);
if (v___x_539_ == 0)
{
lean_dec_ref(v___x_536_);
lean_del_object(v___x_526_);
v___y_460_ = v_a_449_;
v___y_461_ = v_a_450_;
v___y_462_ = v_a_451_;
v___y_463_ = v_a_452_;
v___y_464_ = v_a_453_;
v___y_465_ = v_a_454_;
v___y_466_ = v_a_455_;
v___y_467_ = v_a_456_;
v___y_468_ = v_a_457_;
goto v___jp_459_;
}
else
{
lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_540_ = l_Lean_Expr_appFnCleanup___redArg(v___x_536_);
lean_dec_ref(v___x_536_);
v___x_541_ = l_Lean_Expr_isApp(v___x_540_);
if (v___x_541_ == 0)
{
lean_dec_ref(v___x_540_);
lean_del_object(v___x_526_);
v___y_460_ = v_a_449_;
v___y_461_ = v_a_450_;
v___y_462_ = v_a_451_;
v___y_463_ = v_a_452_;
v___y_464_ = v_a_453_;
v___y_465_ = v_a_454_;
v___y_466_ = v_a_455_;
v___y_467_ = v_a_456_;
v___y_468_ = v_a_457_;
goto v___jp_459_;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_542_ = l_Lean_Expr_appFnCleanup___redArg(v___x_540_);
lean_dec_ref(v___x_540_);
v___x_543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__13));
v___x_544_ = l_Lean_Expr_isConstOf(v___x_542_, v___x_543_);
lean_dec_ref(v___x_542_);
if (v___x_544_ == 0)
{
lean_del_object(v___x_526_);
v___y_460_ = v_a_449_;
v___y_461_ = v_a_450_;
v___y_462_ = v_a_451_;
v___y_463_ = v_a_452_;
v___y_464_ = v_a_453_;
v___y_465_ = v_a_454_;
v___y_466_ = v_a_455_;
v___y_467_ = v_a_456_;
v___y_468_ = v_a_457_;
goto v___jp_459_;
}
else
{
lean_object* v___x_545_; lean_object* v___x_547_; 
lean_dec_ref(v_e_448_);
v___x_545_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_545_, 0, v___x_544_);
lean_ctor_set_uint8(v___x_545_, 1, v___x_538_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_545_);
v___x_547_ = v___x_526_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
else
{
lean_object* v_arg_549_; lean_object* v_arg_550_; lean_object* v_arg_551_; uint8_t v___x_552_; 
lean_dec_ref(v___x_536_);
v_arg_549_ = lean_ctor_get(v___x_528_, 1);
lean_inc_ref(v_arg_549_);
lean_dec_ref(v___x_528_);
v_arg_550_ = lean_ctor_get(v___x_530_, 1);
lean_inc_ref(v_arg_550_);
lean_dec_ref(v___x_530_);
v_arg_551_ = lean_ctor_get(v___x_534_, 1);
lean_inc_ref(v_arg_551_);
lean_dec_ref(v___x_534_);
v___x_552_ = l_Lean_Expr_isProp(v_arg_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; 
lean_dec_ref(v_e_448_);
v___x_553_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getSort_x3f(v_ctx_447_, v_arg_550_);
if (lean_obj_tag(v___x_553_) == 1)
{
lean_object* v_val_554_; lean_object* v___x_555_; 
v_val_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_val_554_);
lean_dec_ref_known(v___x_553_, 1);
v___x_555_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f(v_ctx_447_, v_arg_550_);
if (lean_obj_tag(v___x_555_) == 1)
{
lean_object* v_val_556_; lean_object* v___x_557_; 
v_val_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_val_556_);
lean_dec_ref_known(v___x_555_, 1);
v___x_557_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f(v_ctx_447_, v_arg_549_);
if (lean_obj_tag(v___x_557_) == 1)
{
lean_object* v_val_558_; lean_object* v_sortInfo_559_; lean_object* v___x_560_; lean_object* v_toSortInfo_561_; lean_object* v_width_562_; lean_object* v_toBv_563_; lean_object* v_elemList_564_; lean_object* v_elemListLt_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
lean_del_object(v___x_526_);
v_val_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_val_558_);
lean_dec_ref_known(v___x_557_, 1);
v_sortInfo_559_ = lean_ctor_get(v_ctx_447_, 1);
v___x_560_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0(v_sortInfo_559_, v_val_554_);
lean_dec(v_val_554_);
v_toSortInfo_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc_ref(v_toSortInfo_561_);
v_width_562_ = lean_ctor_get(v___x_560_, 1);
lean_inc(v_width_562_);
v_toBv_563_ = lean_ctor_get(v___x_560_, 2);
lean_inc_ref_n(v_toBv_563_, 2);
v_elemList_564_ = lean_ctor_get(v___x_560_, 4);
lean_inc_ref(v_elemList_564_);
v_elemListLt_565_ = lean_ctor_get(v___x_560_, 5);
lean_inc_ref(v_elemListLt_565_);
lean_dec_ref(v___x_560_);
v___x_566_ = lean_box(0);
v___x_567_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__4, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__4);
v___x_568_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__15, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__15_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__15);
v___x_569_ = l_Lean_mkNatLit(v_width_562_);
lean_inc_ref(v___x_569_);
v___x_570_ = l_Lean_Expr_app___override(v___x_568_, v___x_569_);
lean_inc_ref(v_arg_550_);
v___x_571_ = l_Lean_Expr_app___override(v_toBv_563_, v_arg_550_);
lean_inc_ref(v_arg_549_);
v___x_572_ = l_Lean_Expr_app___override(v_toBv_563_, v_arg_549_);
v___x_573_ = l_Lean_mkApp3(v___x_567_, v___x_570_, v___x_571_, v___x_572_);
v___x_574_ = l_Lean_Meta_Sym_shareCommonInc(v___x_573_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_588_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_588_ == 0)
{
v___x_577_ = v___x_574_;
v_isShared_578_ = v_isSharedCheck_588_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_588_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v_level_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v_level_579_ = lean_ctor_get(v_toSortInfo_561_, 1);
lean_inc(v_level_579_);
lean_dec_ref(v_toSortInfo_561_);
v___x_580_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__17));
v___x_581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_581_, 0, v_level_579_);
lean_ctor_set(v___x_581_, 1, v___x_566_);
v___x_582_ = l_Lean_mkConst(v___x_580_, v___x_581_);
v___x_583_ = l_Lean_mkApp8(v___x_582_, v_arg_551_, v___x_569_, v_elemList_564_, v_elemListLt_565_, v_arg_550_, v_arg_549_, v_val_556_, v_val_558_);
v___x_584_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_584_, 0, v_a_575_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
lean_ctor_set_uint8(v___x_584_, sizeof(void*)*2, v___x_538_);
lean_ctor_set_uint8(v___x_584_, sizeof(void*)*2 + 1, v___x_552_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_584_);
v___x_586_ = v___x_577_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec_ref(v___x_569_);
lean_dec_ref(v_elemListLt_565_);
lean_dec_ref(v_elemList_564_);
lean_dec_ref(v_toSortInfo_561_);
lean_dec(v_val_558_);
lean_dec(v_val_556_);
lean_dec_ref(v_arg_551_);
lean_dec_ref(v_arg_550_);
lean_dec_ref(v_arg_549_);
v_a_589_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_574_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_574_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
else
{
lean_object* v___x_597_; lean_object* v___x_599_; 
lean_dec(v___x_557_);
lean_dec(v_val_556_);
lean_dec(v_val_554_);
lean_dec_ref(v_arg_551_);
lean_dec_ref(v_arg_550_);
lean_dec_ref(v_arg_549_);
v___x_597_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_597_, 0, v___x_552_);
lean_ctor_set_uint8(v___x_597_, 1, v___x_552_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_597_);
v___x_599_ = v___x_526_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_603_; 
lean_dec(v___x_555_);
lean_dec(v_val_554_);
lean_dec_ref(v_arg_551_);
lean_dec_ref(v_arg_550_);
lean_dec_ref(v_arg_549_);
v___x_601_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_601_, 0, v___x_552_);
lean_ctor_set_uint8(v___x_601_, 1, v___x_552_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_601_);
v___x_603_ = v___x_526_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
else
{
lean_object* v___x_605_; lean_object* v___x_607_; 
lean_dec(v___x_553_);
lean_dec_ref(v_arg_551_);
lean_dec_ref(v_arg_550_);
lean_dec_ref(v_arg_549_);
v___x_605_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_605_, 0, v___x_552_);
lean_ctor_set_uint8(v___x_605_, 1, v___x_552_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_605_);
v___x_607_ = v___x_526_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec_ref(v_arg_551_);
lean_del_object(v___x_526_);
lean_inc_ref(v_arg_549_);
lean_inc_ref(v_arg_550_);
v___x_609_ = l_Lean_mkIff(v_arg_550_, v_arg_549_);
v___x_610_ = l_Lean_Meta_Sym_shareCommonInc(v___x_609_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_623_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_623_ == 0)
{
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_623_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_623_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_615_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__20, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__20_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__20);
v___x_616_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__23);
v___x_617_ = l_Lean_mkAppB(v___x_616_, v_arg_550_, v_arg_549_);
lean_inc(v_a_611_);
v___x_618_ = l_Lean_mkApp3(v___x_615_, v_e_448_, v_a_611_, v___x_617_);
v___x_619_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_619_, 0, v_a_611_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*2, v___x_532_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*2 + 1, v___x_532_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_619_);
v___x_621_ = v___x_613_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref(v_arg_550_);
lean_dec_ref(v_arg_549_);
lean_dec_ref(v_e_448_);
v_a_624_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_610_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_610_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
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
uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_635_; 
lean_dec_ref(v___x_530_);
lean_dec_ref(v___x_528_);
lean_dec_ref(v_e_448_);
v___x_632_ = 0;
v___x_633_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_633_, 0, v___x_532_);
lean_ctor_set_uint8(v___x_633_, 1, v___x_632_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_633_);
v___x_635_ = v___x_526_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec_ref(v_e_448_);
v_a_638_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_523_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_523_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
v___jp_459_:
{
uint8_t v___x_469_; 
v___x_469_ = l_Lean_Expr_isFVar(v_e_448_);
if (v___x_469_ == 0)
{
lean_object* v_dummy_470_; lean_object* v_nargs_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_dummy_470_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__0);
v_nargs_471_ = l_Lean_Expr_getAppNumArgs(v_e_448_);
lean_inc(v_nargs_471_);
v___x_472_ = lean_mk_array(v_nargs_471_, v_dummy_470_);
v___x_473_ = lean_unsigned_to_nat(1u);
v___x_474_ = lean_nat_sub(v_nargs_471_, v___x_473_);
lean_dec(v_nargs_471_);
v___x_475_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1(v_ctx_447_, v___x_469_, v_e_448_, v___x_472_, v___x_474_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
return v___x_475_;
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = l_Lean_Expr_fvarId_x21(v_e_448_);
v___x_477_ = l_Lean_FVarId_getType___redArg(v___x_476_, v___y_465_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_514_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_514_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_514_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_514_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
uint8_t v___x_482_; 
v___x_482_ = l_Lean_Expr_isProp(v_a_478_);
lean_dec(v_a_478_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_485_; 
lean_dec_ref(v_e_448_);
v___x_483_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_483_, 0, v___x_482_);
lean_ctor_set_uint8(v___x_483_, 1, v___x_482_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_483_);
v___x_485_ = v___x_480_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
lean_del_object(v___x_480_);
v___x_487_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__4, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__4);
v___x_488_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__7, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__7);
v___x_489_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__6);
lean_inc_ref(v_e_448_);
v___x_490_ = l_Lean_Expr_app___override(v___x_489_, v_e_448_);
v___x_491_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__10, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__10);
v___x_492_ = l_Lean_mkApp3(v___x_487_, v___x_488_, v___x_490_, v___x_491_);
v___x_493_ = l_Lean_Meta_Sym_shareCommonInc(v___x_492_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_505_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_505_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_505_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_505_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_498_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__9);
v___x_499_ = l_Lean_Expr_app___override(v___x_498_, v_e_448_);
v___x_500_ = 0;
v___x_501_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_501_, 0, v_a_494_);
lean_ctor_set(v___x_501_, 1, v___x_499_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*2, v___x_469_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*2 + 1, v___x_500_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_501_);
v___x_503_ = v___x_496_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_dec_ref(v_e_448_);
v_a_506_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_493_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_493_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
lean_dec_ref(v_e_448_);
v_a_515_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_477_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_477_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___boxed(lean_object* v_ctx_646_, lean_object* v_e_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom(v_ctx_646_, v_e_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_ctx_646_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__0(lean_object* v_ctx_659_, uint8_t v___x_660_, lean_object* v_as_661_, size_t v_sz_662_, size_t v_i_663_, lean_object* v_b_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__0___redArg(v_ctx_659_, v___x_660_, v_as_661_, v_sz_662_, v_i_663_, v_b_664_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__0___boxed(lean_object* v_ctx_676_, lean_object* v___x_677_, lean_object* v_as_678_, lean_object* v_sz_679_, lean_object* v_i_680_, lean_object* v_b_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
uint8_t v___x_23246__boxed_692_; size_t v_sz_boxed_693_; size_t v_i_boxed_694_; lean_object* v_res_695_; 
v___x_23246__boxed_692_ = lean_unbox(v___x_677_);
v_sz_boxed_693_ = lean_unbox_usize(v_sz_679_);
lean_dec(v_sz_679_);
v_i_boxed_694_ = lean_unbox_usize(v_i_680_);
lean_dec(v_i_680_);
v_res_695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__0(v_ctx_676_, v___x_23246__boxed_692_, v_as_678_, v_sz_boxed_693_, v_i_boxed_694_, v_b_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v_as_678_);
lean_dec_ref(v_ctx_676_);
return v_res_695_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_696_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__0);
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = lean_box(0);
v___x_700_ = lean_unsigned_to_nat(16u);
v___x_701_ = lean_mk_array(v___x_700_, v___x_699_);
return v___x_701_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_702_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__2);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v___x_702_);
return v___x_704_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__4(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__3);
v___x_706_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__1);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v___x_705_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg(lean_object* v_ctx_708_, lean_object* v_x_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__4);
v___x_718_ = lean_st_mk_ref(v___x_717_);
lean_inc(v_a_715_);
lean_inc_ref(v_a_714_);
lean_inc(v_a_713_);
lean_inc_ref(v_a_712_);
lean_inc(v_a_711_);
lean_inc_ref(v_a_710_);
lean_inc(v___x_718_);
v___x_719_ = lean_apply_9(v_x_709_, v_ctx_708_, v___x_718_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, lean_box(0));
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_728_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_728_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_724_ = lean_st_ref_get(v___x_718_);
lean_dec(v___x_718_);
lean_dec(v___x_724_);
if (v_isShared_723_ == 0)
{
v___x_726_ = v___x_722_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_720_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
else
{
lean_dec(v___x_718_);
return v___x_719_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___boxed(lean_object* v_ctx_729_, lean_object* v_x_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg(v_ctx_729_, v_x_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run(lean_object* v_00_u03b1_739_, lean_object* v_ctx_740_, lean_object* v_x_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg(v_ctx_740_, v_x_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___boxed(lean_object* v_00_u03b1_750_, lean_object* v_ctx_751_, lean_object* v_x_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run(v_00_u03b1_750_, v_ctx_751_, v_x_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_withVarMap___redArg(lean_object* v_varMap_761_, lean_object* v_x_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_predInfo_772_; lean_object* v_sortInfo_773_; lean_object* v_sortMap_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_predInfo_772_ = lean_ctor_get(v_a_763_, 0);
v_sortInfo_773_ = lean_ctor_get(v_a_763_, 1);
v_sortMap_774_ = lean_ctor_get(v_a_763_, 2);
lean_inc_ref(v_sortMap_774_);
lean_inc_ref(v_sortInfo_773_);
lean_inc_ref(v_predInfo_772_);
v___x_775_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_775_, 0, v_predInfo_772_);
lean_ctor_set(v___x_775_, 1, v_sortInfo_773_);
lean_ctor_set(v___x_775_, 2, v_sortMap_774_);
lean_ctor_set(v___x_775_, 3, v_varMap_761_);
lean_inc(v_a_770_);
lean_inc_ref(v_a_769_);
lean_inc(v_a_768_);
lean_inc_ref(v_a_767_);
lean_inc(v_a_766_);
lean_inc_ref(v_a_765_);
lean_inc(v_a_764_);
v___x_776_ = lean_apply_9(v_x_762_, v___x_775_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, lean_box(0));
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_withVarMap___redArg___boxed(lean_object* v_varMap_777_, lean_object* v_x_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_withVarMap___redArg(v_varMap_777_, v_x_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_withVarMap(lean_object* v_00_u03b1_789_, lean_object* v_varMap_790_, lean_object* v_x_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v_predInfo_801_; lean_object* v_sortInfo_802_; lean_object* v_sortMap_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_predInfo_801_ = lean_ctor_get(v_a_792_, 0);
v_sortInfo_802_ = lean_ctor_get(v_a_792_, 1);
v_sortMap_803_ = lean_ctor_get(v_a_792_, 2);
lean_inc_ref(v_sortMap_803_);
lean_inc_ref(v_sortInfo_802_);
lean_inc_ref(v_predInfo_801_);
v___x_804_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_804_, 0, v_predInfo_801_);
lean_ctor_set(v___x_804_, 1, v_sortInfo_802_);
lean_ctor_set(v___x_804_, 2, v_sortMap_803_);
lean_ctor_set(v___x_804_, 3, v_varMap_790_);
lean_inc(v_a_799_);
lean_inc_ref(v_a_798_);
lean_inc(v_a_797_);
lean_inc_ref(v_a_796_);
lean_inc(v_a_795_);
lean_inc_ref(v_a_794_);
lean_inc(v_a_793_);
v___x_805_ = lean_apply_9(v_x_791_, v___x_804_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, lean_box(0));
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_withVarMap___boxed(lean_object* v_00_u03b1_806_, lean_object* v_varMap_807_, lean_object* v_x_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_withVarMap(v_00_u03b1_806_, v_varMap_807_, v_x_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
return v_res_818_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___redArg___closed__1(void){
_start:
{
lean_object* v___x_820_; lean_object* v___f_821_; 
v___x_820_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_EPR_instDecidableEqSortId___boxed), 2, 0);
v___f_821_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_821_, 0, v___x_820_);
return v___f_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___redArg(lean_object* v_sort_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_sortInfo_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___f_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v_sortInfo_825_ = lean_ctor_get(v_a_823_, 1);
v___x_826_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___redArg___closed__0));
v___x_827_ = l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default;
v___f_828_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___redArg___closed__1);
v___x_829_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v___f_828_, v___x_826_, v___x_827_, v_sortInfo_825_, v_sort_822_);
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___redArg___boxed(lean_object* v_sort_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___redArg(v_sort_831_, v_a_832_);
lean_dec_ref(v_a_832_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo(lean_object* v_sort_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_sortInfo_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___f_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_sortInfo_845_ = lean_ctor_get(v_a_836_, 1);
v___x_846_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___redArg___closed__0));
v___x_847_ = l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default;
v___f_848_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___redArg___closed__1);
v___x_849_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v___f_848_, v___x_846_, v___x_847_, v_sortInfo_845_, v_sort_835_);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo___boxed(lean_object* v_sort_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_getSortInfo(v_sort_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp_takeSimpCache___redArg(lean_object* v_a_862_){
_start:
{
lean_object* v___x_864_; lean_object* v_simpCache_865_; lean_object* v_memHypThmsCache_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_876_; 
v___x_864_ = lean_st_ref_take(v_a_862_);
v_simpCache_865_ = lean_ctor_get(v___x_864_, 0);
v_memHypThmsCache_866_ = lean_ctor_get(v___x_864_, 1);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_876_ == 0)
{
v___x_868_ = v___x_864_;
v_isShared_869_ = v_isSharedCheck_876_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_memHypThmsCache_866_);
lean_inc(v_simpCache_865_);
lean_dec(v___x_864_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_876_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_870_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__1);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_870_);
v___x_872_ = v___x_868_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_memHypThmsCache_866_);
v___x_872_ = v_reuseFailAlloc_875_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_st_ref_put(v_a_862_, v___x_872_);
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v_simpCache_865_);
return v___x_874_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp_takeSimpCache___redArg___boxed(lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp_takeSimpCache___redArg(v_a_877_);
lean_dec(v_a_877_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp_takeSimpCache(lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp_takeSimpCache___redArg(v_a_881_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp_takeSimpCache___boxed(lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp_takeSimpCache(v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___lam__0(lean_object* v_x_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___lam__0___closed__0));
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___lam__0___boxed(lean_object* v_x_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___lam__0(v_x_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v_x_915_);
return v_res_926_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__4(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = lean_unsigned_to_nat(0u);
v___x_936_ = l_Lean_Level_ofNat(v___x_935_);
return v___x_936_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__5(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = lean_box(0);
v___x_938_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__4);
v___x_939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v___x_937_);
return v___x_939_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__6(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__5);
v___x_941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__3));
v___x_942_ = l_Lean_mkConst(v___x_941_, v___x_940_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp(lean_object* v_type_943_, lean_object* v_value_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v___f_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_a_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___f_954_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__0));
lean_inc_ref(v_a_945_);
v___x_955_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___boxed), 12, 1);
lean_closure_set(v___x_955_, 0, v_a_945_);
v___x_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v___f_954_);
v___x_957_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp_takeSimpCache___redArg(v_a_946_);
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref(v___x_957_);
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__1);
v___x_961_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set(v___x_961_, 1, v_a_958_);
lean_ctor_set(v___x_961_, 2, v___x_960_);
lean_ctor_set(v___x_961_, 3, v___x_960_);
lean_inc_ref(v_type_943_);
v___x_962_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_962_, 0, v_type_943_);
v___x_963_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__1));
v___x_964_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_962_, v___x_956_, v___x_963_, v___x_961_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_1003_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_1003_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_1003_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v_fst_969_; lean_object* v_snd_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_1002_; 
v_fst_969_ = lean_ctor_get(v_a_965_, 0);
v_snd_970_ = lean_ctor_get(v_a_965_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_a_965_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_972_ = v_a_965_;
v_isShared_973_ = v_isSharedCheck_1002_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_snd_970_);
lean_inc(v_fst_969_);
lean_dec(v_a_965_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_1002_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v_persistentCache_975_; lean_object* v_memHypThmsCache_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1000_; 
v___x_974_ = lean_st_ref_take(v_a_946_);
v_persistentCache_975_ = lean_ctor_get(v_snd_970_, 1);
lean_inc_ref(v_persistentCache_975_);
lean_dec(v_snd_970_);
v_memHypThmsCache_976_ = lean_ctor_get(v___x_974_, 1);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; 
v_unused_1001_ = lean_ctor_get(v___x_974_, 0);
lean_dec(v_unused_1001_);
v___x_978_ = v___x_974_;
v_isShared_979_ = v_isSharedCheck_1000_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_memHypThmsCache_976_);
lean_dec(v___x_974_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1000_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v_persistentCache_975_);
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_persistentCache_975_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_memHypThmsCache_976_);
v___x_981_ = v_reuseFailAlloc_999_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_982_; 
v___x_982_ = lean_st_ref_put(v_a_946_, v___x_981_);
if (lean_obj_tag(v_fst_969_) == 0)
{
lean_object* v___x_984_; 
lean_dec_ref_known(v_fst_969_, 0);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 1, v_value_944_);
lean_ctor_set(v___x_972_, 0, v_type_943_);
v___x_984_ = v___x_972_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_type_943_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_value_944_);
v___x_984_ = v_reuseFailAlloc_988_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_986_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v___x_984_);
v___x_986_ = v___x_967_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
else
{
lean_object* v_e_x27_989_; lean_object* v_proof_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_994_; 
v_e_x27_989_ = lean_ctor_get(v_fst_969_, 0);
lean_inc_ref_n(v_e_x27_989_, 2);
v_proof_990_ = lean_ctor_get(v_fst_969_, 1);
lean_inc_ref(v_proof_990_);
lean_dec_ref_known(v_fst_969_, 2);
v___x_991_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__6);
v___x_992_ = l_Lean_mkApp4(v___x_991_, v_type_943_, v_e_x27_989_, v_proof_990_, v_value_944_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 1, v___x_992_);
lean_ctor_set(v___x_972_, 0, v_e_x27_989_);
v___x_994_ = v___x_972_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_e_x27_989_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v___x_992_);
v___x_994_ = v_reuseFailAlloc_998_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_996_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v___x_994_);
v___x_996_ = v___x_967_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
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
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v_value_944_);
lean_dec_ref(v_type_943_);
v_a_1004_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_964_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_964_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___boxed(lean_object* v_type_1012_, lean_object* v_value_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp(v_type_1012_, v_value_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateGround(lean_object* v_hyp_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_name_1034_; lean_object* v_type_1035_; lean_object* v_value_1036_; lean_object* v_source_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1063_; 
v_name_1034_ = lean_ctor_get(v_hyp_1024_, 0);
v_type_1035_ = lean_ctor_get(v_hyp_1024_, 1);
v_value_1036_ = lean_ctor_get(v_hyp_1024_, 2);
v_source_1037_ = lean_ctor_get(v_hyp_1024_, 3);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_hyp_1024_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1039_ = v_hyp_1024_;
v_isShared_1040_ = v_isSharedCheck_1063_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_source_1037_);
lean_inc(v_value_1036_);
lean_inc(v_type_1035_);
lean_inc(v_name_1034_);
lean_dec(v_hyp_1024_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1063_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; 
v___x_1041_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp(v_type_1035_, v_value_1036_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1054_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1054_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1054_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v_fst_1046_; lean_object* v_snd_1047_; lean_object* v___x_1049_; 
v_fst_1046_ = lean_ctor_get(v_a_1042_, 0);
lean_inc(v_fst_1046_);
v_snd_1047_ = lean_ctor_get(v_a_1042_, 1);
lean_inc(v_snd_1047_);
lean_dec(v_a_1042_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 2, v_snd_1047_);
lean_ctor_set(v___x_1039_, 1, v_fst_1046_);
v___x_1049_ = v___x_1039_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_name_1034_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_fst_1046_);
lean_ctor_set(v_reuseFailAlloc_1053_, 2, v_snd_1047_);
lean_ctor_set(v_reuseFailAlloc_1053_, 3, v_source_1037_);
v___x_1049_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1051_; 
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1049_);
v___x_1051_ = v___x_1044_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_del_object(v___x_1039_);
lean_dec(v_source_1037_);
lean_dec(v_name_1034_);
v_a_1055_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1041_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1041_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateGround___boxed(lean_object* v_hyp_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateGround(v_hyp_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
return v_res_1074_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__4___redArg(lean_object* v_a_1075_, lean_object* v_x_1076_){
_start:
{
if (lean_obj_tag(v_x_1076_) == 0)
{
uint8_t v___x_1077_; 
v___x_1077_ = 0;
return v___x_1077_;
}
else
{
lean_object* v_key_1078_; lean_object* v_tail_1079_; uint8_t v___x_1080_; 
v_key_1078_ = lean_ctor_get(v_x_1076_, 0);
v_tail_1079_ = lean_ctor_get(v_x_1076_, 2);
v___x_1080_ = lean_nat_dec_eq(v_key_1078_, v_a_1075_);
if (v___x_1080_ == 0)
{
v_x_1076_ = v_tail_1079_;
goto _start;
}
else
{
return v___x_1080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__4___redArg___boxed(lean_object* v_a_1082_, lean_object* v_x_1083_){
_start:
{
uint8_t v_res_1084_; lean_object* v_r_1085_; 
v_res_1084_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__4___redArg(v_a_1082_, v_x_1083_);
lean_dec(v_x_1083_);
lean_dec(v_a_1082_);
v_r_1085_ = lean_box(v_res_1084_);
return v_r_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__6___redArg(lean_object* v_a_1086_, lean_object* v_b_1087_, lean_object* v_x_1088_){
_start:
{
if (lean_obj_tag(v_x_1088_) == 0)
{
lean_dec(v_b_1087_);
lean_dec(v_a_1086_);
return v_x_1088_;
}
else
{
lean_object* v_key_1089_; lean_object* v_value_1090_; lean_object* v_tail_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1103_; 
v_key_1089_ = lean_ctor_get(v_x_1088_, 0);
v_value_1090_ = lean_ctor_get(v_x_1088_, 1);
v_tail_1091_ = lean_ctor_get(v_x_1088_, 2);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_x_1088_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1093_ = v_x_1088_;
v_isShared_1094_ = v_isSharedCheck_1103_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_tail_1091_);
lean_inc(v_value_1090_);
lean_inc(v_key_1089_);
lean_dec(v_x_1088_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1103_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
uint8_t v___x_1095_; 
v___x_1095_ = lean_nat_dec_eq(v_key_1089_, v_a_1086_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1096_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__6___redArg(v_a_1086_, v_b_1087_, v_tail_1091_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 2, v___x_1096_);
v___x_1098_ = v___x_1093_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_key_1089_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_value_1090_);
lean_ctor_set(v_reuseFailAlloc_1099_, 2, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
else
{
lean_object* v___x_1101_; 
lean_dec(v_value_1090_);
lean_dec(v_key_1089_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 1, v_b_1087_);
lean_ctor_set(v___x_1093_, 0, v_a_1086_);
v___x_1101_ = v___x_1093_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1086_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_b_1087_);
lean_ctor_set(v_reuseFailAlloc_1102_, 2, v_tail_1091_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__5_spec__6_spec__7___redArg(lean_object* v_x_1104_, lean_object* v_x_1105_){
_start:
{
if (lean_obj_tag(v_x_1105_) == 0)
{
return v_x_1104_;
}
else
{
lean_object* v_key_1106_; lean_object* v_value_1107_; lean_object* v_tail_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1131_; 
v_key_1106_ = lean_ctor_get(v_x_1105_, 0);
v_value_1107_ = lean_ctor_get(v_x_1105_, 1);
v_tail_1108_ = lean_ctor_get(v_x_1105_, 2);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_x_1105_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1110_ = v_x_1105_;
v_isShared_1111_ = v_isSharedCheck_1131_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_tail_1108_);
lean_inc(v_value_1107_);
lean_inc(v_key_1106_);
lean_dec(v_x_1105_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1131_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; uint64_t v___x_1113_; uint64_t v___x_1114_; uint64_t v___x_1115_; uint64_t v_fold_1116_; uint64_t v___x_1117_; uint64_t v___x_1118_; uint64_t v___x_1119_; size_t v___x_1120_; size_t v___x_1121_; size_t v___x_1122_; size_t v___x_1123_; size_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1112_ = lean_array_get_size(v_x_1104_);
v___x_1113_ = l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash(v_key_1106_);
v___x_1114_ = 32ULL;
v___x_1115_ = lean_uint64_shift_right(v___x_1113_, v___x_1114_);
v_fold_1116_ = lean_uint64_xor(v___x_1113_, v___x_1115_);
v___x_1117_ = 16ULL;
v___x_1118_ = lean_uint64_shift_right(v_fold_1116_, v___x_1117_);
v___x_1119_ = lean_uint64_xor(v_fold_1116_, v___x_1118_);
v___x_1120_ = lean_uint64_to_usize(v___x_1119_);
v___x_1121_ = lean_usize_of_nat(v___x_1112_);
v___x_1122_ = ((size_t)1ULL);
v___x_1123_ = lean_usize_sub(v___x_1121_, v___x_1122_);
v___x_1124_ = lean_usize_land(v___x_1120_, v___x_1123_);
v___x_1125_ = lean_array_uget_borrowed(v_x_1104_, v___x_1124_);
lean_inc(v___x_1125_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 2, v___x_1125_);
v___x_1127_ = v___x_1110_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_key_1106_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_value_1107_);
lean_ctor_set(v_reuseFailAlloc_1130_, 2, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_array_uset(v_x_1104_, v___x_1124_, v___x_1127_);
v_x_1104_ = v___x_1128_;
v_x_1105_ = v_tail_1108_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__5_spec__6___redArg(lean_object* v_i_1132_, lean_object* v_source_1133_, lean_object* v_target_1134_){
_start:
{
lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = lean_array_get_size(v_source_1133_);
v___x_1136_ = lean_nat_dec_lt(v_i_1132_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_dec_ref(v_source_1133_);
lean_dec(v_i_1132_);
return v_target_1134_;
}
else
{
lean_object* v_es_1137_; lean_object* v___x_1138_; lean_object* v_source_1139_; lean_object* v_target_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_es_1137_ = lean_array_fget(v_source_1133_, v_i_1132_);
v___x_1138_ = lean_box(0);
v_source_1139_ = lean_array_fset(v_source_1133_, v_i_1132_, v___x_1138_);
v_target_1140_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__5_spec__6_spec__7___redArg(v_target_1134_, v_es_1137_);
v___x_1141_ = lean_unsigned_to_nat(1u);
v___x_1142_ = lean_nat_add(v_i_1132_, v___x_1141_);
lean_dec(v_i_1132_);
v_i_1132_ = v___x_1142_;
v_source_1133_ = v_source_1139_;
v_target_1134_ = v_target_1140_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__5___redArg(lean_object* v_data_1144_){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v_nbuckets_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1145_ = lean_array_get_size(v_data_1144_);
v___x_1146_ = lean_unsigned_to_nat(2u);
v_nbuckets_1147_ = lean_nat_mul(v___x_1145_, v___x_1146_);
v___x_1148_ = lean_unsigned_to_nat(0u);
v___x_1149_ = lean_box(0);
v___x_1150_ = lean_mk_array(v_nbuckets_1147_, v___x_1149_);
v___x_1151_ = lean_array_propagate_mark(v_data_1144_, v___x_1150_);
v___x_1152_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__5_spec__6___redArg(v___x_1148_, v_data_1144_, v___x_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2___redArg(lean_object* v_m_1153_, lean_object* v_a_1154_, lean_object* v_b_1155_){
_start:
{
lean_object* v_size_1156_; lean_object* v_buckets_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1200_; 
v_size_1156_ = lean_ctor_get(v_m_1153_, 0);
v_buckets_1157_ = lean_ctor_get(v_m_1153_, 1);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_m_1153_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1159_ = v_m_1153_;
v_isShared_1160_ = v_isSharedCheck_1200_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_buckets_1157_);
lean_inc(v_size_1156_);
lean_dec(v_m_1153_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1200_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; uint64_t v___x_1162_; uint64_t v___x_1163_; uint64_t v___x_1164_; uint64_t v_fold_1165_; uint64_t v___x_1166_; uint64_t v___x_1167_; uint64_t v___x_1168_; size_t v___x_1169_; size_t v___x_1170_; size_t v___x_1171_; size_t v___x_1172_; size_t v___x_1173_; lean_object* v_bkt_1174_; uint8_t v___x_1175_; 
v___x_1161_ = lean_array_get_size(v_buckets_1157_);
v___x_1162_ = l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash(v_a_1154_);
v___x_1163_ = 32ULL;
v___x_1164_ = lean_uint64_shift_right(v___x_1162_, v___x_1163_);
v_fold_1165_ = lean_uint64_xor(v___x_1162_, v___x_1164_);
v___x_1166_ = 16ULL;
v___x_1167_ = lean_uint64_shift_right(v_fold_1165_, v___x_1166_);
v___x_1168_ = lean_uint64_xor(v_fold_1165_, v___x_1167_);
v___x_1169_ = lean_uint64_to_usize(v___x_1168_);
v___x_1170_ = lean_usize_of_nat(v___x_1161_);
v___x_1171_ = ((size_t)1ULL);
v___x_1172_ = lean_usize_sub(v___x_1170_, v___x_1171_);
v___x_1173_ = lean_usize_land(v___x_1169_, v___x_1172_);
v_bkt_1174_ = lean_array_uget_borrowed(v_buckets_1157_, v___x_1173_);
v___x_1175_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__4___redArg(v_a_1154_, v_bkt_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; lean_object* v_size_x27_1177_; lean_object* v___x_1178_; lean_object* v_buckets_x27_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1176_ = lean_unsigned_to_nat(1u);
v_size_x27_1177_ = lean_nat_add(v_size_1156_, v___x_1176_);
lean_dec(v_size_1156_);
lean_inc(v_bkt_1174_);
v___x_1178_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1178_, 0, v_a_1154_);
lean_ctor_set(v___x_1178_, 1, v_b_1155_);
lean_ctor_set(v___x_1178_, 2, v_bkt_1174_);
v_buckets_x27_1179_ = lean_array_uset(v_buckets_1157_, v___x_1173_, v___x_1178_);
v___x_1180_ = lean_unsigned_to_nat(4u);
v___x_1181_ = lean_nat_mul(v_size_x27_1177_, v___x_1180_);
v___x_1182_ = lean_unsigned_to_nat(3u);
v___x_1183_ = lean_nat_div(v___x_1181_, v___x_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_array_get_size(v_buckets_x27_1179_);
v___x_1185_ = lean_nat_dec_le(v___x_1183_, v___x_1184_);
lean_dec(v___x_1183_);
if (v___x_1185_ == 0)
{
lean_object* v_val_1186_; lean_object* v___x_1188_; 
v_val_1186_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__5___redArg(v_buckets_x27_1179_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v_val_1186_);
lean_ctor_set(v___x_1159_, 0, v_size_x27_1177_);
v___x_1188_ = v___x_1159_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_size_x27_1177_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_val_1186_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
else
{
lean_object* v___x_1191_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v_buckets_x27_1179_);
lean_ctor_set(v___x_1159_, 0, v_size_x27_1177_);
v___x_1191_ = v___x_1159_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_size_x27_1177_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_buckets_x27_1179_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
else
{
lean_object* v___x_1193_; lean_object* v_buckets_x27_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1198_; 
lean_inc(v_bkt_1174_);
v___x_1193_ = lean_box(0);
v_buckets_x27_1194_ = lean_array_uset(v_buckets_1157_, v___x_1173_, v___x_1193_);
v___x_1195_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__6___redArg(v_a_1154_, v_b_1155_, v_bkt_1174_);
v___x_1196_ = lean_array_uset(v_buckets_x27_1194_, v___x_1173_, v___x_1195_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v___x_1196_);
v___x_1198_ = v___x_1159_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_size_1156_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1_spec__2___redArg(lean_object* v_a_1201_, lean_object* v_x_1202_){
_start:
{
if (lean_obj_tag(v_x_1202_) == 0)
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_box(0);
return v___x_1203_;
}
else
{
lean_object* v_key_1204_; lean_object* v_value_1205_; lean_object* v_tail_1206_; uint8_t v___x_1207_; 
v_key_1204_ = lean_ctor_get(v_x_1202_, 0);
v_value_1205_ = lean_ctor_get(v_x_1202_, 1);
v_tail_1206_ = lean_ctor_get(v_x_1202_, 2);
v___x_1207_ = lean_nat_dec_eq(v_key_1204_, v_a_1201_);
if (v___x_1207_ == 0)
{
v_x_1202_ = v_tail_1206_;
goto _start;
}
else
{
lean_object* v___x_1209_; 
lean_inc(v_value_1205_);
v___x_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1209_, 0, v_value_1205_);
return v___x_1209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1_spec__2___redArg___boxed(lean_object* v_a_1210_, lean_object* v_x_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1_spec__2___redArg(v_a_1210_, v_x_1211_);
lean_dec(v_x_1211_);
lean_dec(v_a_1210_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1___redArg(lean_object* v_m_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_buckets_1215_; lean_object* v___x_1216_; uint64_t v___x_1217_; uint64_t v___x_1218_; uint64_t v___x_1219_; uint64_t v_fold_1220_; uint64_t v___x_1221_; uint64_t v___x_1222_; uint64_t v___x_1223_; size_t v___x_1224_; size_t v___x_1225_; size_t v___x_1226_; size_t v___x_1227_; size_t v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v_buckets_1215_ = lean_ctor_get(v_m_1213_, 1);
v___x_1216_ = lean_array_get_size(v_buckets_1215_);
v___x_1217_ = l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash(v_a_1214_);
v___x_1218_ = 32ULL;
v___x_1219_ = lean_uint64_shift_right(v___x_1217_, v___x_1218_);
v_fold_1220_ = lean_uint64_xor(v___x_1217_, v___x_1219_);
v___x_1221_ = 16ULL;
v___x_1222_ = lean_uint64_shift_right(v_fold_1220_, v___x_1221_);
v___x_1223_ = lean_uint64_xor(v_fold_1220_, v___x_1222_);
v___x_1224_ = lean_uint64_to_usize(v___x_1223_);
v___x_1225_ = lean_usize_of_nat(v___x_1216_);
v___x_1226_ = ((size_t)1ULL);
v___x_1227_ = lean_usize_sub(v___x_1225_, v___x_1226_);
v___x_1228_ = lean_usize_land(v___x_1224_, v___x_1227_);
v___x_1229_ = lean_array_uget_borrowed(v_buckets_1215_, v___x_1228_);
v___x_1230_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1_spec__2___redArg(v_a_1214_, v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1___redArg___boxed(lean_object* v_m_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1___redArg(v_m_1231_, v_a_1232_);
lean_dec(v_a_1232_);
lean_dec_ref(v_m_1231_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__0_spec__0(lean_object* v_msgData_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___x_1240_; lean_object* v_env_1241_; uint8_t v___x_1242_; lean_object* v_env_1243_; lean_object* v___x_1244_; lean_object* v_toCold_1245_; lean_object* v_mctx_1246_; lean_object* v_lctx_1247_; lean_object* v_options_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1240_ = lean_st_ref_get(v___y_1238_);
v_env_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc_ref(v_env_1241_);
lean_dec(v___x_1240_);
v___x_1242_ = 0;
v_env_1243_ = l_Lean_Environment_setRecordingDeps(v_env_1241_, v___x_1242_);
v___x_1244_ = lean_st_ref_get(v___y_1236_);
v_toCold_1245_ = lean_ctor_get(v___y_1237_, 0);
v_mctx_1246_ = lean_ctor_get(v___x_1244_, 0);
lean_inc_ref(v_mctx_1246_);
lean_dec(v___x_1244_);
v_lctx_1247_ = lean_ctor_get(v___y_1235_, 2);
v_options_1248_ = lean_ctor_get(v_toCold_1245_, 2);
lean_inc_ref(v_options_1248_);
lean_inc_ref(v_lctx_1247_);
v___x_1249_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1249_, 0, v_env_1243_);
lean_ctor_set(v___x_1249_, 1, v_mctx_1246_);
lean_ctor_set(v___x_1249_, 2, v_lctx_1247_);
lean_ctor_set(v___x_1249_, 3, v_options_1248_);
v___x_1250_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v_msgData_1234_);
v___x_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__0_spec__0___boxed(lean_object* v_msgData_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__0_spec__0(v_msgData_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__0___redArg(lean_object* v_msg_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_ref_1265_; lean_object* v___x_1266_; lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1275_; 
v_ref_1265_ = lean_ctor_get(v___y_1262_, 2);
v___x_1266_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__0_spec__0(v_msg_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1275_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1275_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1273_; 
lean_inc(v_ref_1265_);
v___x_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1271_, 0, v_ref_1265_);
lean_ctor_set(v___x_1271_, 1, v_a_1267_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set_tag(v___x_1269_, 1);
lean_ctor_set(v___x_1269_, 0, v___x_1271_);
v___x_1273_ = v___x_1269_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__0___redArg___boxed(lean_object* v_msg_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__0___redArg(v_msg_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
return v_res_1282_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__1(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__0));
v___x_1285_ = l_Lean_stringToMessageData(v___x_1284_);
return v___x_1285_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__3(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__2));
v___x_1288_ = l_Lean_stringToMessageData(v___x_1287_);
return v___x_1288_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__10(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__5);
v___x_1300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__9));
v___x_1301_ = l_Lean_mkConst(v___x_1300_, v___x_1299_);
return v___x_1301_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__11(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg___closed__0);
v___x_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
return v___x_1303_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__12(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__11, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__11_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__11);
v___x_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp(lean_object* v_expr_1338_, lean_object* v_sortId_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v_sortInfo_1365_; lean_object* v___f_1366_; lean_object* v___x_1367_; lean_object* v_thms_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___x_1433_; lean_object* v_memHypThmsCache_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1514_; 
v_sortInfo_1365_ = lean_ctor_get(v_a_1340_, 1);
v___f_1366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__0));
v___x_1367_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0(v_sortInfo_1365_, v_sortId_1339_);
v___x_1433_ = lean_st_ref_get(v_a_1341_);
v_memHypThmsCache_1434_ = lean_ctor_get(v___x_1433_, 1);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; 
v_unused_1515_ = lean_ctor_get(v___x_1433_, 0);
lean_dec(v_unused_1515_);
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1514_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_memHypThmsCache_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1514_;
goto v_resetjp_1435_;
}
v___jp_1349_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1359_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__1);
v___x_1360_ = l_Lean_MessageData_ofExpr(v___y_1350_);
v___x_1361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1359_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
v___x_1362_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__3);
v___x_1363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1361_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__0___redArg(v___x_1363_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
return v___x_1364_;
}
v___jp_1368_:
{
lean_object* v_elemList_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_elemList_1378_ = lean_ctor_get(v___x_1367_, 4);
lean_inc_ref(v_elemList_1378_);
lean_dec_ref(v___x_1367_);
v___x_1379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__6));
v___x_1380_ = lean_unsigned_to_nat(2u);
v___x_1381_ = lean_mk_empty_array_with_capacity(v___x_1380_);
v___x_1382_ = lean_array_push(v___x_1381_, v_elemList_1378_);
v___x_1383_ = lean_array_push(v___x_1382_, v_expr_1338_);
v___x_1384_ = l_Lean_Meta_mkAppM(v___x_1379_, v___x_1383_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1386_ = l_Lean_Meta_Sym_shareCommonInc(v_a_1385_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc_n(v_a_1387_, 2);
lean_dec_ref_known(v___x_1386_, 1);
v___x_1388_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__7));
v___x_1389_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed), 13, 2);
lean_closure_set(v___x_1389_, 0, v_thms_1369_);
lean_closure_set(v___x_1389_, 1, v___x_1388_);
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
lean_ctor_set(v___x_1390_, 1, v___f_1366_);
v___x_1391_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp___closed__1));
v___x_1392_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_1392_, 0, v_a_1387_);
v___x_1393_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_1392_, v___x_1390_, v___x_1391_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1408_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1396_ = v___x_1393_;
v_isShared_1397_ = v_isSharedCheck_1408_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1393_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1408_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
if (lean_obj_tag(v_a_1394_) == 1)
{
uint8_t v_done_1398_; 
v_done_1398_ = lean_ctor_get_uint8(v_a_1394_, sizeof(void*)*2);
if (v_done_1398_ == 0)
{
uint8_t v_contextDependent_1399_; 
v_contextDependent_1399_ = lean_ctor_get_uint8(v_a_1394_, sizeof(void*)*2 + 1);
if (v_contextDependent_1399_ == 0)
{
lean_object* v_e_x27_1400_; lean_object* v_proof_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1406_; 
v_e_x27_1400_ = lean_ctor_get(v_a_1394_, 0);
lean_inc_ref_n(v_e_x27_1400_, 2);
v_proof_1401_ = lean_ctor_get(v_a_1394_, 1);
lean_inc_ref(v_proof_1401_);
lean_dec_ref_known(v_a_1394_, 2);
v___x_1402_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__10);
v___x_1403_ = l_Lean_mkApp3(v___x_1402_, v_a_1387_, v_e_x27_1400_, v_proof_1401_);
v___x_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1404_, 0, v_e_x27_1400_);
lean_ctor_set(v___x_1404_, 1, v___x_1403_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v___x_1404_);
v___x_1406_ = v___x_1396_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
else
{
lean_dec_ref_known(v_a_1394_, 2);
lean_del_object(v___x_1396_);
v___y_1350_ = v_a_1387_;
v___y_1351_ = v___y_1370_;
v___y_1352_ = v___y_1371_;
v___y_1353_ = v___y_1372_;
v___y_1354_ = v___y_1373_;
v___y_1355_ = v___y_1374_;
v___y_1356_ = v___y_1375_;
v___y_1357_ = v___y_1376_;
v___y_1358_ = v___y_1377_;
goto v___jp_1349_;
}
}
else
{
lean_dec_ref_known(v_a_1394_, 2);
lean_del_object(v___x_1396_);
v___y_1350_ = v_a_1387_;
v___y_1351_ = v___y_1370_;
v___y_1352_ = v___y_1371_;
v___y_1353_ = v___y_1372_;
v___y_1354_ = v___y_1373_;
v___y_1355_ = v___y_1374_;
v___y_1356_ = v___y_1375_;
v___y_1357_ = v___y_1376_;
v___y_1358_ = v___y_1377_;
goto v___jp_1349_;
}
}
else
{
lean_del_object(v___x_1396_);
lean_dec(v_a_1394_);
v___y_1350_ = v_a_1387_;
v___y_1351_ = v___y_1370_;
v___y_1352_ = v___y_1371_;
v___y_1353_ = v___y_1372_;
v___y_1354_ = v___y_1373_;
v___y_1355_ = v___y_1374_;
v___y_1356_ = v___y_1375_;
v___y_1357_ = v___y_1376_;
v___y_1358_ = v___y_1377_;
goto v___jp_1349_;
}
}
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_dec(v_a_1387_);
v_a_1409_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1393_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1393_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec_ref(v_thms_1369_);
v_a_1417_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1386_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1386_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec_ref(v_thms_1369_);
v_a_1425_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1384_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1384_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1___redArg(v_memHypThmsCache_1434_, v_sortId_1339_);
lean_dec_ref(v_memHypThmsCache_1434_);
if (lean_obj_tag(v___x_1438_) == 1)
{
lean_object* v_val_1439_; 
lean_del_object(v___x_1436_);
lean_dec(v_sortId_1339_);
v_val_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_val_1439_);
lean_dec_ref_known(v___x_1438_, 1);
v_thms_1369_ = v_val_1439_;
v___y_1370_ = v_a_1340_;
v___y_1371_ = v_a_1341_;
v___y_1372_ = v_a_1342_;
v___y_1373_ = v_a_1343_;
v___y_1374_ = v_a_1344_;
v___y_1375_ = v_a_1345_;
v___y_1376_ = v_a_1346_;
v___y_1377_ = v_a_1347_;
goto v___jp_1368_;
}
else
{
lean_object* v___x_1440_; lean_object* v_toSortInfo_1441_; lean_object* v_width_1442_; lean_object* v_elemList_1443_; lean_object* v_elemListLt_1444_; lean_object* v_type_1445_; lean_object* v_level_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
lean_dec(v___x_1438_);
v___x_1440_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__12);
v_toSortInfo_1441_ = lean_ctor_get(v___x_1367_, 0);
v_width_1442_ = lean_ctor_get(v___x_1367_, 1);
v_elemList_1443_ = lean_ctor_get(v___x_1367_, 4);
v_elemListLt_1444_ = lean_ctor_get(v___x_1367_, 5);
v_type_1445_ = lean_ctor_get(v_toSortInfo_1441_, 0);
v_level_1446_ = lean_ctor_get(v_toSortInfo_1441_, 1);
v___x_1447_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__14));
v___x_1448_ = lean_box(0);
lean_inc(v_level_1446_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set_tag(v___x_1436_, 1);
lean_ctor_set(v___x_1436_, 1, v___x_1448_);
lean_ctor_set(v___x_1436_, 0, v_level_1446_);
v___x_1450_ = v___x_1436_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_level_1446_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1451_ = l_Lean_mkConst(v___x_1447_, v___x_1450_);
lean_inc(v_width_1442_);
v___x_1452_ = l_Lean_mkNatLit(v_width_1442_);
lean_inc_ref(v_elemListLt_1444_);
lean_inc_ref(v_elemList_1443_);
lean_inc_ref(v_type_1445_);
v___x_1453_ = l_Lean_mkApp4(v___x_1451_, v_type_1445_, v___x_1452_, v_elemList_1443_, v_elemListLt_1444_);
v___x_1454_ = l_Lean_Meta_Sym_Simp_mkTheoremFromExpr(v___x_1453_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref_known(v___x_1454_, 1);
v___x_1456_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v___x_1440_, v_a_1455_);
v___x_1457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__16));
v___x_1458_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v___x_1457_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___x_1458_, 1);
v___x_1460_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v___x_1456_, v_a_1459_);
v___x_1461_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__18));
v___x_1462_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v___x_1461_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1462_, 1);
v___x_1464_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v___x_1460_, v_a_1463_);
v___x_1465_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___closed__20));
v___x_1466_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v___x_1465_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v_simpCache_1470_; lean_object* v_memHypThmsCache_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1480_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
v___x_1468_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v___x_1464_, v_a_1467_);
v___x_1469_ = lean_st_ref_take(v_a_1341_);
v_simpCache_1470_ = lean_ctor_get(v___x_1469_, 0);
v_memHypThmsCache_1471_ = lean_ctor_get(v___x_1469_, 1);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1473_ = v___x_1469_;
v_isShared_1474_ = v_isSharedCheck_1480_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_memHypThmsCache_1471_);
lean_inc(v_simpCache_1470_);
lean_dec(v___x_1469_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1480_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v___x_1477_; 
lean_inc_ref(v___x_1468_);
v___x_1475_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2___redArg(v_memHypThmsCache_1471_, v_sortId_1339_, v___x_1468_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 1, v___x_1475_);
v___x_1477_ = v___x_1473_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_simpCache_1470_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1478_; 
v___x_1478_ = lean_st_ref_put(v_a_1341_, v___x_1477_);
v_thms_1369_ = v___x_1468_;
v___y_1370_ = v_a_1340_;
v___y_1371_ = v_a_1341_;
v___y_1372_ = v_a_1342_;
v___y_1373_ = v_a_1343_;
v___y_1374_ = v_a_1344_;
v___y_1375_ = v_a_1345_;
v___y_1376_ = v_a_1346_;
v___y_1377_ = v_a_1347_;
goto v___jp_1368_;
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v___x_1464_);
lean_dec_ref(v___x_1367_);
lean_dec(v_sortId_1339_);
lean_dec_ref(v_expr_1338_);
v_a_1481_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1466_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1466_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec_ref(v___x_1460_);
lean_dec_ref(v___x_1367_);
lean_dec(v_sortId_1339_);
lean_dec_ref(v_expr_1338_);
v_a_1489_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1462_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1462_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_dec_ref(v___x_1456_);
lean_dec_ref(v___x_1367_);
lean_dec(v_sortId_1339_);
lean_dec_ref(v_expr_1338_);
v_a_1497_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1458_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1458_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec_ref(v___x_1367_);
lean_dec(v_sortId_1339_);
lean_dec_ref(v_expr_1338_);
v_a_1505_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1454_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1454_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp___boxed(lean_object* v_expr_1516_, lean_object* v_sortId_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp(v_expr_1516_, v_sortId_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
lean_dec(v_a_1523_);
lean_dec_ref(v_a_1522_);
lean_dec(v_a_1521_);
lean_dec_ref(v_a_1520_);
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__0(lean_object* v_00_u03b1_1528_, lean_object* v_msg_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__0___redArg(v_msg_1529_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__0___boxed(lean_object* v_00_u03b1_1540_, lean_object* v_msg_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__0(v_00_u03b1_1540_, v_msg_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1(lean_object* v_00_u03b2_1552_, lean_object* v_m_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1___redArg(v_m_1553_, v_a_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1___boxed(lean_object* v_00_u03b2_1556_, lean_object* v_m_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1(v_00_u03b2_1556_, v_m_1557_, v_a_1558_);
lean_dec(v_a_1558_);
lean_dec_ref(v_m_1557_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2(lean_object* v_00_u03b2_1560_, lean_object* v_m_1561_, lean_object* v_a_1562_, lean_object* v_b_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2___redArg(v_m_1561_, v_a_1562_, v_b_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1_spec__2(lean_object* v_00_u03b2_1565_, lean_object* v_a_1566_, lean_object* v_x_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1_spec__2___redArg(v_a_1566_, v_x_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1569_, lean_object* v_a_1570_, lean_object* v_x_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__1_spec__2(v_00_u03b2_1569_, v_a_1570_, v_x_1571_);
lean_dec(v_x_1571_);
lean_dec(v_a_1570_);
return v_res_1572_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__4(lean_object* v_00_u03b2_1573_, lean_object* v_a_1574_, lean_object* v_x_1575_){
_start:
{
uint8_t v___x_1576_; 
v___x_1576_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__4___redArg(v_a_1574_, v_x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1577_, lean_object* v_a_1578_, lean_object* v_x_1579_){
_start:
{
uint8_t v_res_1580_; lean_object* v_r_1581_; 
v_res_1580_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__4(v_00_u03b2_1577_, v_a_1578_, v_x_1579_);
lean_dec(v_x_1579_);
lean_dec(v_a_1578_);
v_r_1581_ = lean_box(v_res_1580_);
return v_r_1581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__5(lean_object* v_00_u03b2_1582_, lean_object* v_data_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__5___redArg(v_data_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__6(lean_object* v_00_u03b2_1585_, lean_object* v_a_1586_, lean_object* v_b_1587_, lean_object* v_x_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__6___redArg(v_a_1586_, v_b_1587_, v_x_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_1590_, lean_object* v_i_1591_, lean_object* v_source_1592_, lean_object* v_target_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__5_spec__6___redArg(v_i_1591_, v_source_1592_, v_target_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_1595_, lean_object* v_x_1596_, lean_object* v_x_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2_spec__5_spec__6_spec__7___redArg(v_x_1596_, v_x_1597_);
return v___x_1598_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_instMonadEIO___redArg();
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1(lean_object* v_msg_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v_toApplicative_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1681_; 
v___x_1614_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__0);
v___x_1615_ = l_StateRefT_x27_instMonad___redArg(v___x_1614_);
v_toApplicative_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1681_ == 0)
{
lean_object* v_unused_1682_; 
v_unused_1682_ = lean_ctor_get(v___x_1615_, 1);
lean_dec(v_unused_1682_);
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1681_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_toApplicative_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1681_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v_toFunctor_1620_; lean_object* v_toSeq_1621_; lean_object* v_toSeqLeft_1622_; lean_object* v_toSeqRight_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1679_; 
v_toFunctor_1620_ = lean_ctor_get(v_toApplicative_1616_, 0);
v_toSeq_1621_ = lean_ctor_get(v_toApplicative_1616_, 2);
v_toSeqLeft_1622_ = lean_ctor_get(v_toApplicative_1616_, 3);
v_toSeqRight_1623_ = lean_ctor_get(v_toApplicative_1616_, 4);
v_isSharedCheck_1679_ = !lean_is_exclusive(v_toApplicative_1616_);
if (v_isSharedCheck_1679_ == 0)
{
lean_object* v_unused_1680_; 
v_unused_1680_ = lean_ctor_get(v_toApplicative_1616_, 1);
lean_dec(v_unused_1680_);
v___x_1625_ = v_toApplicative_1616_;
v_isShared_1626_ = v_isSharedCheck_1679_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_toSeqRight_1623_);
lean_inc(v_toSeqLeft_1622_);
lean_inc(v_toSeq_1621_);
lean_inc(v_toFunctor_1620_);
lean_dec(v_toApplicative_1616_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1679_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___f_1627_; lean_object* v___f_1628_; lean_object* v___f_1629_; lean_object* v___f_1630_; lean_object* v___x_1631_; lean_object* v___f_1632_; lean_object* v___f_1633_; lean_object* v___f_1634_; lean_object* v___x_1636_; 
v___f_1627_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__1));
v___f_1628_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1620_);
v___f_1629_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1629_, 0, v_toFunctor_1620_);
v___f_1630_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1630_, 0, v_toFunctor_1620_);
v___x_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___f_1629_);
lean_ctor_set(v___x_1631_, 1, v___f_1630_);
v___f_1632_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1632_, 0, v_toSeqRight_1623_);
v___f_1633_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1633_, 0, v_toSeqLeft_1622_);
v___f_1634_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1634_, 0, v_toSeq_1621_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 4, v___f_1632_);
lean_ctor_set(v___x_1625_, 3, v___f_1633_);
lean_ctor_set(v___x_1625_, 2, v___f_1634_);
lean_ctor_set(v___x_1625_, 1, v___f_1627_);
lean_ctor_set(v___x_1625_, 0, v___x_1631_);
v___x_1636_ = v___x_1625_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v___f_1627_);
lean_ctor_set(v_reuseFailAlloc_1678_, 2, v___f_1634_);
lean_ctor_set(v_reuseFailAlloc_1678_, 3, v___f_1633_);
lean_ctor_set(v_reuseFailAlloc_1678_, 4, v___f_1632_);
v___x_1636_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1638_; 
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 1, v___f_1628_);
lean_ctor_set(v___x_1618_, 0, v___x_1636_);
v___x_1638_ = v___x_1618_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1636_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v___f_1628_);
v___x_1638_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
lean_object* v___x_1639_; lean_object* v_toApplicative_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1675_; 
v___x_1639_ = l_StateRefT_x27_instMonad___redArg(v___x_1638_);
v_toApplicative_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1675_ == 0)
{
lean_object* v_unused_1676_; 
v_unused_1676_ = lean_ctor_get(v___x_1639_, 1);
lean_dec(v_unused_1676_);
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1675_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_toApplicative_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1675_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v_toFunctor_1644_; lean_object* v_toSeq_1645_; lean_object* v_toSeqLeft_1646_; lean_object* v_toSeqRight_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1673_; 
v_toFunctor_1644_ = lean_ctor_get(v_toApplicative_1640_, 0);
v_toSeq_1645_ = lean_ctor_get(v_toApplicative_1640_, 2);
v_toSeqLeft_1646_ = lean_ctor_get(v_toApplicative_1640_, 3);
v_toSeqRight_1647_ = lean_ctor_get(v_toApplicative_1640_, 4);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_toApplicative_1640_);
if (v_isSharedCheck_1673_ == 0)
{
lean_object* v_unused_1674_; 
v_unused_1674_ = lean_ctor_get(v_toApplicative_1640_, 1);
lean_dec(v_unused_1674_);
v___x_1649_ = v_toApplicative_1640_;
v_isShared_1650_ = v_isSharedCheck_1673_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_toSeqRight_1647_);
lean_inc(v_toSeqLeft_1646_);
lean_inc(v_toSeq_1645_);
lean_inc(v_toFunctor_1644_);
lean_dec(v_toApplicative_1640_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1673_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___f_1651_; lean_object* v___f_1652_; lean_object* v___f_1653_; lean_object* v___f_1654_; lean_object* v___x_1655_; lean_object* v___f_1656_; lean_object* v___f_1657_; lean_object* v___f_1658_; lean_object* v___x_1660_; 
v___f_1651_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__3));
v___f_1652_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1644_);
v___f_1653_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1653_, 0, v_toFunctor_1644_);
v___f_1654_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1654_, 0, v_toFunctor_1644_);
v___x_1655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___f_1653_);
lean_ctor_set(v___x_1655_, 1, v___f_1654_);
v___f_1656_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1656_, 0, v_toSeqRight_1647_);
v___f_1657_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1657_, 0, v_toSeqLeft_1646_);
v___f_1658_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1658_, 0, v_toSeq_1645_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 4, v___f_1656_);
lean_ctor_set(v___x_1649_, 3, v___f_1657_);
lean_ctor_set(v___x_1649_, 2, v___f_1658_);
lean_ctor_set(v___x_1649_, 1, v___f_1651_);
lean_ctor_set(v___x_1649_, 0, v___x_1655_);
v___x_1660_ = v___x_1649_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v___f_1651_);
lean_ctor_set(v_reuseFailAlloc_1672_, 2, v___f_1658_);
lean_ctor_set(v_reuseFailAlloc_1672_, 3, v___f_1657_);
lean_ctor_set(v_reuseFailAlloc_1672_, 4, v___f_1656_);
v___x_1660_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1662_; 
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 1, v___f_1652_);
lean_ctor_set(v___x_1642_, 0, v___x_1660_);
v___x_1662_ = v___x_1642_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v___f_1652_);
v___x_1662_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___f_1668_; lean_object* v___x_14114__overap_1669_; lean_object* v___x_1670_; 
v___x_1663_ = l_StateRefT_x27_instMonad___redArg(v___x_1662_);
v___x_1664_ = l_ReaderT_instMonad___redArg(v___x_1663_);
v___x_1665_ = l_StateRefT_x27_instMonad___redArg(v___x_1664_);
v___x_1666_ = l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedQuantifiedFact_default;
v___x_1667_ = l_instInhabitedOfMonad___redArg(v___x_1665_, v___x_1666_);
v___f_1668_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1668_, 0, v___x_1667_);
v___x_14114__overap_1669_ = lean_panic_fn_borrowed(v___f_1668_, v_msg_1604_);
lean_dec_ref(v___f_1668_);
lean_inc(v___y_1612_);
lean_inc_ref(v___y_1611_);
lean_inc(v___y_1610_);
lean_inc_ref(v___y_1609_);
lean_inc(v___y_1608_);
lean_inc_ref(v___y_1607_);
lean_inc(v___y_1606_);
lean_inc_ref(v___y_1605_);
v___x_1670_ = lean_apply_9(v___x_14114__overap_1669_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, lean_box(0));
return v___x_1670_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___boxed(lean_object* v_msg_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1(v_msg_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__5___redArg___lam__0(lean_object* v_k_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v_b_1699_, lean_object* v_c_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1706_; 
lean_inc(v___y_1704_);
lean_inc_ref(v___y_1703_);
lean_inc(v___y_1702_);
lean_inc_ref(v___y_1701_);
lean_inc(v___y_1698_);
lean_inc_ref(v___y_1697_);
lean_inc(v___y_1696_);
lean_inc_ref(v___y_1695_);
v___x_1706_ = lean_apply_11(v_k_1694_, v_b_1699_, v_c_1700_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, lean_box(0));
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__5___redArg___lam__0___boxed(lean_object* v_k_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v_b_1712_, lean_object* v_c_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__5___redArg___lam__0(v_k_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v_b_1712_, v_c_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__5___redArg(lean_object* v_type_1720_, lean_object* v_maxFVars_x3f_1721_, lean_object* v_k_1722_, uint8_t v_cleanupAnnotations_1723_, uint8_t v_whnfType_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___f_1734_; lean_object* v___x_1735_; 
lean_inc(v___y_1728_);
lean_inc_ref(v___y_1727_);
lean_inc(v___y_1726_);
lean_inc_ref(v___y_1725_);
v___f_1734_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__5___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1734_, 0, v_k_1722_);
lean_closure_set(v___f_1734_, 1, v___y_1725_);
lean_closure_set(v___f_1734_, 2, v___y_1726_);
lean_closure_set(v___f_1734_, 3, v___y_1727_);
lean_closure_set(v___f_1734_, 4, v___y_1728_);
v___x_1735_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1720_, v_maxFVars_x3f_1721_, v___f_1734_, v_cleanupAnnotations_1723_, v_whnfType_1724_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1735_) == 0)
{
return v___x_1735_;
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1735_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__5___redArg___boxed(lean_object* v_type_1744_, lean_object* v_maxFVars_x3f_1745_, lean_object* v_k_1746_, lean_object* v_cleanupAnnotations_1747_, lean_object* v_whnfType_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1758_; uint8_t v_whnfType_boxed_1759_; lean_object* v_res_1760_; 
v_cleanupAnnotations_boxed_1758_ = lean_unbox(v_cleanupAnnotations_1747_);
v_whnfType_boxed_1759_ = lean_unbox(v_whnfType_1748_);
v_res_1760_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__5___redArg(v_type_1744_, v_maxFVars_x3f_1745_, v_k_1746_, v_cleanupAnnotations_boxed_1758_, v_whnfType_boxed_1759_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__5(lean_object* v_00_u03b1_1761_, lean_object* v_type_1762_, lean_object* v_maxFVars_x3f_1763_, lean_object* v_k_1764_, uint8_t v_cleanupAnnotations_1765_, uint8_t v_whnfType_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__5___redArg(v_type_1762_, v_maxFVars_x3f_1763_, v_k_1764_, v_cleanupAnnotations_1765_, v_whnfType_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__5___boxed(lean_object* v_00_u03b1_1777_, lean_object* v_type_1778_, lean_object* v_maxFVars_x3f_1779_, lean_object* v_k_1780_, lean_object* v_cleanupAnnotations_1781_, lean_object* v_whnfType_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1792_; uint8_t v_whnfType_boxed_1793_; lean_object* v_res_1794_; 
v_cleanupAnnotations_boxed_1792_ = lean_unbox(v_cleanupAnnotations_1781_);
v_whnfType_boxed_1793_ = lean_unbox(v_whnfType_1782_);
v_res_1794_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__5(v_00_u03b1_1777_, v_type_1778_, v_maxFVars_x3f_1779_, v_k_1780_, v_cleanupAnnotations_boxed_1792_, v_whnfType_boxed_1793_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__1_spec__4_spec__8___redArg(lean_object* v_x_1795_, lean_object* v_x_1796_){
_start:
{
if (lean_obj_tag(v_x_1796_) == 0)
{
return v_x_1795_;
}
else
{
lean_object* v_key_1797_; lean_object* v_value_1798_; lean_object* v_tail_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1822_; 
v_key_1797_ = lean_ctor_get(v_x_1796_, 0);
v_value_1798_ = lean_ctor_get(v_x_1796_, 1);
v_tail_1799_ = lean_ctor_get(v_x_1796_, 2);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_x_1796_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1801_ = v_x_1796_;
v_isShared_1802_ = v_isSharedCheck_1822_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_tail_1799_);
lean_inc(v_value_1798_);
lean_inc(v_key_1797_);
lean_dec(v_x_1796_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1822_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; uint64_t v___x_1804_; uint64_t v___x_1805_; uint64_t v___x_1806_; uint64_t v_fold_1807_; uint64_t v___x_1808_; uint64_t v___x_1809_; uint64_t v___x_1810_; size_t v___x_1811_; size_t v___x_1812_; size_t v___x_1813_; size_t v___x_1814_; size_t v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1803_ = lean_array_get_size(v_x_1795_);
v___x_1804_ = l_Lean_Expr_hash(v_key_1797_);
v___x_1805_ = 32ULL;
v___x_1806_ = lean_uint64_shift_right(v___x_1804_, v___x_1805_);
v_fold_1807_ = lean_uint64_xor(v___x_1804_, v___x_1806_);
v___x_1808_ = 16ULL;
v___x_1809_ = lean_uint64_shift_right(v_fold_1807_, v___x_1808_);
v___x_1810_ = lean_uint64_xor(v_fold_1807_, v___x_1809_);
v___x_1811_ = lean_uint64_to_usize(v___x_1810_);
v___x_1812_ = lean_usize_of_nat(v___x_1803_);
v___x_1813_ = ((size_t)1ULL);
v___x_1814_ = lean_usize_sub(v___x_1812_, v___x_1813_);
v___x_1815_ = lean_usize_land(v___x_1811_, v___x_1814_);
v___x_1816_ = lean_array_uget_borrowed(v_x_1795_, v___x_1815_);
lean_inc(v___x_1816_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 2, v___x_1816_);
v___x_1818_ = v___x_1801_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_key_1797_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_value_1798_);
lean_ctor_set(v_reuseFailAlloc_1821_, 2, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1819_; 
v___x_1819_ = lean_array_uset(v_x_1795_, v___x_1815_, v___x_1818_);
v_x_1795_ = v___x_1819_;
v_x_1796_ = v_tail_1799_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__1_spec__4___redArg(lean_object* v_i_1823_, lean_object* v_source_1824_, lean_object* v_target_1825_){
_start:
{
lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1826_ = lean_array_get_size(v_source_1824_);
v___x_1827_ = lean_nat_dec_lt(v_i_1823_, v___x_1826_);
if (v___x_1827_ == 0)
{
lean_dec_ref(v_source_1824_);
lean_dec(v_i_1823_);
return v_target_1825_;
}
else
{
lean_object* v_es_1828_; lean_object* v___x_1829_; lean_object* v_source_1830_; lean_object* v_target_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v_es_1828_ = lean_array_fget(v_source_1824_, v_i_1823_);
v___x_1829_ = lean_box(0);
v_source_1830_ = lean_array_fset(v_source_1824_, v_i_1823_, v___x_1829_);
v_target_1831_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__1_spec__4_spec__8___redArg(v_target_1825_, v_es_1828_);
v___x_1832_ = lean_unsigned_to_nat(1u);
v___x_1833_ = lean_nat_add(v_i_1823_, v___x_1832_);
lean_dec(v_i_1823_);
v_i_1823_ = v___x_1833_;
v_source_1824_ = v_source_1830_;
v_target_1825_ = v_target_1831_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__1___redArg(lean_object* v_data_1835_){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v_nbuckets_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1836_ = lean_array_get_size(v_data_1835_);
v___x_1837_ = lean_unsigned_to_nat(2u);
v_nbuckets_1838_ = lean_nat_mul(v___x_1836_, v___x_1837_);
v___x_1839_ = lean_unsigned_to_nat(0u);
v___x_1840_ = lean_box(0);
v___x_1841_ = lean_mk_array(v_nbuckets_1838_, v___x_1840_);
v___x_1842_ = lean_array_propagate_mark(v_data_1835_, v___x_1841_);
v___x_1843_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__1_spec__4___redArg(v___x_1839_, v_data_1835_, v___x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__0___redArg(lean_object* v_a_1844_, lean_object* v_x_1845_){
_start:
{
if (lean_obj_tag(v_x_1845_) == 0)
{
uint8_t v___x_1846_; 
v___x_1846_ = 0;
return v___x_1846_;
}
else
{
lean_object* v_key_1847_; lean_object* v_tail_1848_; uint8_t v___x_1849_; 
v_key_1847_ = lean_ctor_get(v_x_1845_, 0);
v_tail_1848_ = lean_ctor_get(v_x_1845_, 2);
v___x_1849_ = lean_expr_eqv(v_key_1847_, v_a_1844_);
if (v___x_1849_ == 0)
{
v_x_1845_ = v_tail_1848_;
goto _start;
}
else
{
return v___x_1849_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__0___redArg___boxed(lean_object* v_a_1851_, lean_object* v_x_1852_){
_start:
{
uint8_t v_res_1853_; lean_object* v_r_1854_; 
v_res_1853_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__0___redArg(v_a_1851_, v_x_1852_);
lean_dec(v_x_1852_);
lean_dec_ref(v_a_1851_);
v_r_1854_ = lean_box(v_res_1853_);
return v_r_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__2___redArg(lean_object* v_a_1855_, lean_object* v_b_1856_, lean_object* v_x_1857_){
_start:
{
if (lean_obj_tag(v_x_1857_) == 0)
{
lean_dec(v_b_1856_);
lean_dec_ref(v_a_1855_);
return v_x_1857_;
}
else
{
lean_object* v_key_1858_; lean_object* v_value_1859_; lean_object* v_tail_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1872_; 
v_key_1858_ = lean_ctor_get(v_x_1857_, 0);
v_value_1859_ = lean_ctor_get(v_x_1857_, 1);
v_tail_1860_ = lean_ctor_get(v_x_1857_, 2);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_x_1857_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1862_ = v_x_1857_;
v_isShared_1863_ = v_isSharedCheck_1872_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_tail_1860_);
lean_inc(v_value_1859_);
lean_inc(v_key_1858_);
lean_dec(v_x_1857_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1872_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
uint8_t v___x_1864_; 
v___x_1864_ = lean_expr_eqv(v_key_1858_, v_a_1855_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1865_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__2___redArg(v_a_1855_, v_b_1856_, v_tail_1860_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 2, v___x_1865_);
v___x_1867_ = v___x_1862_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_key_1858_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_value_1859_);
lean_ctor_set(v_reuseFailAlloc_1868_, 2, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
else
{
lean_object* v___x_1870_; 
lean_dec(v_value_1859_);
lean_dec(v_key_1858_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 1, v_b_1856_);
lean_ctor_set(v___x_1862_, 0, v_a_1855_);
v___x_1870_ = v___x_1862_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1855_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v_b_1856_);
lean_ctor_set(v_reuseFailAlloc_1871_, 2, v_tail_1860_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0___redArg(lean_object* v_m_1873_, lean_object* v_a_1874_, lean_object* v_b_1875_){
_start:
{
lean_object* v_size_1876_; lean_object* v_buckets_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1920_; 
v_size_1876_ = lean_ctor_get(v_m_1873_, 0);
v_buckets_1877_ = lean_ctor_get(v_m_1873_, 1);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_m_1873_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1879_ = v_m_1873_;
v_isShared_1880_ = v_isSharedCheck_1920_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_buckets_1877_);
lean_inc(v_size_1876_);
lean_dec(v_m_1873_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1920_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; uint64_t v___x_1882_; uint64_t v___x_1883_; uint64_t v___x_1884_; uint64_t v_fold_1885_; uint64_t v___x_1886_; uint64_t v___x_1887_; uint64_t v___x_1888_; size_t v___x_1889_; size_t v___x_1890_; size_t v___x_1891_; size_t v___x_1892_; size_t v___x_1893_; lean_object* v_bkt_1894_; uint8_t v___x_1895_; 
v___x_1881_ = lean_array_get_size(v_buckets_1877_);
v___x_1882_ = l_Lean_Expr_hash(v_a_1874_);
v___x_1883_ = 32ULL;
v___x_1884_ = lean_uint64_shift_right(v___x_1882_, v___x_1883_);
v_fold_1885_ = lean_uint64_xor(v___x_1882_, v___x_1884_);
v___x_1886_ = 16ULL;
v___x_1887_ = lean_uint64_shift_right(v_fold_1885_, v___x_1886_);
v___x_1888_ = lean_uint64_xor(v_fold_1885_, v___x_1887_);
v___x_1889_ = lean_uint64_to_usize(v___x_1888_);
v___x_1890_ = lean_usize_of_nat(v___x_1881_);
v___x_1891_ = ((size_t)1ULL);
v___x_1892_ = lean_usize_sub(v___x_1890_, v___x_1891_);
v___x_1893_ = lean_usize_land(v___x_1889_, v___x_1892_);
v_bkt_1894_ = lean_array_uget_borrowed(v_buckets_1877_, v___x_1893_);
v___x_1895_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__0___redArg(v_a_1874_, v_bkt_1894_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v_size_x27_1897_; lean_object* v___x_1898_; lean_object* v_buckets_x27_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___x_1896_ = lean_unsigned_to_nat(1u);
v_size_x27_1897_ = lean_nat_add(v_size_1876_, v___x_1896_);
lean_dec(v_size_1876_);
lean_inc(v_bkt_1894_);
v___x_1898_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1898_, 0, v_a_1874_);
lean_ctor_set(v___x_1898_, 1, v_b_1875_);
lean_ctor_set(v___x_1898_, 2, v_bkt_1894_);
v_buckets_x27_1899_ = lean_array_uset(v_buckets_1877_, v___x_1893_, v___x_1898_);
v___x_1900_ = lean_unsigned_to_nat(4u);
v___x_1901_ = lean_nat_mul(v_size_x27_1897_, v___x_1900_);
v___x_1902_ = lean_unsigned_to_nat(3u);
v___x_1903_ = lean_nat_div(v___x_1901_, v___x_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_array_get_size(v_buckets_x27_1899_);
v___x_1905_ = lean_nat_dec_le(v___x_1903_, v___x_1904_);
lean_dec(v___x_1903_);
if (v___x_1905_ == 0)
{
lean_object* v_val_1906_; lean_object* v___x_1908_; 
v_val_1906_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__1___redArg(v_buckets_x27_1899_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 1, v_val_1906_);
lean_ctor_set(v___x_1879_, 0, v_size_x27_1897_);
v___x_1908_ = v___x_1879_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_size_x27_1897_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v_val_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
else
{
lean_object* v___x_1911_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 1, v_buckets_x27_1899_);
lean_ctor_set(v___x_1879_, 0, v_size_x27_1897_);
v___x_1911_ = v___x_1879_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_size_x27_1897_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_buckets_x27_1899_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
else
{
lean_object* v___x_1913_; lean_object* v_buckets_x27_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1918_; 
lean_inc(v_bkt_1894_);
v___x_1913_ = lean_box(0);
v_buckets_x27_1914_ = lean_array_uset(v_buckets_1877_, v___x_1893_, v___x_1913_);
v___x_1915_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__2___redArg(v_a_1874_, v_b_1875_, v_bkt_1894_);
v___x_1916_ = lean_array_uset(v_buckets_x27_1914_, v___x_1893_, v___x_1915_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 1, v___x_1916_);
v___x_1918_ = v___x_1879_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_size_1876_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__3___redArg(lean_object* v_as_1921_, size_t v_sz_1922_, size_t v_i_1923_, lean_object* v_b_1924_){
_start:
{
uint8_t v___x_1926_; 
v___x_1926_ = lean_usize_dec_lt(v_i_1923_, v_sz_1922_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; 
v___x_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1927_, 0, v_b_1924_);
return v___x_1927_;
}
else
{
lean_object* v_snd_1928_; lean_object* v_snd_1929_; lean_object* v_snd_1930_; lean_object* v_fst_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_2042_; 
v_snd_1928_ = lean_ctor_get(v_b_1924_, 1);
lean_inc(v_snd_1928_);
v_snd_1929_ = lean_ctor_get(v_snd_1928_, 1);
lean_inc(v_snd_1929_);
v_snd_1930_ = lean_ctor_get(v_snd_1929_, 1);
lean_inc(v_snd_1930_);
v_fst_1931_ = lean_ctor_get(v_b_1924_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_b_1924_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; 
v_unused_2043_ = lean_ctor_get(v_b_1924_, 1);
lean_dec(v_unused_2043_);
v___x_1933_ = v_b_1924_;
v_isShared_1934_ = v_isSharedCheck_2042_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_fst_1931_);
lean_dec(v_b_1924_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_2042_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v_fst_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_2040_; 
v_fst_1935_ = lean_ctor_get(v_snd_1928_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_snd_1928_);
if (v_isSharedCheck_2040_ == 0)
{
lean_object* v_unused_2041_; 
v_unused_2041_ = lean_ctor_get(v_snd_1928_, 1);
lean_dec(v_unused_2041_);
v___x_1937_ = v_snd_1928_;
v_isShared_1938_ = v_isSharedCheck_2040_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_fst_1935_);
lean_dec(v_snd_1928_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_2040_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v_fst_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_2038_; 
v_fst_1939_ = lean_ctor_get(v_snd_1929_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v_snd_1929_);
if (v_isSharedCheck_2038_ == 0)
{
lean_object* v_unused_2039_; 
v_unused_2039_ = lean_ctor_get(v_snd_1929_, 1);
lean_dec(v_unused_2039_);
v___x_1941_ = v_snd_1929_;
v_isShared_1942_ = v_isSharedCheck_2038_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_fst_1939_);
lean_dec(v_snd_1929_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_2038_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v_array_1943_; lean_object* v_start_1944_; lean_object* v_stop_1945_; uint8_t v___x_1946_; 
v_array_1943_ = lean_ctor_get(v_snd_1930_, 0);
v_start_1944_ = lean_ctor_get(v_snd_1930_, 1);
v_stop_1945_ = lean_ctor_get(v_snd_1930_, 2);
v___x_1946_ = lean_nat_dec_lt(v_start_1944_, v_stop_1945_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1948_; 
if (v_isShared_1942_ == 0)
{
v___x_1948_ = v___x_1941_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_fst_1939_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_snd_1930_);
v___x_1948_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
lean_object* v___x_1950_; 
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 1, v___x_1948_);
v___x_1950_ = v___x_1937_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_fst_1935_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v___x_1948_);
v___x_1950_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
lean_object* v___x_1952_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 1, v___x_1950_);
v___x_1952_ = v___x_1933_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_fst_1931_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1953_; 
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
return v___x_1953_;
}
}
}
}
else
{
lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_2034_; 
lean_inc(v_stop_1945_);
lean_inc(v_start_1944_);
lean_inc_ref(v_array_1943_);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_snd_1930_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; lean_object* v_unused_2036_; lean_object* v_unused_2037_; 
v_unused_2035_ = lean_ctor_get(v_snd_1930_, 2);
lean_dec(v_unused_2035_);
v_unused_2036_ = lean_ctor_get(v_snd_1930_, 1);
lean_dec(v_unused_2036_);
v_unused_2037_ = lean_ctor_get(v_snd_1930_, 0);
lean_dec(v_unused_2037_);
v___x_1958_ = v_snd_1930_;
v_isShared_1959_ = v_isSharedCheck_2034_;
goto v_resetjp_1957_;
}
else
{
lean_dec(v_snd_1930_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_2034_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v_array_1960_; lean_object* v_start_1961_; lean_object* v_stop_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; 
v_array_1960_ = lean_ctor_get(v_fst_1939_, 0);
v_start_1961_ = lean_ctor_get(v_fst_1939_, 1);
v_stop_1962_ = lean_ctor_get(v_fst_1939_, 2);
v___x_1963_ = lean_array_fget(v_array_1943_, v_start_1944_);
v___x_1964_ = lean_unsigned_to_nat(1u);
v___x_1965_ = lean_nat_add(v_start_1944_, v___x_1964_);
lean_dec(v_start_1944_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 1, v___x_1965_);
v___x_1967_ = v___x_1958_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_array_1943_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_2033_, 2, v_stop_1945_);
v___x_1967_ = v_reuseFailAlloc_2033_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
uint8_t v___x_1968_; 
v___x_1968_ = lean_nat_dec_lt(v_start_1961_, v_stop_1962_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1970_; 
lean_dec(v___x_1963_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 1, v___x_1967_);
v___x_1970_ = v___x_1941_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_fst_1939_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v___x_1967_);
v___x_1970_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1972_; 
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 1, v___x_1970_);
v___x_1972_ = v___x_1937_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_fst_1935_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1974_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 1, v___x_1972_);
v___x_1974_ = v___x_1933_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_fst_1931_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v___x_1972_);
v___x_1974_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
lean_object* v___x_1975_; 
v___x_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
return v___x_1975_;
}
}
}
}
else
{
lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2029_; 
lean_inc(v_stop_1962_);
lean_inc(v_start_1961_);
lean_inc_ref(v_array_1960_);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_fst_1939_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; lean_object* v_unused_2031_; lean_object* v_unused_2032_; 
v_unused_2030_ = lean_ctor_get(v_fst_1939_, 2);
lean_dec(v_unused_2030_);
v_unused_2031_ = lean_ctor_get(v_fst_1939_, 1);
lean_dec(v_unused_2031_);
v_unused_2032_ = lean_ctor_get(v_fst_1939_, 0);
lean_dec(v_unused_2032_);
v___x_1980_ = v_fst_1939_;
v_isShared_1981_ = v_isSharedCheck_2029_;
goto v_resetjp_1979_;
}
else
{
lean_dec(v_fst_1939_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2029_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v_array_1982_; lean_object* v_start_1983_; lean_object* v_stop_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
v_array_1982_ = lean_ctor_get(v_fst_1935_, 0);
v_start_1983_ = lean_ctor_get(v_fst_1935_, 1);
v_stop_1984_ = lean_ctor_get(v_fst_1935_, 2);
v___x_1985_ = lean_array_fget(v_array_1960_, v_start_1961_);
v___x_1986_ = lean_nat_add(v_start_1961_, v___x_1964_);
lean_dec(v_start_1961_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 1, v___x_1986_);
v___x_1988_ = v___x_1980_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_array_1960_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v___x_1986_);
lean_ctor_set(v_reuseFailAlloc_2028_, 2, v_stop_1962_);
v___x_1988_ = v_reuseFailAlloc_2028_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
uint8_t v___x_1989_; 
v___x_1989_ = lean_nat_dec_lt(v_start_1983_, v_stop_1984_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1991_; 
lean_dec(v___x_1985_);
lean_dec(v___x_1963_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 1, v___x_1967_);
lean_ctor_set(v___x_1941_, 0, v___x_1988_);
v___x_1991_ = v___x_1941_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v___x_1967_);
v___x_1991_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1993_; 
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 1, v___x_1991_);
v___x_1993_ = v___x_1937_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_fst_1935_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1995_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 1, v___x_1993_);
v___x_1995_ = v___x_1933_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_fst_1931_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1996_; 
v___x_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
return v___x_1996_;
}
}
}
}
else
{
lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2024_; 
lean_inc(v_stop_1984_);
lean_inc(v_start_1983_);
lean_inc_ref(v_array_1982_);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_fst_1935_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; lean_object* v_unused_2026_; lean_object* v_unused_2027_; 
v_unused_2025_ = lean_ctor_get(v_fst_1935_, 2);
lean_dec(v_unused_2025_);
v_unused_2026_ = lean_ctor_get(v_fst_1935_, 1);
lean_dec(v_unused_2026_);
v_unused_2027_ = lean_ctor_get(v_fst_1935_, 0);
lean_dec(v_unused_2027_);
v___x_2001_ = v_fst_1935_;
v_isShared_2002_ = v_isSharedCheck_2024_;
goto v_resetjp_2000_;
}
else
{
lean_dec(v_fst_1935_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2024_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v_a_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2007_; 
v_a_2003_ = lean_array_uget_borrowed(v_as_1921_, v_i_1923_);
v___x_2004_ = lean_array_fget(v_array_1982_, v_start_1983_);
v___x_2005_ = lean_nat_add(v_start_1983_, v___x_1964_);
lean_dec(v_start_1983_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 1, v___x_2005_);
v___x_2007_ = v___x_2001_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_array_1982_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v_stop_1984_);
v___x_2007_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2012_; 
lean_inc(v_a_2003_);
v___x_2008_ = l_Lean_Expr_app___override(v___x_2004_, v_a_2003_);
v___x_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_1985_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0___redArg(v_fst_1931_, v___x_1963_, v___x_2009_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 1, v___x_1967_);
lean_ctor_set(v___x_1941_, 0, v___x_1988_);
v___x_2012_ = v___x_1941_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___x_1967_);
v___x_2012_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2014_; 
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 1, v___x_2012_);
lean_ctor_set(v___x_1937_, 0, v___x_2007_);
v___x_2014_ = v___x_1937_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2016_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 1, v___x_2014_);
lean_ctor_set(v___x_1933_, 0, v___x_2010_);
v___x_2016_ = v___x_1933_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
size_t v___x_2017_; size_t v___x_2018_; 
v___x_2017_ = ((size_t)1ULL);
v___x_2018_ = lean_usize_add(v_i_1923_, v___x_2017_);
v_i_1923_ = v___x_2018_;
v_b_1924_ = v___x_2016_;
goto _start;
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__3___redArg___boxed(lean_object* v_as_2044_, lean_object* v_sz_2045_, lean_object* v_i_2046_, lean_object* v_b_2047_, lean_object* v___y_2048_){
_start:
{
size_t v_sz_boxed_2049_; size_t v_i_boxed_2050_; lean_object* v_res_2051_; 
v_sz_boxed_2049_ = lean_unbox_usize(v_sz_2045_);
lean_dec(v_sz_2045_);
v_i_boxed_2050_ = lean_unbox_usize(v_i_2046_);
lean_dec(v_i_2046_);
v_res_2051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__3___redArg(v_as_2044_, v_sz_boxed_2049_, v_i_boxed_2050_, v_b_2047_);
lean_dec_ref(v_as_2044_);
return v_res_2051_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2052_ = lean_box(0);
v___x_2053_ = lean_unsigned_to_nat(16u);
v___x_2054_ = lean_mk_array(v___x_2053_, v___x_2052_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__0(lean_object* v___x_2055_, lean_object* v_fst_2056_, lean_object* v_args_2057_, lean_object* v___x_2058_, lean_object* v___x_2059_, size_t v___x_2060_, lean_object* v_value_2061_, lean_object* v_a_2062_, uint8_t v___x_2063_, lean_object* v_name_2064_, lean_object* v_source_2065_, lean_object* v_boundSorts_2066_, lean_object* v_memHypDisjs_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; size_t v_sz_2085_; lean_object* v___x_2086_; 
v___x_2077_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__0___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__0___closed__0);
lean_inc_n(v___x_2055_, 2);
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2055_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = lean_array_get_size(v_fst_2056_);
v___x_2080_ = l_Array_toSubarray___redArg(v_fst_2056_, v___x_2055_, v___x_2079_);
lean_inc_ref(v_args_2057_);
v___x_2081_ = l_Array_toSubarray___redArg(v_args_2057_, v___x_2055_, v___x_2058_);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2059_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2080_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
v___x_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2078_);
lean_ctor_set(v___x_2084_, 1, v___x_2083_);
v_sz_2085_ = lean_array_size(v_memHypDisjs_2067_);
v___x_2086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__3___redArg(v_memHypDisjs_2067_, v_sz_2085_, v___x_2060_, v___x_2084_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v_fst_2088_; lean_object* v_predInfo_2089_; lean_object* v_sortInfo_2090_; lean_object* v_sortMap_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
lean_dec_ref_known(v___x_2086_, 1);
v_fst_2088_ = lean_ctor_get(v_a_2087_, 0);
lean_inc(v_fst_2088_);
lean_dec(v_a_2087_);
v_predInfo_2089_ = lean_ctor_get(v___y_2068_, 0);
v_sortInfo_2090_ = lean_ctor_get(v___y_2068_, 1);
v_sortMap_2091_ = lean_ctor_get(v___y_2068_, 2);
v___x_2092_ = l_Lean_mkAppN(v_value_2061_, v_args_2057_);
lean_inc_ref(v_sortMap_2091_);
lean_inc_ref(v_sortInfo_2090_);
lean_inc_ref(v_predInfo_2089_);
v___x_2093_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2093_, 0, v_predInfo_2089_);
lean_ctor_set(v___x_2093_, 1, v_sortInfo_2090_);
lean_ctor_set(v___x_2093_, 2, v_sortMap_2091_);
lean_ctor_set(v___x_2093_, 3, v_fst_2088_);
v___x_2094_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_translateProp(v_a_2062_, v___x_2092_, v___x_2093_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec_ref_known(v___x_2093_, 4);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v_fst_2096_; lean_object* v_snd_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2135_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v_fst_2096_ = lean_ctor_get(v_a_2095_, 0);
v_snd_2097_ = lean_ctor_get(v_a_2095_, 1);
v_isSharedCheck_2135_ = !lean_is_exclusive(v_a_2095_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2099_ = v_a_2095_;
v_isShared_2100_ = v_isSharedCheck_2135_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_snd_2097_);
lean_inc(v_fst_2096_);
lean_dec(v_a_2095_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2135_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = l_Array_append___redArg(v_args_2057_, v_memHypDisjs_2067_);
lean_inc_ref(v___x_2101_);
v___x_2102_ = l_Lean_Meta_Sym_mkForallFVarsS(v___x_2101_, v_fst_2096_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; uint8_t v___x_2104_; uint8_t v___x_2105_; lean_object* v___x_2106_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2102_, 1);
v___x_2104_ = 0;
v___x_2105_ = 1;
v___x_2106_ = l_Lean_Meta_mkLambdaFVars(v___x_2101_, v_snd_2097_, v___x_2104_, v___x_2063_, v___x_2104_, v___x_2063_, v___x_2105_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec_ref(v___x_2101_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2118_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2109_ = v___x_2106_;
v_isShared_2110_ = v_isSharedCheck_2118_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2118_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2111_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2111_, 0, v_name_2064_);
lean_ctor_set(v___x_2111_, 1, v_a_2103_);
lean_ctor_set(v___x_2111_, 2, v_a_2107_);
lean_ctor_set(v___x_2111_, 3, v_source_2065_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 1, v_boundSorts_2066_);
lean_ctor_set(v___x_2099_, 0, v___x_2111_);
v___x_2113_ = v___x_2099_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_boundSorts_2066_);
v___x_2113_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2115_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2113_);
v___x_2115_ = v___x_2109_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec(v_a_2103_);
lean_del_object(v___x_2099_);
lean_dec_ref(v_boundSorts_2066_);
lean_dec(v_source_2065_);
lean_dec(v_name_2064_);
v_a_2119_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2106_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2106_);
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
lean_dec_ref(v___x_2101_);
lean_del_object(v___x_2099_);
lean_dec(v_snd_2097_);
lean_dec_ref(v_boundSorts_2066_);
lean_dec(v_source_2065_);
lean_dec(v_name_2064_);
v_a_2127_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2102_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2102_);
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
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec_ref(v_boundSorts_2066_);
lean_dec(v_source_2065_);
lean_dec(v_name_2064_);
lean_dec_ref(v_args_2057_);
v_a_2136_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2094_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2094_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec_ref(v_boundSorts_2066_);
lean_dec(v_source_2065_);
lean_dec(v_name_2064_);
lean_dec_ref(v_a_2062_);
lean_dec_ref(v_value_2061_);
lean_dec_ref(v_args_2057_);
v_a_2144_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2086_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2086_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__0___boxed(lean_object** _args){
lean_object* v___x_2152_ = _args[0];
lean_object* v_fst_2153_ = _args[1];
lean_object* v_args_2154_ = _args[2];
lean_object* v___x_2155_ = _args[3];
lean_object* v___x_2156_ = _args[4];
lean_object* v___x_2157_ = _args[5];
lean_object* v_value_2158_ = _args[6];
lean_object* v_a_2159_ = _args[7];
lean_object* v___x_2160_ = _args[8];
lean_object* v_name_2161_ = _args[9];
lean_object* v_source_2162_ = _args[10];
lean_object* v_boundSorts_2163_ = _args[11];
lean_object* v_memHypDisjs_2164_ = _args[12];
lean_object* v___y_2165_ = _args[13];
lean_object* v___y_2166_ = _args[14];
lean_object* v___y_2167_ = _args[15];
lean_object* v___y_2168_ = _args[16];
lean_object* v___y_2169_ = _args[17];
lean_object* v___y_2170_ = _args[18];
lean_object* v___y_2171_ = _args[19];
lean_object* v___y_2172_ = _args[20];
lean_object* v___y_2173_ = _args[21];
_start:
{
size_t v___x_21288__boxed_2174_; uint8_t v___x_21290__boxed_2175_; lean_object* v_res_2176_; 
v___x_21288__boxed_2174_ = lean_unbox_usize(v___x_2157_);
lean_dec(v___x_2157_);
v___x_21290__boxed_2175_ = lean_unbox(v___x_2160_);
v_res_2176_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__0(v___x_2152_, v_fst_2153_, v_args_2154_, v___x_2155_, v___x_2156_, v___x_21288__boxed_2174_, v_value_2158_, v_a_2159_, v___x_21290__boxed_2175_, v_name_2161_, v_source_2162_, v_boundSorts_2163_, v_memHypDisjs_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec_ref(v_memHypDisjs_2164_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__2(lean_object* v_as_2177_, size_t v_sz_2178_, size_t v_i_2179_, lean_object* v_b_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
uint8_t v___x_2190_; 
v___x_2190_ = lean_usize_dec_lt(v_i_2179_, v_sz_2178_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; 
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v_b_2180_);
return v___x_2191_;
}
else
{
lean_object* v_snd_2192_; lean_object* v_snd_2193_; lean_object* v_fst_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2260_; 
v_snd_2192_ = lean_ctor_get(v_b_2180_, 1);
lean_inc(v_snd_2192_);
v_snd_2193_ = lean_ctor_get(v_snd_2192_, 1);
lean_inc(v_snd_2193_);
v_fst_2194_ = lean_ctor_get(v_b_2180_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v_b_2180_);
if (v_isSharedCheck_2260_ == 0)
{
lean_object* v_unused_2261_; 
v_unused_2261_ = lean_ctor_get(v_b_2180_, 1);
lean_dec(v_unused_2261_);
v___x_2196_ = v_b_2180_;
v_isShared_2197_ = v_isSharedCheck_2260_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_fst_2194_);
lean_dec(v_b_2180_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2260_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v_fst_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2258_; 
v_fst_2198_ = lean_ctor_get(v_snd_2192_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v_snd_2192_);
if (v_isSharedCheck_2258_ == 0)
{
lean_object* v_unused_2259_; 
v_unused_2259_ = lean_ctor_get(v_snd_2192_, 1);
lean_dec(v_unused_2259_);
v___x_2200_ = v_snd_2192_;
v_isShared_2201_ = v_isSharedCheck_2258_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_fst_2198_);
lean_dec(v_snd_2192_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2258_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v_array_2202_; lean_object* v_start_2203_; lean_object* v_stop_2204_; uint8_t v___x_2205_; 
v_array_2202_ = lean_ctor_get(v_snd_2193_, 0);
v_start_2203_ = lean_ctor_get(v_snd_2193_, 1);
v_stop_2204_ = lean_ctor_get(v_snd_2193_, 2);
v___x_2205_ = lean_nat_dec_lt(v_start_2203_, v_stop_2204_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2207_; 
if (v_isShared_2201_ == 0)
{
v___x_2207_ = v___x_2200_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_fst_2198_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v_snd_2193_);
v___x_2207_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2209_; 
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 1, v___x_2207_);
v___x_2209_ = v___x_2196_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_fst_2194_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
lean_object* v___x_2210_; 
v___x_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
return v___x_2210_;
}
}
}
else
{
lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2254_; 
lean_inc(v_stop_2204_);
lean_inc(v_start_2203_);
lean_inc_ref(v_array_2202_);
v_isSharedCheck_2254_ = !lean_is_exclusive(v_snd_2193_);
if (v_isSharedCheck_2254_ == 0)
{
lean_object* v_unused_2255_; lean_object* v_unused_2256_; lean_object* v_unused_2257_; 
v_unused_2255_ = lean_ctor_get(v_snd_2193_, 2);
lean_dec(v_unused_2255_);
v_unused_2256_ = lean_ctor_get(v_snd_2193_, 1);
lean_dec(v_unused_2256_);
v_unused_2257_ = lean_ctor_get(v_snd_2193_, 0);
lean_dec(v_unused_2257_);
v___x_2214_ = v_snd_2193_;
v_isShared_2215_ = v_isSharedCheck_2254_;
goto v_resetjp_2213_;
}
else
{
lean_dec(v_snd_2193_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2254_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v_a_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2221_; 
v_a_2216_ = lean_array_uget_borrowed(v_as_2177_, v_i_2179_);
v___x_2217_ = lean_array_fget(v_array_2202_, v_start_2203_);
v___x_2218_ = lean_unsigned_to_nat(1u);
v___x_2219_ = lean_nat_add(v_start_2203_, v___x_2218_);
lean_dec(v_start_2203_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 1, v___x_2219_);
v___x_2221_ = v___x_2214_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_array_2202_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2253_, 2, v_stop_2204_);
v___x_2221_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
lean_object* v___x_2222_; 
lean_inc(v_a_2216_);
v___x_2222_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp(v_a_2216_, v___x_2217_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v_fst_2224_; lean_object* v_snd_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2244_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_a_2223_);
lean_dec_ref_known(v___x_2222_, 1);
v_fst_2224_ = lean_ctor_get(v_a_2223_, 0);
v_snd_2225_ = lean_ctor_get(v_a_2223_, 1);
v_isSharedCheck_2244_ = !lean_is_exclusive(v_a_2223_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2227_ = v_a_2223_;
v_isShared_2228_ = v_isSharedCheck_2244_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_snd_2225_);
lean_inc(v_fst_2224_);
lean_dec(v_a_2223_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2244_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = lean_box(0);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 1, v_fst_2224_);
lean_ctor_set(v___x_2227_, 0, v___x_2229_);
v___x_2231_ = v___x_2227_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_fst_2224_);
v___x_2231_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2232_ = lean_array_push(v_fst_2194_, v___x_2231_);
v___x_2233_ = lean_array_push(v_fst_2198_, v_snd_2225_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 1, v___x_2221_);
lean_ctor_set(v___x_2200_, 0, v___x_2233_);
v___x_2235_ = v___x_2200_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v___x_2221_);
v___x_2235_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2237_; 
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 1, v___x_2235_);
lean_ctor_set(v___x_2196_, 0, v___x_2232_);
v___x_2237_ = v___x_2196_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
size_t v___x_2238_; size_t v___x_2239_; 
v___x_2238_ = ((size_t)1ULL);
v___x_2239_ = lean_usize_add(v_i_2179_, v___x_2238_);
v_i_2179_ = v___x_2239_;
v_b_2180_ = v___x_2237_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_dec_ref(v___x_2221_);
lean_del_object(v___x_2200_);
lean_dec(v_fst_2198_);
lean_del_object(v___x_2196_);
lean_dec(v_fst_2194_);
v_a_2245_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2222_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2222_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__2___boxed(lean_object* v_as_2262_, lean_object* v_sz_2263_, lean_object* v_i_2264_, lean_object* v_b_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
size_t v_sz_boxed_2275_; size_t v_i_boxed_2276_; lean_object* v_res_2277_; 
v_sz_boxed_2275_ = lean_unbox_usize(v_sz_2263_);
lean_dec(v_sz_2263_);
v_i_boxed_2276_ = lean_unbox_usize(v_i_2264_);
lean_dec(v_i_2264_);
v_res_2277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__2(v_as_2262_, v_sz_boxed_2275_, v_i_boxed_2276_, v_b_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec_ref(v_as_2262_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__11(size_t v_sz_2278_, size_t v_i_2279_, lean_object* v_bs_2280_){
_start:
{
uint8_t v___x_2281_; 
v___x_2281_ = lean_usize_dec_lt(v_i_2279_, v_sz_2278_);
if (v___x_2281_ == 0)
{
return v_bs_2280_;
}
else
{
lean_object* v_v_2282_; lean_object* v_fst_2283_; lean_object* v_snd_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2300_; 
v_v_2282_ = lean_array_uget(v_bs_2280_, v_i_2279_);
v_fst_2283_ = lean_ctor_get(v_v_2282_, 0);
v_snd_2284_ = lean_ctor_get(v_v_2282_, 1);
v_isSharedCheck_2300_ = !lean_is_exclusive(v_v_2282_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2286_ = v_v_2282_;
v_isShared_2287_ = v_isSharedCheck_2300_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_snd_2284_);
lean_inc(v_fst_2283_);
lean_dec(v_v_2282_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2300_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2288_; lean_object* v_bs_x27_2289_; uint8_t v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2293_; 
v___x_2288_ = lean_unsigned_to_nat(0u);
v_bs_x27_2289_ = lean_array_uset(v_bs_2280_, v_i_2279_, v___x_2288_);
v___x_2290_ = 0;
v___x_2291_ = lean_box(v___x_2290_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2291_);
v___x_2293_ = v___x_2286_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2291_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_snd_2284_);
v___x_2293_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
lean_object* v___x_2294_; size_t v___x_2295_; size_t v___x_2296_; lean_object* v___x_2297_; 
v___x_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2294_, 0, v_fst_2283_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
v___x_2295_ = ((size_t)1ULL);
v___x_2296_ = lean_usize_add(v_i_2279_, v___x_2295_);
v___x_2297_ = lean_array_uset(v_bs_x27_2289_, v_i_2279_, v___x_2294_);
v_i_2279_ = v___x_2296_;
v_bs_2280_ = v___x_2297_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__11___boxed(lean_object* v_sz_2301_, lean_object* v_i_2302_, lean_object* v_bs_2303_){
_start:
{
size_t v_sz_boxed_2304_; size_t v_i_boxed_2305_; lean_object* v_res_2306_; 
v_sz_boxed_2304_ = lean_unbox_usize(v_sz_2301_);
lean_dec(v_sz_2301_);
v_i_boxed_2305_ = lean_unbox_usize(v_i_2302_);
lean_dec(v_i_2302_);
v_res_2306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__11(v_sz_boxed_2304_, v_i_boxed_2305_, v_bs_2303_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14_spec__15___redArg___lam__0(lean_object* v_k_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v_b_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v___x_2318_; 
lean_inc(v___y_2316_);
lean_inc_ref(v___y_2315_);
lean_inc(v___y_2314_);
lean_inc_ref(v___y_2313_);
lean_inc(v___y_2311_);
lean_inc_ref(v___y_2310_);
lean_inc(v___y_2309_);
lean_inc_ref(v___y_2308_);
v___x_2318_ = lean_apply_10(v_k_2307_, v_b_2312_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, lean_box(0));
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14_spec__15___redArg___lam__0___boxed(lean_object* v_k_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v_b_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14_spec__15___redArg___lam__0(v_k_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v_b_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14_spec__15___redArg(lean_object* v_name_2331_, uint8_t v_bi_2332_, lean_object* v_type_2333_, lean_object* v_k_2334_, uint8_t v_kind_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v___f_2345_; lean_object* v___x_2346_; 
lean_inc(v___y_2339_);
lean_inc_ref(v___y_2338_);
lean_inc(v___y_2337_);
lean_inc_ref(v___y_2336_);
v___f_2345_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14_spec__15___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2345_, 0, v_k_2334_);
lean_closure_set(v___f_2345_, 1, v___y_2336_);
lean_closure_set(v___f_2345_, 2, v___y_2337_);
lean_closure_set(v___f_2345_, 3, v___y_2338_);
lean_closure_set(v___f_2345_, 4, v___y_2339_);
v___x_2346_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2331_, v_bi_2332_, v_type_2333_, v___f_2345_, v_kind_2335_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
if (lean_obj_tag(v___x_2346_) == 0)
{
return v___x_2346_;
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2346_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2346_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14_spec__15___redArg___boxed(lean_object* v_name_2355_, lean_object* v_bi_2356_, lean_object* v_type_2357_, lean_object* v_k_2358_, lean_object* v_kind_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
uint8_t v_bi_boxed_2369_; uint8_t v_kind_boxed_2370_; lean_object* v_res_2371_; 
v_bi_boxed_2369_ = lean_unbox(v_bi_2356_);
v_kind_boxed_2370_ = lean_unbox(v_kind_2359_);
v_res_2371_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14_spec__15___redArg(v_name_2355_, v_bi_boxed_2369_, v_type_2357_, v_k_2358_, v_kind_boxed_2370_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14___lam__0(lean_object* v___x_2372_, lean_object* v___x_2373_, lean_object* v_a_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v___x_20590__overap_2384_; lean_object* v___x_2385_; 
v___x_20590__overap_2384_ = l_instInhabitedOfMonad___redArg(v___x_2372_, v___x_2373_);
lean_inc(v___y_2382_);
lean_inc_ref(v___y_2381_);
lean_inc(v___y_2380_);
lean_inc_ref(v___y_2379_);
lean_inc(v___y_2378_);
lean_inc_ref(v___y_2377_);
lean_inc(v___y_2376_);
lean_inc_ref(v___y_2375_);
v___x_2385_ = lean_apply_9(v___x_20590__overap_2384_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, lean_box(0));
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14___lam__0___boxed(lean_object* v___x_2386_, lean_object* v___x_2387_, lean_object* v_a_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14___lam__0(v___x_2386_, v___x_2387_, v_a_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec_ref(v_a_2388_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14___lam__1___boxed(lean_object* v_acc_2399_, lean_object* v_declInfos_2400_, lean_object* v_k_2401_, lean_object* v_kind_2402_, lean_object* v_x_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
uint8_t v_kind_boxed_2413_; lean_object* v_res_2414_; 
v_kind_boxed_2413_ = lean_unbox(v_kind_2402_);
v_res_2414_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14___lam__1(v_acc_2399_, v_declInfos_2400_, v_k_2401_, v_kind_boxed_2413_, v_x_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14(lean_object* v_declInfos_2415_, lean_object* v_k_2416_, uint8_t v_kind_2417_, lean_object* v_acc_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v_toApplicative_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2522_; 
v___x_2428_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__0);
v___x_2429_ = l_StateRefT_x27_instMonad___redArg(v___x_2428_);
v_toApplicative_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2522_ == 0)
{
lean_object* v_unused_2523_; 
v_unused_2523_ = lean_ctor_get(v___x_2429_, 1);
lean_dec(v_unused_2523_);
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2522_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_toApplicative_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2522_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v_toFunctor_2434_; lean_object* v_toSeq_2435_; lean_object* v_toSeqLeft_2436_; lean_object* v_toSeqRight_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2520_; 
v_toFunctor_2434_ = lean_ctor_get(v_toApplicative_2430_, 0);
v_toSeq_2435_ = lean_ctor_get(v_toApplicative_2430_, 2);
v_toSeqLeft_2436_ = lean_ctor_get(v_toApplicative_2430_, 3);
v_toSeqRight_2437_ = lean_ctor_get(v_toApplicative_2430_, 4);
v_isSharedCheck_2520_ = !lean_is_exclusive(v_toApplicative_2430_);
if (v_isSharedCheck_2520_ == 0)
{
lean_object* v_unused_2521_; 
v_unused_2521_ = lean_ctor_get(v_toApplicative_2430_, 1);
lean_dec(v_unused_2521_);
v___x_2439_ = v_toApplicative_2430_;
v_isShared_2440_ = v_isSharedCheck_2520_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_toSeqRight_2437_);
lean_inc(v_toSeqLeft_2436_);
lean_inc(v_toSeq_2435_);
lean_inc(v_toFunctor_2434_);
lean_dec(v_toApplicative_2430_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2520_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___f_2441_; lean_object* v___f_2442_; lean_object* v___f_2443_; lean_object* v___f_2444_; lean_object* v___x_2445_; lean_object* v___f_2446_; lean_object* v___f_2447_; lean_object* v___f_2448_; lean_object* v___x_2450_; 
v___f_2441_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__1));
v___f_2442_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__2));
lean_inc_ref(v_toFunctor_2434_);
v___f_2443_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2443_, 0, v_toFunctor_2434_);
v___f_2444_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2444_, 0, v_toFunctor_2434_);
v___x_2445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___f_2443_);
lean_ctor_set(v___x_2445_, 1, v___f_2444_);
v___f_2446_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2446_, 0, v_toSeqRight_2437_);
v___f_2447_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2447_, 0, v_toSeqLeft_2436_);
v___f_2448_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2448_, 0, v_toSeq_2435_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 4, v___f_2446_);
lean_ctor_set(v___x_2439_, 3, v___f_2447_);
lean_ctor_set(v___x_2439_, 2, v___f_2448_);
lean_ctor_set(v___x_2439_, 1, v___f_2441_);
lean_ctor_set(v___x_2439_, 0, v___x_2445_);
v___x_2450_ = v___x_2439_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2445_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v___f_2441_);
lean_ctor_set(v_reuseFailAlloc_2519_, 2, v___f_2448_);
lean_ctor_set(v_reuseFailAlloc_2519_, 3, v___f_2447_);
lean_ctor_set(v_reuseFailAlloc_2519_, 4, v___f_2446_);
v___x_2450_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
lean_object* v___x_2452_; 
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 1, v___f_2442_);
lean_ctor_set(v___x_2432_, 0, v___x_2450_);
v___x_2452_ = v___x_2432_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v___f_2442_);
v___x_2452_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; lean_object* v_toApplicative_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2516_; 
v___x_2453_ = l_StateRefT_x27_instMonad___redArg(v___x_2452_);
v_toApplicative_2454_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2516_ == 0)
{
lean_object* v_unused_2517_; 
v_unused_2517_ = lean_ctor_get(v___x_2453_, 1);
lean_dec(v_unused_2517_);
v___x_2456_ = v___x_2453_;
v_isShared_2457_ = v_isSharedCheck_2516_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_toApplicative_2454_);
lean_dec(v___x_2453_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2516_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v_toFunctor_2458_; lean_object* v_toSeq_2459_; lean_object* v_toSeqLeft_2460_; lean_object* v_toSeqRight_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2514_; 
v_toFunctor_2458_ = lean_ctor_get(v_toApplicative_2454_, 0);
v_toSeq_2459_ = lean_ctor_get(v_toApplicative_2454_, 2);
v_toSeqLeft_2460_ = lean_ctor_get(v_toApplicative_2454_, 3);
v_toSeqRight_2461_ = lean_ctor_get(v_toApplicative_2454_, 4);
v_isSharedCheck_2514_ = !lean_is_exclusive(v_toApplicative_2454_);
if (v_isSharedCheck_2514_ == 0)
{
lean_object* v_unused_2515_; 
v_unused_2515_ = lean_ctor_get(v_toApplicative_2454_, 1);
lean_dec(v_unused_2515_);
v___x_2463_ = v_toApplicative_2454_;
v_isShared_2464_ = v_isSharedCheck_2514_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_toSeqRight_2461_);
lean_inc(v_toSeqLeft_2460_);
lean_inc(v_toSeq_2459_);
lean_inc(v_toFunctor_2458_);
lean_dec(v_toApplicative_2454_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2514_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___f_2465_; lean_object* v___f_2466_; lean_object* v___f_2467_; lean_object* v___f_2468_; lean_object* v___x_2469_; lean_object* v___f_2470_; lean_object* v___f_2471_; lean_object* v___f_2472_; lean_object* v___x_2474_; 
v___f_2465_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__3));
v___f_2466_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1___closed__4));
lean_inc_ref(v_toFunctor_2458_);
v___f_2467_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2467_, 0, v_toFunctor_2458_);
v___f_2468_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2468_, 0, v_toFunctor_2458_);
v___x_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___f_2467_);
lean_ctor_set(v___x_2469_, 1, v___f_2468_);
v___f_2470_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2470_, 0, v_toSeqRight_2461_);
v___f_2471_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2471_, 0, v_toSeqLeft_2460_);
v___f_2472_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2472_, 0, v_toSeq_2459_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 4, v___f_2470_);
lean_ctor_set(v___x_2463_, 3, v___f_2471_);
lean_ctor_set(v___x_2463_, 2, v___f_2472_);
lean_ctor_set(v___x_2463_, 1, v___f_2465_);
lean_ctor_set(v___x_2463_, 0, v___x_2469_);
v___x_2474_ = v___x_2463_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v___f_2465_);
lean_ctor_set(v_reuseFailAlloc_2513_, 2, v___f_2472_);
lean_ctor_set(v_reuseFailAlloc_2513_, 3, v___f_2471_);
lean_ctor_set(v_reuseFailAlloc_2513_, 4, v___f_2470_);
v___x_2474_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
lean_object* v___x_2476_; 
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 1, v___f_2466_);
lean_ctor_set(v___x_2456_, 0, v___x_2474_);
v___x_2476_ = v___x_2456_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2474_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v___f_2466_);
v___x_2476_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
v___x_2477_ = l_StateRefT_x27_instMonad___redArg(v___x_2476_);
v___x_2478_ = l_ReaderT_instMonad___redArg(v___x_2477_);
v___x_2479_ = l_StateRefT_x27_instMonad___redArg(v___x_2478_);
v___x_2480_ = l_ReaderT_instMonad___redArg(v___x_2479_);
v___x_2481_ = lean_array_get_size(v_acc_2418_);
v___x_2482_ = lean_array_get_size(v_declInfos_2415_);
v___x_2483_ = lean_nat_dec_lt(v___x_2481_, v___x_2482_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; 
lean_dec_ref(v___x_2480_);
lean_dec_ref(v_declInfos_2415_);
lean_inc(v___y_2426_);
lean_inc_ref(v___y_2425_);
lean_inc(v___y_2424_);
lean_inc_ref(v___y_2423_);
lean_inc(v___y_2422_);
lean_inc_ref(v___y_2421_);
lean_inc(v___y_2420_);
lean_inc_ref(v___y_2419_);
v___x_2484_ = lean_apply_10(v_k_2416_, v_acc_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, lean_box(0));
return v___x_2484_;
}
else
{
lean_object* v___x_2485_; uint8_t v___x_2486_; lean_object* v___x_2487_; lean_object* v___f_2488_; lean_object* v___f_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v_snd_2494_; lean_object* v_fst_2495_; lean_object* v_fst_2496_; lean_object* v_snd_2497_; lean_object* v___x_2498_; lean_object* v___f_2499_; lean_object* v___x_2500_; 
v___x_2485_ = lean_box(0);
v___x_2486_ = 0;
v___x_2487_ = l_Lean_instInhabitedExpr;
v___f_2488_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14___lam__0___boxed), 12, 2);
lean_closure_set(v___f_2488_, 0, v___x_2480_);
lean_closure_set(v___f_2488_, 1, v___x_2487_);
v___f_2489_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2489_, 0, v___f_2488_);
v___x_2490_ = lean_box(v___x_2486_);
v___x_2491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2490_);
lean_ctor_set(v___x_2491_, 1, v___f_2489_);
v___x_2492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2485_);
lean_ctor_set(v___x_2492_, 1, v___x_2491_);
v___x_2493_ = lean_array_get(v___x_2492_, v_declInfos_2415_, v___x_2481_);
lean_dec_ref_known(v___x_2492_, 2);
v_snd_2494_ = lean_ctor_get(v___x_2493_, 1);
lean_inc(v_snd_2494_);
v_fst_2495_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_fst_2495_);
lean_dec(v___x_2493_);
v_fst_2496_ = lean_ctor_get(v_snd_2494_, 0);
lean_inc(v_fst_2496_);
v_snd_2497_ = lean_ctor_get(v_snd_2494_, 1);
lean_inc(v_snd_2497_);
lean_dec(v_snd_2494_);
v___x_2498_ = lean_box(v_kind_2417_);
lean_inc_ref(v_acc_2418_);
v___f_2499_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14___lam__1___boxed), 14, 4);
lean_closure_set(v___f_2499_, 0, v_acc_2418_);
lean_closure_set(v___f_2499_, 1, v_declInfos_2415_);
lean_closure_set(v___f_2499_, 2, v_k_2416_);
lean_closure_set(v___f_2499_, 3, v___x_2498_);
lean_inc(v___y_2426_);
lean_inc_ref(v___y_2425_);
lean_inc(v___y_2424_);
lean_inc_ref(v___y_2423_);
lean_inc(v___y_2422_);
lean_inc_ref(v___y_2421_);
lean_inc(v___y_2420_);
lean_inc_ref(v___y_2419_);
v___x_2500_ = lean_apply_10(v_snd_2497_, v_acc_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, lean_box(0));
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; uint8_t v___x_2502_; lean_object* v___x_2503_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_a_2501_);
lean_dec_ref_known(v___x_2500_, 1);
v___x_2502_ = lean_unbox(v_fst_2496_);
lean_dec(v_fst_2496_);
v___x_2503_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14_spec__15___redArg(v_fst_2495_, v___x_2502_, v_a_2501_, v___f_2499_, v_kind_2417_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
return v___x_2503_;
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_dec_ref(v___f_2499_);
lean_dec(v_fst_2496_);
lean_dec(v_fst_2495_);
v_a_2504_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2500_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2500_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14___lam__1(lean_object* v_acc_2524_, lean_object* v_declInfos_2525_, lean_object* v_k_2526_, uint8_t v_kind_2527_, lean_object* v_x_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_array_push(v_acc_2524_, v_x_2528_);
v___x_2539_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14(v_declInfos_2525_, v_k_2526_, v_kind_2527_, v___x_2538_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14___boxed(lean_object* v_declInfos_2540_, lean_object* v_k_2541_, lean_object* v_kind_2542_, lean_object* v_acc_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
uint8_t v_kind_boxed_2553_; lean_object* v_res_2554_; 
v_kind_boxed_2553_ = lean_unbox(v_kind_2542_);
v_res_2554_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14(v_declInfos_2540_, v_k_2541_, v_kind_boxed_2553_, v_acc_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12(lean_object* v_declInfos_2557_, lean_object* v_k_2558_, uint8_t v_kind_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12___closed__0));
v___x_2570_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14(v_declInfos_2557_, v_k_2558_, v_kind_2559_, v___x_2569_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12___boxed(lean_object* v_declInfos_2571_, lean_object* v_k_2572_, lean_object* v_kind_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
uint8_t v_kind_boxed_2583_; lean_object* v_res_2584_; 
v_kind_boxed_2583_ = lean_unbox(v_kind_2573_);
v_res_2584_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12(v_declInfos_2571_, v_k_2572_, v_kind_boxed_2583_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8(lean_object* v_declInfos_2585_, lean_object* v_k_2586_, uint8_t v_kind_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
size_t v_sz_2597_; size_t v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v_sz_2597_ = lean_array_size(v_declInfos_2585_);
v___x_2598_ = ((size_t)0ULL);
v___x_2599_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__11(v_sz_2597_, v___x_2598_, v_declInfos_2585_);
v___x_2600_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12(v___x_2599_, v_k_2586_, v_kind_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8___boxed(lean_object* v_declInfos_2601_, lean_object* v_k_2602_, lean_object* v_kind_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
uint8_t v_kind_boxed_2613_; lean_object* v_res_2614_; 
v_kind_boxed_2613_ = lean_unbox(v_kind_2603_);
v_res_2614_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8(v_declInfos_2601_, v_k_2602_, v_kind_boxed_2613_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__7___lam__0(lean_object* v_snd_2615_, lean_object* v_x_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v_snd_2615_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__7___lam__0___boxed(lean_object* v_snd_2627_, lean_object* v_x_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__7___lam__0(v_snd_2627_, v_x_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec_ref(v_x_2628_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__7(size_t v_sz_2639_, size_t v_i_2640_, lean_object* v_bs_2641_){
_start:
{
uint8_t v___x_2642_; 
v___x_2642_ = lean_usize_dec_lt(v_i_2640_, v_sz_2639_);
if (v___x_2642_ == 0)
{
return v_bs_2641_;
}
else
{
lean_object* v_v_2643_; lean_object* v_fst_2644_; lean_object* v_snd_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2659_; 
v_v_2643_ = lean_array_uget(v_bs_2641_, v_i_2640_);
v_fst_2644_ = lean_ctor_get(v_v_2643_, 0);
v_snd_2645_ = lean_ctor_get(v_v_2643_, 1);
v_isSharedCheck_2659_ = !lean_is_exclusive(v_v_2643_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2647_ = v_v_2643_;
v_isShared_2648_ = v_isSharedCheck_2659_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_snd_2645_);
lean_inc(v_fst_2644_);
lean_dec(v_v_2643_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2659_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; lean_object* v_bs_x27_2650_; lean_object* v___f_2651_; lean_object* v___x_2653_; 
v___x_2649_ = lean_unsigned_to_nat(0u);
v_bs_x27_2650_ = lean_array_uset(v_bs_2641_, v_i_2640_, v___x_2649_);
v___f_2651_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__7___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2651_, 0, v_snd_2645_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 1, v___f_2651_);
v___x_2653_ = v___x_2647_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_fst_2644_);
lean_ctor_set(v_reuseFailAlloc_2658_, 1, v___f_2651_);
v___x_2653_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
size_t v___x_2654_; size_t v___x_2655_; lean_object* v___x_2656_; 
v___x_2654_ = ((size_t)1ULL);
v___x_2655_ = lean_usize_add(v_i_2640_, v___x_2654_);
v___x_2656_ = lean_array_uset(v_bs_x27_2650_, v_i_2640_, v___x_2653_);
v_i_2640_ = v___x_2655_;
v_bs_2641_ = v___x_2656_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__7___boxed(lean_object* v_sz_2660_, lean_object* v_i_2661_, lean_object* v_bs_2662_){
_start:
{
size_t v_sz_boxed_2663_; size_t v_i_boxed_2664_; lean_object* v_res_2665_; 
v_sz_boxed_2663_ = lean_unbox_usize(v_sz_2660_);
lean_dec(v_sz_2660_);
v_i_boxed_2664_ = lean_unbox_usize(v_i_2661_);
lean_dec(v_i_2661_);
v_res_2665_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__7(v_sz_boxed_2663_, v_i_boxed_2664_, v_bs_2662_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4(lean_object* v_declInfos_2666_, lean_object* v_k_2667_, uint8_t v_kind_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
size_t v_sz_2678_; size_t v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v_sz_2678_ = lean_array_size(v_declInfos_2666_);
v___x_2679_ = ((size_t)0ULL);
v___x_2680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__7(v_sz_2678_, v___x_2679_, v_declInfos_2666_);
v___x_2681_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8(v___x_2680_, v_k_2667_, v_kind_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4___boxed(lean_object* v_declInfos_2682_, lean_object* v_k_2683_, lean_object* v_kind_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
uint8_t v_kind_boxed_2694_; lean_object* v_res_2695_; 
v_kind_boxed_2694_ = lean_unbox(v_kind_2684_);
v_res_2695_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4(v_declInfos_2682_, v_k_2683_, v_kind_boxed_2694_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
return v_res_2695_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2699_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__2));
v___x_2700_ = lean_unsigned_to_nat(4u);
v___x_2701_ = lean_unsigned_to_nat(176u);
v___x_2702_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__1));
v___x_2703_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__0));
v___x_2704_ = l_mkPanicMessageWithDecl(v___x_2703_, v___x_2702_, v___x_2701_, v___x_2700_, v___x_2699_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1(lean_object* v___x_2709_, lean_object* v_boundSorts_2710_, lean_object* v_value_2711_, lean_object* v_name_2712_, lean_object* v_source_2713_, lean_object* v_args_2714_, lean_object* v_body_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_Meta_Sym_shareCommon(v_body_2715_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2727_; uint8_t v___x_2728_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref_known(v___x_2725_, 1);
v___x_2727_ = lean_array_get_size(v_args_2714_);
v___x_2728_ = lean_nat_dec_eq(v___x_2727_, v___x_2709_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
lean_dec(v_a_2726_);
lean_dec_ref(v_args_2714_);
lean_dec(v_source_2713_);
lean_dec(v_name_2712_);
lean_dec_ref(v_value_2711_);
lean_dec_ref(v_boundSorts_2710_);
lean_dec(v___x_2709_);
v___x_2729_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__3);
v___x_2730_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__1(v___x_2729_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
return v___x_2730_;
}
else
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; size_t v_sz_2736_; size_t v___x_2737_; lean_object* v___x_2738_; 
v___x_2731_ = lean_unsigned_to_nat(0u);
v___x_2732_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___closed__4));
lean_inc_ref(v_boundSorts_2710_);
v___x_2733_ = l_Array_toSubarray___redArg(v_boundSorts_2710_, v___x_2731_, v___x_2709_);
lean_inc_ref(v___x_2733_);
v___x_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2732_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
v___x_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2732_);
lean_ctor_set(v___x_2735_, 1, v___x_2734_);
v_sz_2736_ = lean_array_size(v_args_2714_);
v___x_2737_ = ((size_t)0ULL);
v___x_2738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__2(v_args_2714_, v_sz_2736_, v___x_2737_, v___x_2735_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v_snd_2740_; lean_object* v_fst_2741_; lean_object* v_fst_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___f_2745_; uint8_t v___x_2746_; lean_object* v___x_2747_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_a_2739_);
lean_dec_ref_known(v___x_2738_, 1);
v_snd_2740_ = lean_ctor_get(v_a_2739_, 1);
lean_inc(v_snd_2740_);
v_fst_2741_ = lean_ctor_get(v_a_2739_, 0);
lean_inc(v_fst_2741_);
lean_dec(v_a_2739_);
v_fst_2742_ = lean_ctor_get(v_snd_2740_, 0);
lean_inc(v_fst_2742_);
lean_dec(v_snd_2740_);
v___x_2743_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___boxed__const__1));
v___x_2744_ = lean_box(v___x_2728_);
v___f_2745_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__0___boxed), 22, 12);
lean_closure_set(v___f_2745_, 0, v___x_2731_);
lean_closure_set(v___f_2745_, 1, v_fst_2742_);
lean_closure_set(v___f_2745_, 2, v_args_2714_);
lean_closure_set(v___f_2745_, 3, v___x_2727_);
lean_closure_set(v___f_2745_, 4, v___x_2733_);
lean_closure_set(v___f_2745_, 5, v___x_2743_);
lean_closure_set(v___f_2745_, 6, v_value_2711_);
lean_closure_set(v___f_2745_, 7, v_a_2726_);
lean_closure_set(v___f_2745_, 8, v___x_2744_);
lean_closure_set(v___f_2745_, 9, v_name_2712_);
lean_closure_set(v___f_2745_, 10, v_source_2713_);
lean_closure_set(v___f_2745_, 11, v_boundSorts_2710_);
v___x_2746_ = 0;
v___x_2747_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4(v_fst_2741_, v___f_2745_, v___x_2746_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
return v___x_2747_;
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
lean_dec_ref(v___x_2733_);
lean_dec(v_a_2726_);
lean_dec_ref(v_args_2714_);
lean_dec(v_source_2713_);
lean_dec(v_name_2712_);
lean_dec_ref(v_value_2711_);
lean_dec_ref(v_boundSorts_2710_);
v_a_2748_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2738_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2738_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2748_);
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
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_dec_ref(v_args_2714_);
lean_dec(v_source_2713_);
lean_dec(v_name_2712_);
lean_dec_ref(v_value_2711_);
lean_dec_ref(v_boundSorts_2710_);
lean_dec(v___x_2709_);
v_a_2756_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2725_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2725_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___boxed(lean_object* v___x_2764_, lean_object* v_boundSorts_2765_, lean_object* v_value_2766_, lean_object* v_name_2767_, lean_object* v_source_2768_, lean_object* v_args_2769_, lean_object* v_body_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1(v___x_2764_, v_boundSorts_2765_, v_value_2766_, v_name_2767_, v_source_2768_, v_args_2769_, v_body_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified(lean_object* v_hyp_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v_hyp_2791_; lean_object* v_boundSorts_2792_; lean_object* v_name_2793_; lean_object* v_type_2794_; lean_object* v_value_2795_; lean_object* v_source_2796_; lean_object* v___x_2797_; lean_object* v___f_2798_; lean_object* v___x_2799_; uint8_t v___x_2800_; lean_object* v___x_2801_; 
v_hyp_2791_ = lean_ctor_get(v_hyp_2781_, 0);
lean_inc_ref(v_hyp_2791_);
v_boundSorts_2792_ = lean_ctor_get(v_hyp_2781_, 1);
lean_inc_ref(v_boundSorts_2792_);
lean_dec_ref(v_hyp_2781_);
v_name_2793_ = lean_ctor_get(v_hyp_2791_, 0);
lean_inc(v_name_2793_);
v_type_2794_ = lean_ctor_get(v_hyp_2791_, 1);
lean_inc_ref(v_type_2794_);
v_value_2795_ = lean_ctor_get(v_hyp_2791_, 2);
lean_inc_ref(v_value_2795_);
v_source_2796_ = lean_ctor_get(v_hyp_2791_, 3);
lean_inc(v_source_2796_);
lean_dec_ref(v_hyp_2791_);
v___x_2797_ = lean_array_get_size(v_boundSorts_2792_);
v___f_2798_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___boxed), 16, 5);
lean_closure_set(v___f_2798_, 0, v___x_2797_);
lean_closure_set(v___f_2798_, 1, v_boundSorts_2792_);
lean_closure_set(v___f_2798_, 2, v_value_2795_);
lean_closure_set(v___f_2798_, 3, v_name_2793_);
lean_closure_set(v___f_2798_, 4, v_source_2796_);
v___x_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2797_);
v___x_2800_ = 0;
v___x_2801_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__5___redArg(v_type_2794_, v___x_2799_, v___f_2798_, v___x_2800_, v___x_2800_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___boxed(lean_object* v_hyp_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified(v_hyp_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_);
lean_dec(v_a_2810_);
lean_dec_ref(v_a_2809_);
lean_dec(v_a_2808_);
lean_dec_ref(v_a_2807_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0(lean_object* v_00_u03b2_2813_, lean_object* v_m_2814_, lean_object* v_a_2815_, lean_object* v_b_2816_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0___redArg(v_m_2814_, v_a_2815_, v_b_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__3(lean_object* v_as_2818_, size_t v_sz_2819_, size_t v_i_2820_, lean_object* v_b_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v___x_2831_; 
v___x_2831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__3___redArg(v_as_2818_, v_sz_2819_, v_i_2820_, v_b_2821_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__3___boxed(lean_object* v_as_2832_, lean_object* v_sz_2833_, lean_object* v_i_2834_, lean_object* v_b_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
size_t v_sz_boxed_2845_; size_t v_i_boxed_2846_; lean_object* v_res_2847_; 
v_sz_boxed_2845_ = lean_unbox_usize(v_sz_2833_);
lean_dec(v_sz_2833_);
v_i_boxed_2846_ = lean_unbox_usize(v_i_2834_);
lean_dec(v_i_2834_);
v_res_2847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__3(v_as_2832_, v_sz_boxed_2845_, v_i_boxed_2846_, v_b_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec_ref(v_as_2832_);
return v_res_2847_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__0(lean_object* v_00_u03b2_2848_, lean_object* v_a_2849_, lean_object* v_x_2850_){
_start:
{
uint8_t v___x_2851_; 
v___x_2851_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__0___redArg(v_a_2849_, v_x_2850_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2852_, lean_object* v_a_2853_, lean_object* v_x_2854_){
_start:
{
uint8_t v_res_2855_; lean_object* v_r_2856_; 
v_res_2855_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__0(v_00_u03b2_2852_, v_a_2853_, v_x_2854_);
lean_dec(v_x_2854_);
lean_dec_ref(v_a_2853_);
v_r_2856_ = lean_box(v_res_2855_);
return v_r_2856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__1(lean_object* v_00_u03b2_2857_, lean_object* v_data_2858_){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__1___redArg(v_data_2858_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__2(lean_object* v_00_u03b2_2860_, lean_object* v_a_2861_, lean_object* v_b_2862_, lean_object* v_x_2863_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__2___redArg(v_a_2861_, v_b_2862_, v_x_2863_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2865_, lean_object* v_i_2866_, lean_object* v_source_2867_, lean_object* v_target_2868_){
_start:
{
lean_object* v___x_2869_; 
v___x_2869_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__1_spec__4___redArg(v_i_2866_, v_source_2867_, v_target_2868_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_2870_, lean_object* v_x_2871_, lean_object* v_x_2872_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0_spec__1_spec__4_spec__8___redArg(v_x_2871_, v_x_2872_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14_spec__15(lean_object* v_00_u03b1_2874_, lean_object* v_name_2875_, uint8_t v_bi_2876_, lean_object* v_type_2877_, lean_object* v_k_2878_, uint8_t v_kind_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14_spec__15___redArg(v_name_2875_, v_bi_2876_, v_type_2877_, v_k_2878_, v_kind_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14_spec__15___boxed(lean_object* v_00_u03b1_2890_, lean_object* v_name_2891_, lean_object* v_bi_2892_, lean_object* v_type_2893_, lean_object* v_k_2894_, lean_object* v_kind_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
uint8_t v_bi_boxed_2905_; uint8_t v_kind_boxed_2906_; lean_object* v_res_2907_; 
v_bi_boxed_2905_ = lean_unbox(v_bi_2892_);
v_kind_boxed_2906_ = lean_unbox(v_kind_2895_);
v_res_2907_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__4_spec__8_spec__12_spec__14_spec__15(v_00_u03b1_2890_, v_name_2891_, v_bi_boxed_2905_, v_type_2893_, v_k_2894_, v_kind_boxed_2906_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__2___redArg(lean_object* v_msg_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_ref_2914_; lean_object* v___x_2915_; lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2924_; 
v_ref_2914_ = lean_ctor_get(v___y_2911_, 2);
v___x_2915_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__0_spec__0(v_msg_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
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
lean_inc(v_ref_2914_);
v___x_2920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2920_, 0, v_ref_2914_);
lean_ctor_set(v___x_2920_, 1, v_a_2916_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set_tag(v___x_2918_, 1);
lean_ctor_set(v___x_2918_, 0, v___x_2920_);
v___x_2922_ = v___x_2918_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2920_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__2___redArg___boxed(lean_object* v_msg_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__2___redArg(v_msg_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__0(lean_object* v_sortInfos_2932_, size_t v_sz_2933_, size_t v_i_2934_, lean_object* v_bs_2935_){
_start:
{
uint8_t v___x_2936_; 
v___x_2936_ = lean_usize_dec_lt(v_i_2934_, v_sz_2933_);
if (v___x_2936_ == 0)
{
return v_bs_2935_;
}
else
{
lean_object* v_v_2937_; lean_object* v___x_2938_; lean_object* v_toSortInfo_2939_; lean_object* v_level_2940_; lean_object* v___x_2941_; lean_object* v_bs_x27_2942_; size_t v___x_2943_; size_t v___x_2944_; lean_object* v___x_2945_; 
v_v_2937_ = lean_array_uget_borrowed(v_bs_2935_, v_i_2934_);
v___x_2938_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0(v_sortInfos_2932_, v_v_2937_);
v_toSortInfo_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc_ref(v_toSortInfo_2939_);
lean_dec_ref(v___x_2938_);
v_level_2940_ = lean_ctor_get(v_toSortInfo_2939_, 1);
lean_inc(v_level_2940_);
lean_dec_ref(v_toSortInfo_2939_);
v___x_2941_ = lean_unsigned_to_nat(0u);
v_bs_x27_2942_ = lean_array_uset(v_bs_2935_, v_i_2934_, v___x_2941_);
v___x_2943_ = ((size_t)1ULL);
v___x_2944_ = lean_usize_add(v_i_2934_, v___x_2943_);
v___x_2945_ = lean_array_uset(v_bs_x27_2942_, v_i_2934_, v_level_2940_);
v_i_2934_ = v___x_2944_;
v_bs_2935_ = v___x_2945_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__0___boxed(lean_object* v_sortInfos_2947_, lean_object* v_sz_2948_, lean_object* v_i_2949_, lean_object* v_bs_2950_){
_start:
{
size_t v_sz_boxed_2951_; size_t v_i_boxed_2952_; lean_object* v_res_2953_; 
v_sz_boxed_2951_ = lean_unbox_usize(v_sz_2948_);
lean_dec(v_sz_2948_);
v_i_boxed_2952_ = lean_unbox_usize(v_i_2949_);
lean_dec(v_i_2949_);
v_res_2953_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__0(v_sortInfos_2947_, v_sz_boxed_2951_, v_i_boxed_2952_, v_bs_2950_);
lean_dec_ref(v_sortInfos_2947_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__1___redArg(lean_object* v_sortInfos_2954_, lean_object* v_as_2955_, size_t v_sz_2956_, size_t v_i_2957_, lean_object* v_b_2958_){
_start:
{
uint8_t v___x_2960_; 
v___x_2960_ = lean_usize_dec_lt(v_i_2957_, v_sz_2956_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; 
v___x_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2961_, 0, v_b_2958_);
return v___x_2961_;
}
else
{
lean_object* v_fst_2962_; lean_object* v_snd_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2987_; 
v_fst_2962_ = lean_ctor_get(v_b_2958_, 0);
v_snd_2963_ = lean_ctor_get(v_b_2958_, 1);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_b_2958_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2965_ = v_b_2958_;
v_isShared_2966_ = v_isSharedCheck_2987_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_snd_2963_);
lean_inc(v_fst_2962_);
lean_dec(v_b_2958_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2987_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v_a_2967_; lean_object* v___x_2968_; lean_object* v_toSortInfo_2969_; lean_object* v_width_2970_; lean_object* v_elemList_2971_; lean_object* v_elemListLt_2972_; lean_object* v_type_2973_; lean_object* v_elements_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2982_; 
v_a_2967_ = lean_array_uget_borrowed(v_as_2955_, v_i_2957_);
v___x_2968_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateCtx_getMemProof_x3f_spec__0(v_sortInfos_2954_, v_a_2967_);
v_toSortInfo_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc_ref(v_toSortInfo_2969_);
v_width_2970_ = lean_ctor_get(v___x_2968_, 1);
lean_inc(v_width_2970_);
v_elemList_2971_ = lean_ctor_get(v___x_2968_, 4);
lean_inc_ref_n(v_elemList_2971_, 2);
v_elemListLt_2972_ = lean_ctor_get(v___x_2968_, 5);
lean_inc_ref(v_elemListLt_2972_);
lean_dec_ref(v___x_2968_);
v_type_2973_ = lean_ctor_get(v_toSortInfo_2969_, 0);
lean_inc_ref_n(v_type_2973_, 2);
v_elements_2974_ = lean_ctor_get(v_toSortInfo_2969_, 2);
lean_inc_ref(v_elements_2974_);
lean_dec_ref(v_toSortInfo_2969_);
v___x_2975_ = l_Lean_mkNatLit(v_width_2970_);
v___x_2976_ = l_Lean_instInhabitedExpr;
v___x_2977_ = lean_unsigned_to_nat(0u);
v___x_2978_ = lean_array_get(v___x_2976_, v_elements_2974_, v___x_2977_);
lean_dec_ref(v_elements_2974_);
lean_inc(v___x_2978_);
lean_inc_ref(v___x_2975_);
v___x_2979_ = l_Lean_mkApp4(v_fst_2962_, v_type_2973_, v___x_2975_, v_elemList_2971_, v___x_2978_);
v___x_2980_ = l_Lean_mkApp5(v_snd_2963_, v_type_2973_, v___x_2975_, v_elemList_2971_, v_elemListLt_2972_, v___x_2978_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 1, v___x_2980_);
lean_ctor_set(v___x_2965_, 0, v___x_2979_);
v___x_2982_ = v___x_2965_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2979_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v___x_2980_);
v___x_2982_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
size_t v___x_2983_; size_t v___x_2984_; 
v___x_2983_ = ((size_t)1ULL);
v___x_2984_ = lean_usize_add(v_i_2957_, v___x_2983_);
v_i_2957_ = v___x_2984_;
v_b_2958_ = v___x_2982_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__1___redArg___boxed(lean_object* v_sortInfos_2988_, lean_object* v_as_2989_, lean_object* v_sz_2990_, lean_object* v_i_2991_, lean_object* v_b_2992_, lean_object* v___y_2993_){
_start:
{
size_t v_sz_boxed_2994_; size_t v_i_boxed_2995_; lean_object* v_res_2996_; 
v_sz_boxed_2994_ = lean_unbox_usize(v_sz_2990_);
lean_dec(v_sz_2990_);
v_i_boxed_2995_ = lean_unbox_usize(v_i_2991_);
lean_dec(v_i_2991_);
v_res_2996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__1___redArg(v_sortInfos_2988_, v_as_2989_, v_sz_boxed_2994_, v_i_boxed_2995_, v_b_2992_);
lean_dec_ref(v_as_2989_);
lean_dec_ref(v_sortInfos_2988_);
return v_res_2996_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__1));
v___x_3001_ = l_Lean_stringToMessageData(v___x_3000_);
return v___x_3001_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__4(void){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__3));
v___x_3004_ = l_Lean_stringToMessageData(v___x_3003_);
return v___x_3004_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__5(void){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3005_ = l_Std_Tactic_BVDecide_EPR_BitVec_maxToBvPredArity;
v___x_3006_ = l_Nat_reprFast(v___x_3005_);
return v___x_3006_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__6(void){
_start:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__5, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__5_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__5);
v___x_3008_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
return v___x_3008_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__7(void){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3009_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__6, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__6_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__6);
v___x_3010_ = l_Lean_MessageData_ofFormat(v___x_3009_);
return v___x_3010_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__8(void){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3011_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__7, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__7_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__7);
v___x_3012_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__4, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__4_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__4);
v___x_3013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
lean_ctor_set(v___x_3013_, 1, v___x_3011_);
return v___x_3013_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__10(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__9));
v___x_3016_ = l_Lean_stringToMessageData(v___x_3015_);
return v___x_3016_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__11(void){
_start:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3017_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__10, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__10_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__10);
v___x_3018_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__8, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__8_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__8);
v___x_3019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
lean_ctor_set(v___x_3019_, 1, v___x_3017_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3(lean_object* v_sortInfos_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__0));
if (lean_obj_tag(v_a_3021_) == 0)
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3031_, 0, v_a_3022_);
v___x_3032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3031_);
return v___x_3032_;
}
else
{
lean_object* v_value_3033_; lean_object* v_key_3034_; lean_object* v_tail_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3139_; 
v_value_3033_ = lean_ctor_get(v_a_3021_, 1);
v_key_3034_ = lean_ctor_get(v_a_3021_, 0);
v_tail_3035_ = lean_ctor_get(v_a_3021_, 2);
v_isSharedCheck_3139_ = !lean_is_exclusive(v_a_3021_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3037_ = v_a_3021_;
v_isShared_3038_ = v_isSharedCheck_3139_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_tail_3035_);
lean_inc(v_value_3033_);
lean_inc(v_key_3034_);
lean_dec(v_a_3021_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3139_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v_argumentSorts_3039_; uint8_t v_encoding_3040_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___x_3124_; lean_object* v___x_3125_; uint8_t v___x_3126_; 
v_argumentSorts_3039_ = lean_ctor_get(v_value_3033_, 0);
v_encoding_3040_ = lean_ctor_get_uint8(v_value_3033_, sizeof(void*)*1);
v___x_3124_ = l_Std_Tactic_BVDecide_EPR_BitVec_maxToBvPredArity;
v___x_3125_ = lean_array_get_size(v_argumentSorts_3039_);
v___x_3126_ = lean_nat_dec_lt(v___x_3124_, v___x_3125_);
if (v___x_3126_ == 0)
{
v___y_3105_ = v___y_3023_;
v___y_3106_ = v___y_3024_;
v___y_3107_ = v___y_3025_;
v___y_3108_ = v___y_3026_;
v___y_3109_ = v___y_3027_;
v___y_3110_ = v___y_3028_;
goto v___jp_3104_;
}
else
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_del_object(v___x_3037_);
lean_dec(v_tail_3035_);
lean_dec(v_value_3033_);
lean_dec_ref(v_a_3022_);
v___x_3127_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__11, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__11_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__11);
v___x_3128_ = l_Lean_MessageData_ofExpr(v_key_3034_);
v___x_3129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3127_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
v___x_3130_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__2___redArg(v___x_3129_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3130_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3130_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
v___jp_3041_:
{
lean_object* v_fst_3049_; lean_object* v_snd_3050_; size_t v_sz_3051_; size_t v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v_fst_3049_ = lean_ctor_get(v___y_3048_, 0);
v_snd_3050_ = lean_ctor_get(v___y_3048_, 1);
v_sz_3051_ = lean_array_size(v_argumentSorts_3039_);
v___x_3052_ = ((size_t)0ULL);
lean_inc_ref(v_argumentSorts_3039_);
v___x_3053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__0(v_sortInfos_3020_, v_sz_3051_, v___x_3052_, v_argumentSorts_3039_);
v___x_3054_ = lean_array_to_list(v___x_3053_);
lean_inc(v___x_3054_);
lean_inc(v_fst_3049_);
v___x_3055_ = l_Lean_mkConst(v_fst_3049_, v___x_3054_);
lean_inc(v_snd_3050_);
v___x_3056_ = l_Lean_mkConst(v_snd_3050_, v___x_3054_);
v___x_3057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3055_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
v___x_3058_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__1___redArg(v_sortInfos_3020_, v_argumentSorts_3039_, v_sz_3051_, v___x_3052_, v___x_3057_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v_fst_3060_; lean_object* v_snd_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref_known(v___x_3058_, 1);
v_fst_3060_ = lean_ctor_get(v_a_3059_, 0);
lean_inc(v_fst_3060_);
v_snd_3061_ = lean_ctor_get(v_a_3059_, 1);
lean_inc(v_snd_3061_);
lean_dec(v_a_3059_);
lean_inc(v_key_3034_);
v___x_3062_ = l_Lean_Expr_app___override(v_fst_3060_, v_key_3034_);
v___x_3063_ = l_Lean_Meta_Sym_shareCommonInc(v___x_3062_, v___y_3043_, v___y_3046_, v___y_3047_, v___y_3045_, v___y_3044_, v___y_3042_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; lean_object* v___x_3065_; lean_object* v___x_3067_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
lean_inc(v_a_3064_);
lean_dec_ref_known(v___x_3063_, 1);
lean_inc(v_key_3034_);
v___x_3065_ = l_Lean_Expr_app___override(v_snd_3061_, v_key_3034_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set_tag(v___x_3037_, 0);
lean_ctor_set(v___x_3037_, 2, v___x_3065_);
lean_ctor_set(v___x_3037_, 1, v_a_3064_);
lean_ctor_set(v___x_3037_, 0, v_value_3033_);
v___x_3067_ = v___x_3037_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_value_3033_);
lean_ctor_set(v_reuseFailAlloc_3070_, 1, v_a_3064_);
lean_ctor_set(v_reuseFailAlloc_3070_, 2, v___x_3065_);
v___x_3067_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0___redArg(v_a_3022_, v_key_3034_, v___x_3067_);
v_a_3021_ = v_tail_3035_;
v_a_3022_ = v___x_3068_;
goto _start;
}
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec(v_snd_3061_);
lean_del_object(v___x_3037_);
lean_dec(v_tail_3035_);
lean_dec(v_key_3034_);
lean_dec(v_value_3033_);
lean_dec_ref(v_a_3022_);
v_a_3071_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_3063_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_3063_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_del_object(v___x_3037_);
lean_dec(v_tail_3035_);
lean_dec(v_key_3034_);
lean_dec(v_value_3033_);
lean_dec_ref(v_a_3022_);
v_a_3079_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_3058_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3058_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
v___jp_3087_:
{
if (v_encoding_3040_ == 0)
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3094_ = l_Std_Tactic_BVDecide_EPR_BitVec_toBvPredPropDecls;
v___x_3095_ = lean_array_get_size(v_argumentSorts_3039_);
v___x_3096_ = lean_unsigned_to_nat(1u);
v___x_3097_ = lean_nat_sub(v___x_3095_, v___x_3096_);
v___x_3098_ = lean_array_get_borrowed(v___x_3030_, v___x_3094_, v___x_3097_);
lean_dec(v___x_3097_);
v___y_3042_ = v___y_3093_;
v___y_3043_ = v___y_3088_;
v___y_3044_ = v___y_3092_;
v___y_3045_ = v___y_3091_;
v___y_3046_ = v___y_3089_;
v___y_3047_ = v___y_3090_;
v___y_3048_ = v___x_3098_;
goto v___jp_3041_;
}
else
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3099_ = l_Std_Tactic_BVDecide_EPR_BitVec_toBvPredBoolDecls;
v___x_3100_ = lean_array_get_size(v_argumentSorts_3039_);
v___x_3101_ = lean_unsigned_to_nat(1u);
v___x_3102_ = lean_nat_sub(v___x_3100_, v___x_3101_);
v___x_3103_ = lean_array_get_borrowed(v___x_3030_, v___x_3099_, v___x_3102_);
lean_dec(v___x_3102_);
v___y_3042_ = v___y_3093_;
v___y_3043_ = v___y_3088_;
v___y_3044_ = v___y_3092_;
v___y_3045_ = v___y_3091_;
v___y_3046_ = v___y_3089_;
v___y_3047_ = v___y_3090_;
v___y_3048_ = v___x_3103_;
goto v___jp_3041_;
}
}
v___jp_3104_:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; uint8_t v___x_3113_; 
v___x_3111_ = lean_array_get_size(v_argumentSorts_3039_);
v___x_3112_ = lean_unsigned_to_nat(0u);
v___x_3113_ = lean_nat_dec_eq(v___x_3111_, v___x_3112_);
if (v___x_3113_ == 0)
{
v___y_3088_ = v___y_3105_;
v___y_3089_ = v___y_3106_;
v___y_3090_ = v___y_3107_;
v___y_3091_ = v___y_3108_;
v___y_3092_ = v___y_3109_;
v___y_3093_ = v___y_3110_;
goto v___jp_3087_;
}
else
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_del_object(v___x_3037_);
lean_dec(v_tail_3035_);
lean_dec(v_key_3034_);
lean_dec(v_value_3033_);
lean_dec_ref(v_a_3022_);
v___x_3114_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__2, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__2_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___closed__2);
v___x_3115_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__2___redArg(v___x_3114_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_3115_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3115_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3___boxed(lean_object* v_sortInfos_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3(v_sortInfos_3140_, v_a_3141_, v_a_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec_ref(v_sortInfos_3140_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__4(lean_object* v_sortInfos_3151_, lean_object* v_as_3152_, size_t v_sz_3153_, size_t v_i_3154_, lean_object* v_b_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
uint8_t v___x_3163_; 
v___x_3163_ = lean_usize_dec_lt(v_i_3154_, v_sz_3153_);
if (v___x_3163_ == 0)
{
lean_object* v___x_3164_; 
v___x_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3164_, 0, v_b_3155_);
return v___x_3164_;
}
else
{
lean_object* v_a_3165_; lean_object* v___x_3166_; 
v_a_3165_ = lean_array_uget_borrowed(v_as_3152_, v_i_3154_);
lean_inc(v_a_3165_);
v___x_3166_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__3(v_sortInfos_3151_, v_a_3165_, v_b_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3179_; 
v_a_3167_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3169_ = v___x_3166_;
v_isShared_3170_ = v_isSharedCheck_3179_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3166_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3179_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
if (lean_obj_tag(v_a_3167_) == 0)
{
lean_object* v_a_3171_; lean_object* v___x_3173_; 
v_a_3171_ = lean_ctor_get(v_a_3167_, 0);
lean_inc(v_a_3171_);
lean_dec_ref_known(v_a_3167_, 1);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 0, v_a_3171_);
v___x_3173_ = v___x_3169_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3171_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
else
{
lean_object* v_a_3175_; size_t v___x_3176_; size_t v___x_3177_; 
lean_del_object(v___x_3169_);
v_a_3175_ = lean_ctor_get(v_a_3167_, 0);
lean_inc(v_a_3175_);
lean_dec_ref_known(v_a_3167_, 1);
v___x_3176_ = ((size_t)1ULL);
v___x_3177_ = lean_usize_add(v_i_3154_, v___x_3176_);
v_i_3154_ = v___x_3177_;
v_b_3155_ = v_a_3175_;
goto _start;
}
}
}
else
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
v_a_3180_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3182_ = v___x_3166_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3166_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3180_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__4___boxed(lean_object* v_sortInfos_3188_, lean_object* v_as_3189_, lean_object* v_sz_3190_, lean_object* v_i_3191_, lean_object* v_b_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
size_t v_sz_boxed_3200_; size_t v_i_boxed_3201_; lean_object* v_res_3202_; 
v_sz_boxed_3200_ = lean_unbox_usize(v_sz_3190_);
lean_dec(v_sz_3190_);
v_i_boxed_3201_ = lean_unbox_usize(v_i_3191_);
lean_dec(v_i_3191_);
v_res_3202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__4(v_sortInfos_3188_, v_as_3189_, v_sz_boxed_3200_, v_i_boxed_3201_, v_b_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec_ref(v_as_3189_);
lean_dec_ref(v_sortInfos_3188_);
return v_res_3202_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds___closed__0(void){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v_newInfos_3205_; 
v___x_3203_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__0___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__0___closed__0);
v___x_3204_ = lean_unsigned_to_nat(0u);
v_newInfos_3205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_newInfos_3205_, 0, v___x_3204_);
lean_ctor_set(v_newInfos_3205_, 1, v___x_3203_);
return v_newInfos_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds(lean_object* v_preds_3206_, lean_object* v_sortInfos_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_){
_start:
{
lean_object* v_buckets_3215_; lean_object* v_newInfos_3216_; size_t v_sz_3217_; size_t v___x_3218_; lean_object* v___x_3219_; 
v_buckets_3215_ = lean_ctor_get(v_preds_3206_, 1);
v_newInfos_3216_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds___closed__0);
v_sz_3217_ = lean_array_size(v_buckets_3215_);
v___x_3218_ = ((size_t)0ULL);
v___x_3219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__4(v_sortInfos_3207_, v_buckets_3215_, v_sz_3217_, v___x_3218_, v_newInfos_3216_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds___boxed(lean_object* v_preds_3220_, lean_object* v_sortInfos_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds(v_preds_3220_, v_sortInfos_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
lean_dec(v_a_3227_);
lean_dec_ref(v_a_3226_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec_ref(v_sortInfos_3221_);
lean_dec_ref(v_preds_3220_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__1(lean_object* v_sortInfos_3230_, lean_object* v_as_3231_, size_t v_sz_3232_, size_t v_i_3233_, lean_object* v_b_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__1___redArg(v_sortInfos_3230_, v_as_3231_, v_sz_3232_, v_i_3233_, v_b_3234_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__1___boxed(lean_object* v_sortInfos_3243_, lean_object* v_as_3244_, lean_object* v_sz_3245_, lean_object* v_i_3246_, lean_object* v_b_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_){
_start:
{
size_t v_sz_boxed_3255_; size_t v_i_boxed_3256_; lean_object* v_res_3257_; 
v_sz_boxed_3255_ = lean_unbox_usize(v_sz_3245_);
lean_dec(v_sz_3245_);
v_i_boxed_3256_ = lean_unbox_usize(v_i_3246_);
lean_dec(v_i_3246_);
v_res_3257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__1(v_sortInfos_3243_, v_as_3244_, v_sz_boxed_3255_, v_i_boxed_3256_, v_b_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec_ref(v_as_3244_);
lean_dec_ref(v_sortInfos_3243_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__2(lean_object* v_00_u03b1_3258_, lean_object* v_msg_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v___x_3267_; 
v___x_3267_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__2___redArg(v_msg_3259_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__2___boxed(lean_object* v_00_u03b1_3268_, lean_object* v_msg_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds_spec__2(v_00_u03b1_3268_, v_msg_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__1(lean_object* v___x_3279_, lean_object* v___x_3280_, lean_object* v_n_3281_){
_start:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3282_ = l_BitVec_ofNat(v___x_3279_, v_n_3281_);
v___x_3283_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__1___closed__0));
v___x_3284_ = l_Lean_Name_mkStr2(v___x_3280_, v___x_3283_);
v___x_3285_ = lean_box(0);
v___x_3286_ = l_Lean_Expr_const___override(v___x_3284_, v___x_3285_);
v___x_3287_ = l_Lean_mkNatLit(v___x_3279_);
v___x_3288_ = l_Lean_mkNatLit(v___x_3282_);
v___x_3289_ = l_Lean_mkAppB(v___x_3286_, v___x_3287_, v___x_3288_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__1___boxed(lean_object* v___x_3290_, lean_object* v___x_3291_, lean_object* v_n_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__1(v___x_3290_, v___x_3291_, v_n_3292_);
lean_dec(v_n_3292_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__0(lean_object* v_type_3294_, lean_object* v_value_3295_){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3296_ = lean_box(0);
v___x_3297_ = lean_box(6);
v___x_3298_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3296_);
lean_ctor_set(v___x_3298_, 1, v_type_3294_);
lean_ctor_set(v___x_3298_, 2, v_value_3295_);
lean_ctor_set(v___x_3298_, 3, v___x_3297_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0_spec__0___redArg(lean_object* v_upperBound_3299_, lean_object* v___x_3300_, lean_object* v___x_3301_, lean_object* v_a_3302_, lean_object* v___x_3303_, lean_object* v_a_3304_, lean_object* v___x_3305_, lean_object* v_a_3306_, lean_object* v_b_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
uint8_t v___x_3315_; 
v___x_3315_ = lean_nat_dec_lt(v_a_3306_, v_upperBound_3299_);
if (v___x_3315_ == 0)
{
lean_object* v___x_3316_; 
lean_dec(v_a_3306_);
lean_dec_ref(v___x_3305_);
lean_dec_ref(v_a_3304_);
lean_dec_ref(v___x_3303_);
lean_dec_ref(v_a_3302_);
lean_dec(v___x_3301_);
v___x_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3316_, 0, v_b_3307_);
return v___x_3316_;
}
else
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3317_ = l_Lean_instInhabitedExpr;
v___x_3318_ = lean_unsigned_to_nat(1u);
v___x_3319_ = lean_array_get_borrowed(v___x_3317_, v___x_3300_, v_a_3306_);
v___x_3320_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__4, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__4);
v___x_3321_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__15, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__15_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__15);
lean_inc(v___x_3301_);
v___x_3322_ = l_Lean_mkNatLit(v___x_3301_);
v___x_3323_ = l_Lean_Expr_app___override(v___x_3321_, v___x_3322_);
lean_inc(v___x_3319_);
lean_inc_ref(v_a_3302_);
v___x_3324_ = l_Lean_Expr_app___override(v_a_3302_, v___x_3319_);
lean_inc_ref(v___x_3303_);
v___x_3325_ = l_Lean_mkApp3(v___x_3320_, v___x_3323_, v___x_3324_, v___x_3303_);
v___x_3326_ = l_Lean_mkNot(v___x_3325_);
lean_inc_ref(v_a_3304_);
v___x_3327_ = l_Lean_mkArrow(v_a_3304_, v___x_3326_, v___y_3312_, v___y_3313_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v___x_3329_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_a_3328_);
lean_dec_ref_known(v___x_3327_, 1);
v___x_3329_ = l_Lean_Meta_Sym_shareCommonInc(v_a_3328_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_a_3330_);
lean_dec_ref_known(v___x_3329_, 1);
lean_inc(v___x_3319_);
lean_inc_ref(v___x_3305_);
v___x_3331_ = l_Lean_Expr_app___override(v___x_3305_, v___x_3319_);
v___x_3332_ = lean_box(0);
v___x_3333_ = lean_box(6);
v___x_3334_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3332_);
lean_ctor_set(v___x_3334_, 1, v_a_3330_);
lean_ctor_set(v___x_3334_, 2, v___x_3331_);
lean_ctor_set(v___x_3334_, 3, v___x_3333_);
v___x_3335_ = lean_array_push(v_b_3307_, v___x_3334_);
v___x_3336_ = lean_nat_add(v_a_3306_, v___x_3318_);
lean_dec(v_a_3306_);
v_a_3306_ = v___x_3336_;
v_b_3307_ = v___x_3335_;
goto _start;
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
lean_dec_ref(v_b_3307_);
lean_dec(v_a_3306_);
lean_dec_ref(v___x_3305_);
lean_dec_ref(v_a_3304_);
lean_dec_ref(v___x_3303_);
lean_dec_ref(v_a_3302_);
lean_dec(v___x_3301_);
v_a_3338_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3329_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3329_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
lean_dec_ref(v_b_3307_);
lean_dec(v_a_3306_);
lean_dec_ref(v___x_3305_);
lean_dec_ref(v_a_3304_);
lean_dec_ref(v___x_3303_);
lean_dec_ref(v_a_3302_);
lean_dec(v___x_3301_);
v_a_3346_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3327_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3327_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0_spec__0___redArg___boxed(lean_object* v_upperBound_3354_, lean_object* v___x_3355_, lean_object* v___x_3356_, lean_object* v_a_3357_, lean_object* v___x_3358_, lean_object* v_a_3359_, lean_object* v___x_3360_, lean_object* v_a_3361_, lean_object* v_b_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0_spec__0___redArg(v_upperBound_3354_, v___x_3355_, v___x_3356_, v_a_3357_, v___x_3358_, v_a_3359_, v___x_3360_, v_a_3361_, v_b_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec_ref(v___x_3355_);
lean_dec(v_upperBound_3354_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0___redArg(lean_object* v_upperBound_3371_, lean_object* v___x_3372_, lean_object* v___x_3373_, lean_object* v_a_3374_, lean_object* v___x_3375_, lean_object* v_a_3376_, lean_object* v___x_3377_, lean_object* v_a_3378_, lean_object* v_b_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
uint8_t v___x_3387_; 
v___x_3387_ = lean_nat_dec_lt(v_a_3378_, v_upperBound_3371_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3388_; 
lean_dec_ref(v___x_3377_);
lean_dec_ref(v_a_3376_);
lean_dec_ref(v___x_3375_);
lean_dec_ref(v_a_3374_);
lean_dec(v___x_3373_);
v___x_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3388_, 0, v_b_3379_);
return v___x_3388_;
}
else
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3389_ = l_Lean_instInhabitedExpr;
v___x_3390_ = lean_unsigned_to_nat(1u);
v___x_3391_ = lean_array_get_borrowed(v___x_3389_, v___x_3372_, v_a_3378_);
v___x_3392_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__4, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom_spec__1___closed__4);
v___x_3393_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__15, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__15_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__15);
lean_inc(v___x_3373_);
v___x_3394_ = l_Lean_mkNatLit(v___x_3373_);
v___x_3395_ = l_Lean_Expr_app___override(v___x_3393_, v___x_3394_);
lean_inc(v___x_3391_);
lean_inc_ref(v_a_3374_);
v___x_3396_ = l_Lean_Expr_app___override(v_a_3374_, v___x_3391_);
lean_inc_ref(v___x_3375_);
v___x_3397_ = l_Lean_mkApp3(v___x_3392_, v___x_3395_, v___x_3396_, v___x_3375_);
v___x_3398_ = l_Lean_mkNot(v___x_3397_);
lean_inc_ref(v_a_3376_);
v___x_3399_ = l_Lean_mkArrow(v_a_3376_, v___x_3398_, v___y_3384_, v___y_3385_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; lean_object* v___x_3401_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
lean_dec_ref_known(v___x_3399_, 1);
v___x_3401_ = l_Lean_Meta_Sym_shareCommonInc(v_a_3400_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_a_3402_);
lean_dec_ref_known(v___x_3401_, 1);
lean_inc(v___x_3391_);
lean_inc_ref(v___x_3377_);
v___x_3403_ = l_Lean_Expr_app___override(v___x_3377_, v___x_3391_);
v___x_3404_ = lean_box(0);
v___x_3405_ = lean_box(6);
v___x_3406_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3404_);
lean_ctor_set(v___x_3406_, 1, v_a_3402_);
lean_ctor_set(v___x_3406_, 2, v___x_3403_);
lean_ctor_set(v___x_3406_, 3, v___x_3405_);
v___x_3407_ = lean_array_push(v_b_3379_, v___x_3406_);
v___x_3408_ = lean_nat_add(v_a_3378_, v___x_3390_);
v___x_3409_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0_spec__0___redArg(v_upperBound_3371_, v___x_3372_, v___x_3373_, v_a_3374_, v___x_3375_, v_a_3376_, v___x_3377_, v___x_3408_, v___x_3407_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
return v___x_3409_;
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_dec_ref(v_b_3379_);
lean_dec_ref(v___x_3377_);
lean_dec_ref(v_a_3376_);
lean_dec_ref(v___x_3375_);
lean_dec_ref(v_a_3374_);
lean_dec(v___x_3373_);
v_a_3410_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3401_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3401_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_dec_ref(v_b_3379_);
lean_dec_ref(v___x_3377_);
lean_dec_ref(v_a_3376_);
lean_dec_ref(v___x_3375_);
lean_dec_ref(v_a_3374_);
lean_dec(v___x_3373_);
v_a_3418_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3399_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3399_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0___redArg___boxed(lean_object* v_upperBound_3426_, lean_object* v___x_3427_, lean_object* v___x_3428_, lean_object* v_a_3429_, lean_object* v___x_3430_, lean_object* v_a_3431_, lean_object* v___x_3432_, lean_object* v_a_3433_, lean_object* v_b_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0___redArg(v_upperBound_3426_, v___x_3427_, v___x_3428_, v_a_3429_, v___x_3430_, v_a_3431_, v___x_3432_, v_a_3433_, v_b_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec(v_a_3433_);
lean_dec_ref(v___x_3427_);
lean_dec(v_upperBound_3426_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__2(lean_object* v___x_3445_, uint8_t v_symBreak_3446_, lean_object* v_a_3447_, lean_object* v___x_3448_, lean_object* v___x_3449_, lean_object* v___x_3450_, lean_object* v___x_3451_, lean_object* v___x_3452_, lean_object* v___x_3453_, lean_object* v___x_3454_, lean_object* v___x_3455_, lean_object* v___x_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v___x_3459_, lean_object* v___x_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v___f_3464_, lean_object* v___x_3465_, lean_object* v___x_3466_, lean_object* v___x_3467_, lean_object* v___x_3468_, lean_object* v___f_3469_, lean_object* v_____r_3470_, lean_object* v_facts_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
lean_object* v___y_3480_; lean_object* v_facts_3485_; 
switch(v_symBreak_3446_)
{
case 1:
{
goto v___jp_3523_;
}
case 2:
{
goto v___jp_3523_;
}
default: 
{
lean_dec_ref(v___f_3469_);
v_facts_3485_ = v_facts_3471_;
goto v___jp_3484_;
}
}
v___jp_3479_:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___y_3480_);
lean_ctor_set(v___x_3481_, 1, v___x_3445_);
v___x_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3481_);
v___x_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
return v___x_3483_;
}
v___jp_3484_:
{
if (v_symBreak_3446_ == 2)
{
uint8_t v___x_3486_; 
v___x_3486_ = lean_nat_dec_eq(v_a_3447_, v___x_3448_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3487_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__2___closed__0));
v___x_3488_ = l_Lean_Name_mkStr6(v___x_3449_, v___x_3450_, v___x_3451_, v___x_3452_, v___x_3453_, v___x_3487_);
v___x_3489_ = l_Lean_mkConst(v___x_3488_, v___x_3454_);
lean_inc_ref(v___x_3459_);
v___x_3490_ = l_Lean_mkApp8(v___x_3489_, v___x_3455_, v___x_3456_, v_a_3457_, v_a_3458_, v___x_3459_, v___x_3460_, v_a_3461_, v_a_3462_);
lean_inc_ref(v_a_3463_);
v___x_3491_ = l_Lean_Expr_app___override(v_a_3463_, v___x_3459_);
lean_inc(v_a_3447_);
v___x_3492_ = lean_apply_1(v___f_3464_, v_a_3447_);
lean_inc_ref(v___x_3492_);
v___x_3493_ = l_Lean_Meta_mkLt(v___x_3491_, v___x_3492_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3494_);
lean_dec_ref_known(v___x_3493_, 1);
v___x_3495_ = lean_nat_add(v_a_3447_, v___x_3465_);
lean_dec(v_a_3447_);
v___x_3496_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0___redArg(v___x_3466_, v___x_3467_, v___x_3468_, v_a_3463_, v___x_3492_, v_a_3494_, v___x_3490_, v___x_3495_, v_facts_3485_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
lean_dec(v___x_3495_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3506_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3499_ = v___x_3496_;
v_isShared_3500_ = v_isSharedCheck_3506_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3496_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3506_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3504_; 
v___x_3501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3501_, 0, v_a_3497_);
lean_ctor_set(v___x_3501_, 1, v___x_3445_);
v___x_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v___x_3502_);
v___x_3504_ = v___x_3499_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3502_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
else
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3514_; 
lean_dec_ref(v___x_3445_);
v_a_3507_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3509_ = v___x_3496_;
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3496_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_a_3507_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
else
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3522_; 
lean_dec_ref(v___x_3492_);
lean_dec_ref(v___x_3490_);
lean_dec_ref(v_facts_3485_);
lean_dec(v___x_3468_);
lean_dec_ref(v_a_3463_);
lean_dec(v_a_3447_);
lean_dec_ref(v___x_3445_);
v_a_3515_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3517_ = v___x_3493_;
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3493_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
if (v_isShared_3518_ == 0)
{
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3515_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
else
{
lean_dec(v___x_3468_);
lean_dec_ref(v___f_3464_);
lean_dec_ref(v_a_3463_);
lean_dec_ref(v_a_3462_);
lean_dec_ref(v_a_3461_);
lean_dec_ref(v___x_3460_);
lean_dec_ref(v___x_3459_);
lean_dec_ref(v_a_3458_);
lean_dec_ref(v_a_3457_);
lean_dec_ref(v___x_3456_);
lean_dec_ref(v___x_3455_);
lean_dec(v___x_3454_);
lean_dec_ref(v___x_3453_);
lean_dec_ref(v___x_3452_);
lean_dec_ref(v___x_3451_);
lean_dec_ref(v___x_3450_);
lean_dec_ref(v___x_3449_);
lean_dec(v_a_3447_);
v___y_3480_ = v_facts_3485_;
goto v___jp_3479_;
}
}
else
{
lean_dec(v___x_3468_);
lean_dec_ref(v___f_3464_);
lean_dec_ref(v_a_3463_);
lean_dec_ref(v_a_3462_);
lean_dec_ref(v_a_3461_);
lean_dec_ref(v___x_3460_);
lean_dec_ref(v___x_3459_);
lean_dec_ref(v_a_3458_);
lean_dec_ref(v_a_3457_);
lean_dec_ref(v___x_3456_);
lean_dec_ref(v___x_3455_);
lean_dec(v___x_3454_);
lean_dec_ref(v___x_3453_);
lean_dec_ref(v___x_3452_);
lean_dec_ref(v___x_3451_);
lean_dec_ref(v___x_3450_);
lean_dec_ref(v___x_3449_);
lean_dec(v_a_3447_);
v___y_3480_ = v_facts_3485_;
goto v___jp_3479_;
}
}
v___jp_3523_:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
lean_inc_ref(v___x_3459_);
lean_inc_ref(v_a_3463_);
v___x_3524_ = l_Lean_Expr_app___override(v_a_3463_, v___x_3459_);
lean_inc_ref(v___f_3464_);
lean_inc(v_a_3447_);
v___x_3525_ = lean_apply_1(v___f_3464_, v_a_3447_);
v___x_3526_ = l_Lean_Meta_mkLE(v___x_3524_, v___x_3525_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3528_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3527_);
lean_dec_ref_known(v___x_3526_, 1);
v___x_3528_ = l_Lean_Meta_Sym_shareCommonInc(v_a_3527_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3529_);
lean_dec_ref_known(v___x_3528_, 1);
v___x_3530_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__2___closed__1));
lean_inc_ref(v___x_3453_);
lean_inc_ref(v___x_3452_);
lean_inc_ref(v___x_3451_);
lean_inc_ref(v___x_3450_);
lean_inc_ref(v___x_3449_);
v___x_3531_ = l_Lean_Name_mkStr6(v___x_3449_, v___x_3450_, v___x_3451_, v___x_3452_, v___x_3453_, v___x_3530_);
lean_inc(v___x_3454_);
v___x_3532_ = l_Lean_mkConst(v___x_3531_, v___x_3454_);
lean_inc_ref(v_a_3462_);
lean_inc_ref(v_a_3461_);
lean_inc_ref(v___x_3460_);
lean_inc_ref(v___x_3459_);
lean_inc_ref(v_a_3458_);
lean_inc_ref(v_a_3457_);
lean_inc_ref(v___x_3456_);
lean_inc_ref(v___x_3455_);
v___x_3533_ = l_Lean_mkApp8(v___x_3532_, v___x_3455_, v___x_3456_, v_a_3457_, v_a_3458_, v___x_3459_, v___x_3460_, v_a_3461_, v_a_3462_);
v___x_3534_ = lean_apply_2(v___f_3469_, v_a_3529_, v___x_3533_);
v___x_3535_ = lean_array_push(v_facts_3471_, v___x_3534_);
v_facts_3485_ = v___x_3535_;
goto v___jp_3484_;
}
else
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
lean_dec_ref(v_facts_3471_);
lean_dec_ref(v___f_3469_);
lean_dec(v___x_3468_);
lean_dec_ref(v___f_3464_);
lean_dec_ref(v_a_3463_);
lean_dec_ref(v_a_3462_);
lean_dec_ref(v_a_3461_);
lean_dec_ref(v___x_3460_);
lean_dec_ref(v___x_3459_);
lean_dec_ref(v_a_3458_);
lean_dec_ref(v_a_3457_);
lean_dec_ref(v___x_3456_);
lean_dec_ref(v___x_3455_);
lean_dec(v___x_3454_);
lean_dec_ref(v___x_3453_);
lean_dec_ref(v___x_3452_);
lean_dec_ref(v___x_3451_);
lean_dec_ref(v___x_3450_);
lean_dec_ref(v___x_3449_);
lean_dec(v_a_3447_);
lean_dec_ref(v___x_3445_);
v_a_3536_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_3528_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3528_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
else
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3551_; 
lean_dec_ref(v_facts_3471_);
lean_dec_ref(v___f_3469_);
lean_dec(v___x_3468_);
lean_dec_ref(v___f_3464_);
lean_dec_ref(v_a_3463_);
lean_dec_ref(v_a_3462_);
lean_dec_ref(v_a_3461_);
lean_dec_ref(v___x_3460_);
lean_dec_ref(v___x_3459_);
lean_dec_ref(v_a_3458_);
lean_dec_ref(v_a_3457_);
lean_dec_ref(v___x_3456_);
lean_dec_ref(v___x_3455_);
lean_dec(v___x_3454_);
lean_dec_ref(v___x_3453_);
lean_dec_ref(v___x_3452_);
lean_dec_ref(v___x_3451_);
lean_dec_ref(v___x_3450_);
lean_dec_ref(v___x_3449_);
lean_dec(v_a_3447_);
lean_dec_ref(v___x_3445_);
v_a_3544_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3546_ = v___x_3526_;
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3526_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
if (v_isShared_3547_ == 0)
{
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3544_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_3552_ = _args[0];
lean_object* v_symBreak_3553_ = _args[1];
lean_object* v_a_3554_ = _args[2];
lean_object* v___x_3555_ = _args[3];
lean_object* v___x_3556_ = _args[4];
lean_object* v___x_3557_ = _args[5];
lean_object* v___x_3558_ = _args[6];
lean_object* v___x_3559_ = _args[7];
lean_object* v___x_3560_ = _args[8];
lean_object* v___x_3561_ = _args[9];
lean_object* v___x_3562_ = _args[10];
lean_object* v___x_3563_ = _args[11];
lean_object* v_a_3564_ = _args[12];
lean_object* v_a_3565_ = _args[13];
lean_object* v___x_3566_ = _args[14];
lean_object* v___x_3567_ = _args[15];
lean_object* v_a_3568_ = _args[16];
lean_object* v_a_3569_ = _args[17];
lean_object* v_a_3570_ = _args[18];
lean_object* v___f_3571_ = _args[19];
lean_object* v___x_3572_ = _args[20];
lean_object* v___x_3573_ = _args[21];
lean_object* v___x_3574_ = _args[22];
lean_object* v___x_3575_ = _args[23];
lean_object* v___f_3576_ = _args[24];
lean_object* v_____r_3577_ = _args[25];
lean_object* v_facts_3578_ = _args[26];
lean_object* v___y_3579_ = _args[27];
lean_object* v___y_3580_ = _args[28];
lean_object* v___y_3581_ = _args[29];
lean_object* v___y_3582_ = _args[30];
lean_object* v___y_3583_ = _args[31];
lean_object* v___y_3584_ = _args[32];
lean_object* v___y_3585_ = _args[33];
_start:
{
uint8_t v_symBreak_boxed_3586_; lean_object* v_res_3587_; 
v_symBreak_boxed_3586_ = lean_unbox(v_symBreak_3553_);
v_res_3587_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__2(v___x_3552_, v_symBreak_boxed_3586_, v_a_3554_, v___x_3555_, v___x_3556_, v___x_3557_, v___x_3558_, v___x_3559_, v___x_3560_, v___x_3561_, v___x_3562_, v___x_3563_, v_a_3564_, v_a_3565_, v___x_3566_, v___x_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v___f_3571_, v___x_3572_, v___x_3573_, v___x_3574_, v___x_3575_, v___f_3576_, v_____r_3577_, v_facts_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec_ref(v___x_3574_);
lean_dec(v___x_3573_);
lean_dec(v___x_3572_);
lean_dec(v___x_3555_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg(lean_object* v_upperBound_3605_, lean_object* v___x_3606_, lean_object* v_b_3607_, lean_object* v___x_3608_, lean_object* v___x_3609_, lean_object* v_a_3610_, uint8_t v_symBreak_3611_, lean_object* v___x_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v___x_3615_, lean_object* v___x_3616_, lean_object* v_a_3617_, lean_object* v_b_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
uint8_t v___x_3626_; 
v___x_3626_ = lean_nat_dec_lt(v_a_3617_, v_upperBound_3605_);
if (v___x_3626_ == 0)
{
lean_object* v___x_3627_; 
lean_dec(v_a_3617_);
lean_dec(v___x_3615_);
lean_dec_ref(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec_ref(v___x_3612_);
lean_dec_ref(v_a_3610_);
lean_dec_ref(v___x_3609_);
lean_dec(v___x_3608_);
v___x_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3627_, 0, v_b_3618_);
return v___x_3627_;
}
else
{
lean_object* v_fst_3628_; lean_object* v_snd_3629_; lean_object* v_elements_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___f_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___f_3640_; lean_object* v___x_3641_; lean_object* v___y_3643_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v_fst_3628_ = lean_ctor_get(v_b_3618_, 0);
lean_inc(v_fst_3628_);
v_snd_3629_ = lean_ctor_get(v_b_3618_, 1);
lean_inc(v_snd_3629_);
lean_dec_ref(v_b_3618_);
v_elements_3630_ = lean_ctor_get(v_b_3607_, 2);
v___x_3631_ = l_Lean_instInhabitedExpr;
v___x_3632_ = lean_array_get_borrowed(v___x_3631_, v___x_3606_, v_a_3617_);
v___f_3633_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__0));
v___x_3634_ = lean_unsigned_to_nat(0u);
v___x_3635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__1));
v___x_3636_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__2));
v___x_3637_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__3));
v___x_3638_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__10));
v___x_3639_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__11));
lean_inc(v___x_3615_);
v___f_3640_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3640_, 0, v___x_3615_);
lean_closure_set(v___f_3640_, 1, v___x_3639_);
v___x_3641_ = lean_unsigned_to_nat(1u);
lean_inc(v_a_3617_);
v___x_3664_ = l_Lean_mkNatLit(v_a_3617_);
v___x_3665_ = lean_array_get_size(v_elements_3630_);
v___x_3666_ = l_Lean_mkNatLit(v___x_3665_);
lean_inc_ref(v___x_3664_);
v___x_3667_ = l_Lean_Meta_mkLt(v___x_3664_, v___x_3666_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; lean_object* v___x_3669_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc(v_a_3668_);
lean_dec_ref_known(v___x_3667_, 1);
v___x_3669_ = l_Lean_Meta_mkDecideProof(v_a_3668_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v___x_3671_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_a_3670_);
lean_dec_ref_known(v___x_3669_, 1);
lean_inc(v___x_3632_);
v___x_3671_ = l_Lean_Meta_mkEqRefl(v___x_3632_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v_a_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
lean_inc(v_a_3672_);
lean_dec_ref_known(v___x_3671_, 1);
v___x_3673_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__3));
v___x_3674_ = lean_mk_empty_array_with_capacity(v___x_3641_);
v___x_3675_ = lean_array_push(v___x_3674_, v_a_3672_);
v___x_3676_ = l_Lean_Meta_mkAppM(v___x_3673_, v___x_3675_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc_n(v_a_3677_, 2);
lean_dec_ref_known(v___x_3676_, 1);
v___x_3678_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__5));
lean_inc(v___x_3608_);
v___x_3679_ = l_Lean_mkConst(v___x_3678_, v___x_3608_);
lean_inc_n(v___x_3632_, 2);
lean_inc(v_a_3670_);
lean_inc_ref(v___x_3664_);
lean_inc_ref(v_a_3610_);
lean_inc_ref(v___x_3609_);
v___x_3680_ = l_Lean_mkApp6(v___x_3679_, v___x_3609_, v_a_3610_, v___x_3664_, v_a_3670_, v___x_3632_, v_a_3677_);
lean_inc_ref(v___x_3680_);
v___x_3681_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_spec__0___redArg(v_snd_3629_, v___x_3632_, v___x_3680_);
if (v_symBreak_3611_ == 0)
{
lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
lean_inc(v___x_3632_);
lean_inc_ref(v_a_3614_);
v___x_3682_ = l_Lean_Expr_app___override(v_a_3614_, v___x_3632_);
v___x_3683_ = lean_array_get_size(v___x_3606_);
lean_inc(v___x_3615_);
v___x_3684_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__1(v___x_3615_, v___x_3639_, v___x_3683_);
v___x_3685_ = l_Lean_Meta_mkLt(v___x_3682_, v___x_3684_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_a_3686_; lean_object* v___x_3687_; 
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
lean_inc(v_a_3686_);
lean_dec_ref_known(v___x_3685_, 1);
v___x_3687_ = l_Lean_Meta_Sym_shareCommonInc(v_a_3686_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_a_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_a_3688_);
lean_dec_ref_known(v___x_3687_, 1);
v___x_3689_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___closed__7));
lean_inc_n(v___x_3608_, 2);
v___x_3690_ = l_Lean_mkConst(v___x_3689_, v___x_3608_);
lean_inc_n(v___x_3632_, 2);
lean_inc_ref_n(v_a_3613_, 2);
lean_inc_ref_n(v_a_3610_, 2);
lean_inc_ref_n(v___x_3612_, 2);
lean_inc_ref_n(v___x_3609_, 2);
v___x_3691_ = l_Lean_mkApp6(v___x_3690_, v___x_3609_, v___x_3612_, v_a_3610_, v_a_3613_, v___x_3632_, v___x_3680_);
v___x_3692_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__0(v_a_3688_, v___x_3691_);
v___x_3693_ = lean_array_push(v_fst_3628_, v___x_3692_);
v___x_3694_ = lean_box(0);
lean_inc(v___x_3615_);
lean_inc_ref(v_a_3614_);
lean_inc(v_a_3617_);
v___x_3695_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__2(v___x_3681_, v_symBreak_3611_, v_a_3617_, v___x_3634_, v___x_3635_, v___x_3636_, v___x_3637_, v___x_3638_, v___x_3639_, v___x_3608_, v___x_3609_, v___x_3612_, v_a_3610_, v_a_3613_, v___x_3632_, v___x_3664_, v_a_3670_, v_a_3677_, v_a_3614_, v___f_3640_, v___x_3641_, v___x_3616_, v___x_3606_, v___x_3615_, v___f_3633_, v___x_3694_, v___x_3693_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
v___y_3643_ = v___x_3695_;
goto v___jp_3642_;
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_dec_ref(v___x_3681_);
lean_dec_ref(v___x_3680_);
lean_dec(v_a_3677_);
lean_dec(v_a_3670_);
lean_dec_ref(v___x_3664_);
lean_dec_ref(v___f_3640_);
lean_dec(v_fst_3628_);
lean_dec(v_a_3617_);
lean_dec(v___x_3615_);
lean_dec_ref(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec_ref(v___x_3612_);
lean_dec_ref(v_a_3610_);
lean_dec_ref(v___x_3609_);
lean_dec(v___x_3608_);
v_a_3696_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3687_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3687_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec_ref(v___x_3681_);
lean_dec_ref(v___x_3680_);
lean_dec(v_a_3677_);
lean_dec(v_a_3670_);
lean_dec_ref(v___x_3664_);
lean_dec_ref(v___f_3640_);
lean_dec(v_fst_3628_);
lean_dec(v_a_3617_);
lean_dec(v___x_3615_);
lean_dec_ref(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec_ref(v___x_3612_);
lean_dec_ref(v_a_3610_);
lean_dec_ref(v___x_3609_);
lean_dec(v___x_3608_);
v_a_3704_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3685_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3685_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
else
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
lean_dec_ref(v___x_3680_);
v___x_3712_ = lean_box(0);
lean_inc(v___x_3615_);
lean_inc_ref(v_a_3614_);
lean_inc(v___x_3632_);
lean_inc_ref(v_a_3613_);
lean_inc_ref(v_a_3610_);
lean_inc_ref(v___x_3612_);
lean_inc_ref(v___x_3609_);
lean_inc(v___x_3608_);
lean_inc(v_a_3617_);
v___x_3713_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___lam__2(v___x_3681_, v_symBreak_3611_, v_a_3617_, v___x_3634_, v___x_3635_, v___x_3636_, v___x_3637_, v___x_3638_, v___x_3639_, v___x_3608_, v___x_3609_, v___x_3612_, v_a_3610_, v_a_3613_, v___x_3632_, v___x_3664_, v_a_3670_, v_a_3677_, v_a_3614_, v___f_3640_, v___x_3641_, v___x_3616_, v___x_3606_, v___x_3615_, v___f_3633_, v___x_3712_, v_fst_3628_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
v___y_3643_ = v___x_3713_;
goto v___jp_3642_;
}
}
else
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3721_; 
lean_dec(v_a_3670_);
lean_dec_ref(v___x_3664_);
lean_dec_ref(v___f_3640_);
lean_dec(v_snd_3629_);
lean_dec(v_fst_3628_);
lean_dec(v_a_3617_);
lean_dec(v___x_3615_);
lean_dec_ref(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec_ref(v___x_3612_);
lean_dec_ref(v_a_3610_);
lean_dec_ref(v___x_3609_);
lean_dec(v___x_3608_);
v_a_3714_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3716_ = v___x_3676_;
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3676_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3719_; 
if (v_isShared_3717_ == 0)
{
v___x_3719_ = v___x_3716_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_a_3714_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
}
}
else
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
lean_dec(v_a_3670_);
lean_dec_ref(v___x_3664_);
lean_dec_ref(v___f_3640_);
lean_dec(v_snd_3629_);
lean_dec(v_fst_3628_);
lean_dec(v_a_3617_);
lean_dec(v___x_3615_);
lean_dec_ref(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec_ref(v___x_3612_);
lean_dec_ref(v_a_3610_);
lean_dec_ref(v___x_3609_);
lean_dec(v___x_3608_);
v_a_3722_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3671_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3671_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec_ref(v___x_3664_);
lean_dec_ref(v___f_3640_);
lean_dec(v_snd_3629_);
lean_dec(v_fst_3628_);
lean_dec(v_a_3617_);
lean_dec(v___x_3615_);
lean_dec_ref(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec_ref(v___x_3612_);
lean_dec_ref(v_a_3610_);
lean_dec_ref(v___x_3609_);
lean_dec(v___x_3608_);
v_a_3730_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3669_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3669_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
lean_dec_ref(v___x_3664_);
lean_dec_ref(v___f_3640_);
lean_dec(v_snd_3629_);
lean_dec(v_fst_3628_);
lean_dec(v_a_3617_);
lean_dec(v___x_3615_);
lean_dec_ref(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec_ref(v___x_3612_);
lean_dec_ref(v_a_3610_);
lean_dec_ref(v___x_3609_);
lean_dec(v___x_3608_);
v_a_3738_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3667_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3667_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
v___jp_3642_:
{
if (lean_obj_tag(v___y_3643_) == 0)
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3655_; 
v_a_3644_ = lean_ctor_get(v___y_3643_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___y_3643_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3646_ = v___y_3643_;
v_isShared_3647_ = v_isSharedCheck_3655_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___y_3643_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3655_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
if (lean_obj_tag(v_a_3644_) == 0)
{
lean_object* v_a_3648_; lean_object* v___x_3650_; 
lean_dec(v_a_3617_);
lean_dec(v___x_3615_);
lean_dec_ref(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec_ref(v___x_3612_);
lean_dec_ref(v_a_3610_);
lean_dec_ref(v___x_3609_);
lean_dec(v___x_3608_);
v_a_3648_ = lean_ctor_get(v_a_3644_, 0);
lean_inc(v_a_3648_);
lean_dec_ref_known(v_a_3644_, 1);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 0, v_a_3648_);
v___x_3650_ = v___x_3646_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3648_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
else
{
lean_object* v_a_3652_; lean_object* v___x_3653_; 
lean_del_object(v___x_3646_);
v_a_3652_ = lean_ctor_get(v_a_3644_, 0);
lean_inc(v_a_3652_);
lean_dec_ref_known(v_a_3644_, 1);
v___x_3653_ = lean_nat_add(v_a_3617_, v___x_3641_);
lean_dec(v_a_3617_);
v_a_3617_ = v___x_3653_;
v_b_3618_ = v_a_3652_;
goto _start;
}
}
}
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
lean_dec(v_a_3617_);
lean_dec(v___x_3615_);
lean_dec_ref(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec_ref(v___x_3612_);
lean_dec_ref(v_a_3610_);
lean_dec_ref(v___x_3609_);
lean_dec(v___x_3608_);
v_a_3656_ = lean_ctor_get(v___y_3643_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___y_3643_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___y_3643_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___y_3643_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3656_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_3746_ = _args[0];
lean_object* v___x_3747_ = _args[1];
lean_object* v_b_3748_ = _args[2];
lean_object* v___x_3749_ = _args[3];
lean_object* v___x_3750_ = _args[4];
lean_object* v_a_3751_ = _args[5];
lean_object* v_symBreak_3752_ = _args[6];
lean_object* v___x_3753_ = _args[7];
lean_object* v_a_3754_ = _args[8];
lean_object* v_a_3755_ = _args[9];
lean_object* v___x_3756_ = _args[10];
lean_object* v___x_3757_ = _args[11];
lean_object* v_a_3758_ = _args[12];
lean_object* v_b_3759_ = _args[13];
lean_object* v___y_3760_ = _args[14];
lean_object* v___y_3761_ = _args[15];
lean_object* v___y_3762_ = _args[16];
lean_object* v___y_3763_ = _args[17];
lean_object* v___y_3764_ = _args[18];
lean_object* v___y_3765_ = _args[19];
lean_object* v___y_3766_ = _args[20];
_start:
{
uint8_t v_symBreak_boxed_3767_; lean_object* v_res_3768_; 
v_symBreak_boxed_3767_ = lean_unbox(v_symBreak_3752_);
v_res_3768_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg(v_upperBound_3746_, v___x_3747_, v_b_3748_, v___x_3749_, v___x_3750_, v_a_3751_, v_symBreak_boxed_3767_, v___x_3753_, v_a_3754_, v_a_3755_, v___x_3756_, v___x_3757_, v_a_3758_, v_b_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___x_3757_);
lean_dec_ref(v_b_3748_);
lean_dec_ref(v___x_3747_);
lean_dec(v_upperBound_3746_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2(uint8_t v_symBreak_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
if (lean_obj_tag(v_a_3782_) == 0)
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3791_, 0, v_a_3783_);
v___x_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3791_);
return v___x_3792_;
}
else
{
lean_object* v_value_3793_; lean_object* v_key_3794_; lean_object* v_tail_3795_; lean_object* v_fst_3796_; lean_object* v_snd_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3923_; 
v_value_3793_ = lean_ctor_get(v_a_3782_, 1);
lean_inc(v_value_3793_);
v_key_3794_ = lean_ctor_get(v_a_3782_, 0);
lean_inc(v_key_3794_);
v_tail_3795_ = lean_ctor_get(v_a_3782_, 2);
lean_inc(v_tail_3795_);
lean_dec_ref_known(v_a_3782_, 3);
v_fst_3796_ = lean_ctor_get(v_a_3783_, 0);
v_snd_3797_ = lean_ctor_get(v_a_3783_, 1);
v_isSharedCheck_3923_ = !lean_is_exclusive(v_a_3783_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3799_ = v_a_3783_;
v_isShared_3800_ = v_isSharedCheck_3923_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_snd_3797_);
lean_inc(v_fst_3796_);
lean_dec(v_a_3783_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3923_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v_type_3801_; lean_object* v_level_3802_; lean_object* v_elements_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v_type_3801_ = lean_ctor_get(v_value_3793_, 0);
v_level_3802_ = lean_ctor_get(v_value_3793_, 1);
v_elements_3803_ = lean_ctor_get(v_value_3793_, 2);
v___x_3804_ = lean_array_get_size(v_elements_3803_);
v___x_3805_ = lean_nat_log2(v___x_3804_);
v___x_3806_ = lean_unsigned_to_nat(1u);
v___x_3807_ = lean_nat_add(v___x_3805_, v___x_3806_);
lean_dec(v___x_3805_);
lean_inc_ref(v_elements_3803_);
v___x_3808_ = lean_array_to_list(v_elements_3803_);
lean_inc_ref(v_type_3801_);
v___x_3809_ = l_Lean_Meta_mkListLit(v_type_3801_, v___x_3808_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; lean_object* v___x_3811_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3810_);
lean_dec_ref_known(v___x_3809_, 1);
v___x_3811_ = l_Lean_Meta_Sym_shareCommonInc(v_a_3810_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
if (lean_obj_tag(v___x_3811_) == 0)
{
lean_object* v_a_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v_a_3812_ = lean_ctor_get(v___x_3811_, 0);
lean_inc_n(v_a_3812_, 2);
lean_dec_ref_known(v___x_3811_, 1);
v___x_3813_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__1));
v___x_3814_ = lean_mk_empty_array_with_capacity(v___x_3806_);
v___x_3815_ = lean_array_push(v___x_3814_, v_a_3812_);
v___x_3816_ = l_Lean_Meta_mkAppM(v___x_3813_, v___x_3815_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v_a_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_a_3817_);
lean_dec_ref_known(v___x_3816_, 1);
v___x_3818_ = lean_unsigned_to_nat(2u);
v___x_3819_ = lean_nat_pow(v___x_3818_, v___x_3807_);
v___x_3820_ = l_Lean_mkNatLit(v___x_3819_);
v___x_3821_ = l_Lean_Meta_mkLt(v_a_3817_, v___x_3820_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; lean_object* v___x_3823_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_a_3822_);
lean_dec_ref_known(v___x_3821_, 1);
v___x_3823_ = l_Lean_Meta_mkDecideProof(v_a_3822_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v_a_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v_a_3824_ = lean_ctor_get(v___x_3823_, 0);
lean_inc_n(v_a_3824_, 2);
lean_dec_ref_known(v___x_3823_, 1);
v___x_3825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateAtom___closed__13));
v___x_3826_ = lean_box(0);
lean_inc(v_level_3802_);
v___x_3827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3827_, 0, v_level_3802_);
lean_ctor_set(v___x_3827_, 1, v___x_3826_);
lean_inc_ref(v___x_3827_);
v___x_3828_ = l_Lean_mkConst(v___x_3825_, v___x_3827_);
lean_inc(v___x_3807_);
v___x_3829_ = l_Lean_mkNatLit(v___x_3807_);
lean_inc(v_a_3812_);
lean_inc_ref(v___x_3829_);
lean_inc_ref(v_type_3801_);
v___x_3830_ = l_Lean_mkApp4(v___x_3828_, v_type_3801_, v___x_3829_, v_a_3812_, v_a_3824_);
v___x_3831_ = l_Lean_Meta_Sym_shareCommonInc(v___x_3830_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v_a_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
lean_inc(v_a_3832_);
lean_dec_ref_known(v___x_3831_, 1);
v___x_3833_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___closed__3));
lean_inc_ref(v___x_3827_);
v___x_3834_ = l_Lean_mkConst(v___x_3833_, v___x_3827_);
v___x_3835_ = l_Lean_instInhabitedExpr;
v___x_3836_ = lean_unsigned_to_nat(0u);
v___x_3837_ = lean_array_get_borrowed(v___x_3835_, v_elements_3803_, v___x_3836_);
lean_inc(v___x_3837_);
lean_inc(v_a_3812_);
lean_inc_ref(v___x_3829_);
lean_inc_ref(v_type_3801_);
v___x_3838_ = l_Lean_mkApp4(v___x_3834_, v_type_3801_, v___x_3829_, v_a_3812_, v___x_3837_);
v___x_3839_ = l_Lean_Meta_Sym_shareCommonInc(v___x_3838_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; lean_object* v___x_3841_; lean_object* v___x_3843_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_a_3840_);
lean_dec_ref_known(v___x_3839_, 1);
v___x_3841_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds___closed__0);
if (v_isShared_3800_ == 0)
{
lean_ctor_set(v___x_3799_, 1, v___x_3841_);
lean_ctor_set(v___x_3799_, 0, v_snd_3797_);
v___x_3843_ = v___x_3799_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_snd_3797_);
lean_ctor_set(v_reuseFailAlloc_3866_, 1, v___x_3841_);
v___x_3843_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
lean_object* v___x_3844_; 
lean_inc(v___x_3807_);
lean_inc(v_a_3832_);
lean_inc(v_a_3824_);
lean_inc(v_a_3812_);
lean_inc_ref(v_type_3801_);
v___x_3844_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg(v___x_3804_, v_elements_3803_, v_value_3793_, v___x_3827_, v_type_3801_, v_a_3812_, v_symBreak_3781_, v___x_3829_, v_a_3824_, v_a_3832_, v___x_3807_, v___x_3804_, v___x_3836_, v___x_3843_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; lean_object* v_fst_3846_; lean_object* v_snd_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3857_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref_known(v___x_3844_, 1);
v_fst_3846_ = lean_ctor_get(v_a_3845_, 0);
v_snd_3847_ = lean_ctor_get(v_a_3845_, 1);
v_isSharedCheck_3857_ = !lean_is_exclusive(v_a_3845_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3849_ = v_a_3845_;
v_isShared_3850_ = v_isSharedCheck_3857_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_snd_3847_);
lean_inc(v_fst_3846_);
lean_dec(v_a_3845_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3857_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3854_; 
v___x_3851_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3851_, 0, v_value_3793_);
lean_ctor_set(v___x_3851_, 1, v___x_3807_);
lean_ctor_set(v___x_3851_, 2, v_a_3832_);
lean_ctor_set(v___x_3851_, 3, v_a_3840_);
lean_ctor_set(v___x_3851_, 4, v_a_3812_);
lean_ctor_set(v___x_3851_, 5, v_a_3824_);
lean_ctor_set(v___x_3851_, 6, v_snd_3847_);
v___x_3852_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified_mkMemHyp_spec__2___redArg(v_fst_3796_, v_key_3794_, v___x_3851_);
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 1, v_fst_3846_);
lean_ctor_set(v___x_3849_, 0, v___x_3852_);
v___x_3854_ = v___x_3849_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3852_);
lean_ctor_set(v_reuseFailAlloc_3856_, 1, v_fst_3846_);
v___x_3854_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
v_a_3782_ = v_tail_3795_;
v_a_3783_ = v___x_3854_;
goto _start;
}
}
}
else
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3865_; 
lean_dec(v_a_3840_);
lean_dec(v_a_3832_);
lean_dec(v_a_3824_);
lean_dec(v_a_3812_);
lean_dec(v___x_3807_);
lean_dec(v_fst_3796_);
lean_dec(v_tail_3795_);
lean_dec(v_key_3794_);
lean_dec(v_value_3793_);
v_a_3858_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3860_ = v___x_3844_;
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3844_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3861_ == 0)
{
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
}
else
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3874_; 
lean_dec(v_a_3832_);
lean_dec_ref(v___x_3829_);
lean_dec_ref_known(v___x_3827_, 2);
lean_dec(v_a_3824_);
lean_dec(v_a_3812_);
lean_dec(v___x_3807_);
lean_del_object(v___x_3799_);
lean_dec(v_snd_3797_);
lean_dec(v_fst_3796_);
lean_dec(v_tail_3795_);
lean_dec(v_key_3794_);
lean_dec(v_value_3793_);
v_a_3867_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3869_ = v___x_3839_;
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3839_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
if (v_isShared_3870_ == 0)
{
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3867_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
else
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3882_; 
lean_dec_ref(v___x_3829_);
lean_dec_ref_known(v___x_3827_, 2);
lean_dec(v_a_3824_);
lean_dec(v_a_3812_);
lean_dec(v___x_3807_);
lean_del_object(v___x_3799_);
lean_dec(v_snd_3797_);
lean_dec(v_fst_3796_);
lean_dec(v_tail_3795_);
lean_dec(v_key_3794_);
lean_dec(v_value_3793_);
v_a_3875_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3877_ = v___x_3831_;
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3831_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3880_; 
if (v_isShared_3878_ == 0)
{
v___x_3880_ = v___x_3877_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_a_3875_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
}
else
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3890_; 
lean_dec(v_a_3812_);
lean_dec(v___x_3807_);
lean_del_object(v___x_3799_);
lean_dec(v_snd_3797_);
lean_dec(v_fst_3796_);
lean_dec(v_tail_3795_);
lean_dec(v_key_3794_);
lean_dec(v_value_3793_);
v_a_3883_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3885_ = v___x_3823_;
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3823_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3888_; 
if (v_isShared_3886_ == 0)
{
v___x_3888_ = v___x_3885_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
}
else
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3898_; 
lean_dec(v_a_3812_);
lean_dec(v___x_3807_);
lean_del_object(v___x_3799_);
lean_dec(v_snd_3797_);
lean_dec(v_fst_3796_);
lean_dec(v_tail_3795_);
lean_dec(v_key_3794_);
lean_dec(v_value_3793_);
v_a_3891_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3893_ = v___x_3821_;
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3821_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3896_; 
if (v_isShared_3894_ == 0)
{
v___x_3896_ = v___x_3893_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
}
else
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3906_; 
lean_dec(v_a_3812_);
lean_dec(v___x_3807_);
lean_del_object(v___x_3799_);
lean_dec(v_snd_3797_);
lean_dec(v_fst_3796_);
lean_dec(v_tail_3795_);
lean_dec(v_key_3794_);
lean_dec(v_value_3793_);
v_a_3899_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3901_ = v___x_3816_;
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3816_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3899_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
else
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3914_; 
lean_dec(v___x_3807_);
lean_del_object(v___x_3799_);
lean_dec(v_snd_3797_);
lean_dec(v_fst_3796_);
lean_dec(v_tail_3795_);
lean_dec(v_key_3794_);
lean_dec(v_value_3793_);
v_a_3907_ = lean_ctor_get(v___x_3811_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3909_ = v___x_3811_;
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3811_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3912_; 
if (v_isShared_3910_ == 0)
{
v___x_3912_ = v___x_3909_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3907_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec(v___x_3807_);
lean_del_object(v___x_3799_);
lean_dec(v_snd_3797_);
lean_dec(v_fst_3796_);
lean_dec(v_tail_3795_);
lean_dec(v_key_3794_);
lean_dec(v_value_3793_);
v_a_3915_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3809_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3809_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2___boxed(lean_object* v_symBreak_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
uint8_t v_symBreak_boxed_3934_; lean_object* v_res_3935_; 
v_symBreak_boxed_3934_ = lean_unbox(v_symBreak_3924_);
v_res_3935_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2(v_symBreak_boxed_3934_, v_a_3925_, v_a_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__3(uint8_t v_symBreak_3936_, lean_object* v_as_3937_, size_t v_sz_3938_, size_t v_i_3939_, lean_object* v_b_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
uint8_t v___x_3948_; 
v___x_3948_ = lean_usize_dec_lt(v_i_3939_, v_sz_3938_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; 
v___x_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3949_, 0, v_b_3940_);
return v___x_3949_;
}
else
{
lean_object* v_a_3950_; lean_object* v___x_3951_; 
v_a_3950_ = lean_array_uget_borrowed(v_as_3937_, v_i_3939_);
lean_inc(v_a_3950_);
v___x_3951_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__2(v_symBreak_3936_, v_a_3950_, v_b_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v_a_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3964_; 
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3954_ = v___x_3951_;
v_isShared_3955_ = v_isSharedCheck_3964_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_a_3952_);
lean_dec(v___x_3951_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3964_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
if (lean_obj_tag(v_a_3952_) == 0)
{
lean_object* v_a_3956_; lean_object* v___x_3958_; 
v_a_3956_ = lean_ctor_get(v_a_3952_, 0);
lean_inc(v_a_3956_);
lean_dec_ref_known(v_a_3952_, 1);
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 0, v_a_3956_);
v___x_3958_ = v___x_3954_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_a_3956_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
}
}
else
{
lean_object* v_a_3960_; size_t v___x_3961_; size_t v___x_3962_; 
lean_del_object(v___x_3954_);
v_a_3960_ = lean_ctor_get(v_a_3952_, 0);
lean_inc(v_a_3960_);
lean_dec_ref_known(v_a_3952_, 1);
v___x_3961_ = ((size_t)1ULL);
v___x_3962_ = lean_usize_add(v_i_3939_, v___x_3961_);
v_i_3939_ = v___x_3962_;
v_b_3940_ = v_a_3960_;
goto _start;
}
}
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
v_a_3965_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3951_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3951_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__3___boxed(lean_object* v_symBreak_3973_, lean_object* v_as_3974_, lean_object* v_sz_3975_, lean_object* v_i_3976_, lean_object* v_b_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
uint8_t v_symBreak_boxed_3985_; size_t v_sz_boxed_3986_; size_t v_i_boxed_3987_; lean_object* v_res_3988_; 
v_symBreak_boxed_3985_ = lean_unbox(v_symBreak_3973_);
v_sz_boxed_3986_ = lean_unbox_usize(v_sz_3975_);
lean_dec(v_sz_3975_);
v_i_boxed_3987_ = lean_unbox_usize(v_i_3976_);
lean_dec(v_i_3976_);
v_res_3988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__3(v_symBreak_boxed_3985_, v_as_3974_, v_sz_boxed_3986_, v_i_boxed_3987_, v_b_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec_ref(v_as_3974_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts(lean_object* v_sorts_3991_, uint8_t v_symBreak_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_){
_start:
{
lean_object* v_size_4000_; lean_object* v_buckets_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4038_; 
v_size_4000_ = lean_ctor_get(v_sorts_3991_, 0);
v_buckets_4001_ = lean_ctor_get(v_sorts_3991_, 1);
v_isSharedCheck_4038_ = !lean_is_exclusive(v_sorts_3991_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4003_ = v_sorts_3991_;
v_isShared_4004_ = v_isSharedCheck_4038_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_buckets_4001_);
lean_inc(v_size_4000_);
lean_dec(v_sorts_3991_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4038_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v_bvSortInfo_4014_; 
v___x_4005_ = lean_unsigned_to_nat(0u);
v___x_4006_ = lean_unsigned_to_nat(4u);
v___x_4007_ = lean_nat_mul(v_size_4000_, v___x_4006_);
lean_dec(v_size_4000_);
v___x_4008_ = lean_unsigned_to_nat(3u);
v___x_4009_ = lean_nat_div(v___x_4007_, v___x_4008_);
lean_dec(v___x_4007_);
v___x_4010_ = l_Nat_nextPowerOfTwo(v___x_4009_);
lean_dec(v___x_4009_);
v___x_4011_ = lean_box(0);
v___x_4012_ = lean_mk_array(v___x_4010_, v___x_4011_);
if (v_isShared_4004_ == 0)
{
lean_ctor_set(v___x_4003_, 1, v___x_4012_);
lean_ctor_set(v___x_4003_, 0, v___x_4005_);
v_bvSortInfo_4014_ = v___x_4003_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v___x_4005_);
lean_ctor_set(v_reuseFailAlloc_4037_, 1, v___x_4012_);
v_bvSortInfo_4014_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
lean_object* v_facts_4015_; lean_object* v___x_4016_; size_t v_sz_4017_; size_t v___x_4018_; lean_object* v___x_4019_; 
v_facts_4015_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts___closed__0));
v___x_4016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4016_, 0, v_bvSortInfo_4014_);
lean_ctor_set(v___x_4016_, 1, v_facts_4015_);
v_sz_4017_ = lean_array_size(v_buckets_4001_);
v___x_4018_ = ((size_t)0ULL);
v___x_4019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__3(v_symBreak_3992_, v_buckets_4001_, v_sz_4017_, v___x_4018_, v___x_4016_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
lean_dec_ref(v_buckets_4001_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4036_; 
v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4022_ = v___x_4019_;
v_isShared_4023_ = v_isSharedCheck_4036_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_4019_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4036_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v_fst_4024_; lean_object* v_snd_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4035_; 
v_fst_4024_ = lean_ctor_get(v_a_4020_, 0);
v_snd_4025_ = lean_ctor_get(v_a_4020_, 1);
v_isSharedCheck_4035_ = !lean_is_exclusive(v_a_4020_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4027_ = v_a_4020_;
v_isShared_4028_ = v_isSharedCheck_4035_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_snd_4025_);
lean_inc(v_fst_4024_);
lean_dec(v_a_4020_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4035_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4030_; 
if (v_isShared_4028_ == 0)
{
v___x_4030_ = v___x_4027_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_fst_4024_);
lean_ctor_set(v_reuseFailAlloc_4034_, 1, v_snd_4025_);
v___x_4030_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
lean_object* v___x_4032_; 
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 0, v___x_4030_);
v___x_4032_ = v___x_4022_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_4030_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
}
else
{
return v___x_4019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts___boxed(lean_object* v_sorts_4039_, lean_object* v_symBreak_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_){
_start:
{
uint8_t v_symBreak_boxed_4048_; lean_object* v_res_4049_; 
v_symBreak_boxed_4048_ = lean_unbox(v_symBreak_4040_);
v_res_4049_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts(v_sorts_4039_, v_symBreak_boxed_4048_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_);
lean_dec(v_a_4046_);
lean_dec_ref(v_a_4045_);
lean_dec(v_a_4044_);
lean_dec_ref(v_a_4043_);
lean_dec(v_a_4042_);
lean_dec_ref(v_a_4041_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0(lean_object* v_upperBound_4050_, lean_object* v___x_4051_, lean_object* v___x_4052_, lean_object* v_a_4053_, lean_object* v___x_4054_, lean_object* v_a_4055_, lean_object* v___x_4056_, lean_object* v_inst_4057_, lean_object* v_R_4058_, lean_object* v_a_4059_, lean_object* v_b_4060_, lean_object* v_c_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
lean_object* v___x_4069_; 
v___x_4069_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0___redArg(v_upperBound_4050_, v___x_4051_, v___x_4052_, v_a_4053_, v___x_4054_, v_a_4055_, v___x_4056_, v_a_4059_, v_b_4060_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_4070_ = _args[0];
lean_object* v___x_4071_ = _args[1];
lean_object* v___x_4072_ = _args[2];
lean_object* v_a_4073_ = _args[3];
lean_object* v___x_4074_ = _args[4];
lean_object* v_a_4075_ = _args[5];
lean_object* v___x_4076_ = _args[6];
lean_object* v_inst_4077_ = _args[7];
lean_object* v_R_4078_ = _args[8];
lean_object* v_a_4079_ = _args[9];
lean_object* v_b_4080_ = _args[10];
lean_object* v_c_4081_ = _args[11];
lean_object* v___y_4082_ = _args[12];
lean_object* v___y_4083_ = _args[13];
lean_object* v___y_4084_ = _args[14];
lean_object* v___y_4085_ = _args[15];
lean_object* v___y_4086_ = _args[16];
lean_object* v___y_4087_ = _args[17];
lean_object* v___y_4088_ = _args[18];
_start:
{
lean_object* v_res_4089_; 
v_res_4089_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0(v_upperBound_4070_, v___x_4071_, v___x_4072_, v_a_4073_, v___x_4074_, v_a_4075_, v___x_4076_, v_inst_4077_, v_R_4078_, v_a_4079_, v_b_4080_, v_c_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
lean_dec(v_a_4079_);
lean_dec_ref(v___x_4071_);
lean_dec(v_upperBound_4070_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1(lean_object* v_upperBound_4090_, lean_object* v___x_4091_, lean_object* v_b_4092_, lean_object* v___x_4093_, lean_object* v___x_4094_, lean_object* v_a_4095_, uint8_t v_symBreak_4096_, lean_object* v___x_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v___x_4100_, lean_object* v___x_4101_, lean_object* v_inst_4102_, lean_object* v_R_4103_, lean_object* v_a_4104_, lean_object* v_b_4105_, lean_object* v_c_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v___x_4114_; 
v___x_4114_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___redArg(v_upperBound_4090_, v___x_4091_, v_b_4092_, v___x_4093_, v___x_4094_, v_a_4095_, v_symBreak_4096_, v___x_4097_, v_a_4098_, v_a_4099_, v___x_4100_, v___x_4101_, v_a_4104_, v_b_4105_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_4115_ = _args[0];
lean_object* v___x_4116_ = _args[1];
lean_object* v_b_4117_ = _args[2];
lean_object* v___x_4118_ = _args[3];
lean_object* v___x_4119_ = _args[4];
lean_object* v_a_4120_ = _args[5];
lean_object* v_symBreak_4121_ = _args[6];
lean_object* v___x_4122_ = _args[7];
lean_object* v_a_4123_ = _args[8];
lean_object* v_a_4124_ = _args[9];
lean_object* v___x_4125_ = _args[10];
lean_object* v___x_4126_ = _args[11];
lean_object* v_inst_4127_ = _args[12];
lean_object* v_R_4128_ = _args[13];
lean_object* v_a_4129_ = _args[14];
lean_object* v_b_4130_ = _args[15];
lean_object* v_c_4131_ = _args[16];
lean_object* v___y_4132_ = _args[17];
lean_object* v___y_4133_ = _args[18];
lean_object* v___y_4134_ = _args[19];
lean_object* v___y_4135_ = _args[20];
lean_object* v___y_4136_ = _args[21];
lean_object* v___y_4137_ = _args[22];
lean_object* v___y_4138_ = _args[23];
_start:
{
uint8_t v_symBreak_boxed_4139_; lean_object* v_res_4140_; 
v_symBreak_boxed_4139_ = lean_unbox(v_symBreak_4121_);
v_res_4140_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__1(v_upperBound_4115_, v___x_4116_, v_b_4117_, v___x_4118_, v___x_4119_, v_a_4120_, v_symBreak_boxed_4139_, v___x_4122_, v_a_4123_, v_a_4124_, v___x_4125_, v___x_4126_, v_inst_4127_, v_R_4128_, v_a_4129_, v_b_4130_, v_c_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec(v___x_4126_);
lean_dec_ref(v_b_4117_);
lean_dec_ref(v___x_4116_);
lean_dec(v_upperBound_4115_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0_spec__0(lean_object* v_upperBound_4141_, lean_object* v___x_4142_, lean_object* v___x_4143_, lean_object* v_a_4144_, lean_object* v___x_4145_, lean_object* v_a_4146_, lean_object* v___x_4147_, lean_object* v_inst_4148_, lean_object* v_R_4149_, lean_object* v_a_4150_, lean_object* v_b_4151_, lean_object* v_c_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
lean_object* v___x_4160_; 
v___x_4160_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0_spec__0___redArg(v_upperBound_4141_, v___x_4142_, v___x_4143_, v_a_4144_, v___x_4145_, v_a_4146_, v___x_4147_, v_a_4150_, v_b_4151_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_4161_ = _args[0];
lean_object* v___x_4162_ = _args[1];
lean_object* v___x_4163_ = _args[2];
lean_object* v_a_4164_ = _args[3];
lean_object* v___x_4165_ = _args[4];
lean_object* v_a_4166_ = _args[5];
lean_object* v___x_4167_ = _args[6];
lean_object* v_inst_4168_ = _args[7];
lean_object* v_R_4169_ = _args[8];
lean_object* v_a_4170_ = _args[9];
lean_object* v_b_4171_ = _args[10];
lean_object* v_c_4172_ = _args[11];
lean_object* v___y_4173_ = _args[12];
lean_object* v___y_4174_ = _args[13];
lean_object* v___y_4175_ = _args[14];
lean_object* v___y_4176_ = _args[15];
lean_object* v___y_4177_ = _args[16];
lean_object* v___y_4178_ = _args[17];
lean_object* v___y_4179_ = _args[18];
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts_spec__0_spec__0(v_upperBound_4161_, v___x_4162_, v___x_4163_, v_a_4164_, v___x_4165_, v_a_4166_, v___x_4167_, v_inst_4168_, v_R_4169_, v_a_4170_, v_b_4171_, v_c_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec_ref(v___x_4162_);
lean_dec(v_upperBound_4161_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__2___redArg___lam__0(lean_object* v_x_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
lean_object* v___x_4189_; 
lean_inc(v___y_4183_);
lean_inc_ref(v___y_4182_);
v___x_4189_ = lean_apply_7(v_x_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, lean_box(0));
return v___x_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__2___redArg___lam__0___boxed(lean_object* v_x_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__2___redArg___lam__0(v_x_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__2___redArg(lean_object* v_mvarId_4199_, lean_object* v_x_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v___f_4208_; lean_object* v___x_4209_; 
lean_inc(v___y_4202_);
lean_inc_ref(v___y_4201_);
v___f_4208_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4208_, 0, v_x_4200_);
lean_closure_set(v___f_4208_, 1, v___y_4201_);
lean_closure_set(v___f_4208_, 2, v___y_4202_);
v___x_4209_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4199_, v___f_4208_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
if (lean_obj_tag(v___x_4209_) == 0)
{
return v___x_4209_;
}
else
{
lean_object* v_a_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4217_; 
v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4212_ = v___x_4209_;
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_a_4210_);
lean_dec(v___x_4209_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4215_; 
if (v_isShared_4213_ == 0)
{
v___x_4215_ = v___x_4212_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_a_4210_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__2___redArg___boxed(lean_object* v_mvarId_4218_, lean_object* v_x_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__2___redArg(v_mvarId_4218_, v_x_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__2(lean_object* v_00_u03b1_4228_, lean_object* v_mvarId_4229_, lean_object* v_x_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_){
_start:
{
lean_object* v___x_4238_; 
v___x_4238_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__2___redArg(v_mvarId_4229_, v_x_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__2___boxed(lean_object* v_00_u03b1_4239_, lean_object* v_mvarId_4240_, lean_object* v_x_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v_res_4249_; 
v_res_4249_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__2(v_00_u03b1_4239_, v_mvarId_4240_, v_x_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__1(size_t v_sz_4250_, size_t v_i_4251_, lean_object* v_bs_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
uint8_t v___x_4262_; 
v___x_4262_ = lean_usize_dec_lt(v_i_4251_, v_sz_4250_);
if (v___x_4262_ == 0)
{
lean_object* v___x_4263_; 
v___x_4263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4263_, 0, v_bs_4252_);
return v___x_4263_;
}
else
{
lean_object* v_v_4264_; lean_object* v___x_4265_; lean_object* v_bs_x27_4266_; lean_object* v___x_4267_; 
v_v_4264_ = lean_array_uget(v_bs_4252_, v_i_4251_);
v___x_4265_ = lean_unsigned_to_nat(0u);
v_bs_x27_4266_ = lean_array_uset(v_bs_4252_, v_i_4251_, v___x_4265_);
v___x_4267_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified(v_v_4264_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_);
if (lean_obj_tag(v___x_4267_) == 0)
{
lean_object* v_a_4268_; size_t v___x_4269_; size_t v___x_4270_; lean_object* v___x_4271_; 
v_a_4268_ = lean_ctor_get(v___x_4267_, 0);
lean_inc(v_a_4268_);
lean_dec_ref_known(v___x_4267_, 1);
v___x_4269_ = ((size_t)1ULL);
v___x_4270_ = lean_usize_add(v_i_4251_, v___x_4269_);
v___x_4271_ = lean_array_uset(v_bs_x27_4266_, v_i_4251_, v_a_4268_);
v_i_4251_ = v___x_4270_;
v_bs_4252_ = v___x_4271_;
goto _start;
}
else
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4280_; 
lean_dec_ref(v_bs_x27_4266_);
v_a_4273_ = lean_ctor_get(v___x_4267_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4267_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4275_ = v___x_4267_;
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4267_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4278_; 
if (v_isShared_4276_ == 0)
{
v___x_4278_ = v___x_4275_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4273_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__1___boxed(lean_object* v_sz_4281_, lean_object* v_i_4282_, lean_object* v_bs_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_){
_start:
{
size_t v_sz_boxed_4293_; size_t v_i_boxed_4294_; lean_object* v_res_4295_; 
v_sz_boxed_4293_ = lean_unbox_usize(v_sz_4281_);
lean_dec(v_sz_4281_);
v_i_boxed_4294_ = lean_unbox_usize(v_i_4282_);
lean_dec(v_i_4282_);
v_res_4295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__1(v_sz_boxed_4293_, v_i_boxed_4294_, v_bs_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
return v_res_4295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__0(size_t v_sz_4296_, size_t v_i_4297_, lean_object* v_bs_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_){
_start:
{
uint8_t v___x_4308_; 
v___x_4308_ = lean_usize_dec_lt(v_i_4297_, v_sz_4296_);
if (v___x_4308_ == 0)
{
lean_object* v___x_4309_; 
v___x_4309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4309_, 0, v_bs_4298_);
return v___x_4309_;
}
else
{
lean_object* v_v_4310_; lean_object* v___x_4311_; lean_object* v_bs_x27_4312_; lean_object* v___x_4313_; 
v_v_4310_ = lean_array_uget(v_bs_4298_, v_i_4297_);
v___x_4311_ = lean_unsigned_to_nat(0u);
v_bs_x27_4312_ = lean_array_uset(v_bs_4298_, v_i_4297_, v___x_4311_);
v___x_4313_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateGround(v_v_4310_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
if (lean_obj_tag(v___x_4313_) == 0)
{
lean_object* v_a_4314_; size_t v___x_4315_; size_t v___x_4316_; lean_object* v___x_4317_; 
v_a_4314_ = lean_ctor_get(v___x_4313_, 0);
lean_inc(v_a_4314_);
lean_dec_ref_known(v___x_4313_, 1);
v___x_4315_ = ((size_t)1ULL);
v___x_4316_ = lean_usize_add(v_i_4297_, v___x_4315_);
v___x_4317_ = lean_array_uset(v_bs_x27_4312_, v_i_4297_, v_a_4314_);
v_i_4297_ = v___x_4316_;
v_bs_4298_ = v___x_4317_;
goto _start;
}
else
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4326_; 
lean_dec_ref(v_bs_x27_4312_);
v_a_4319_ = lean_ctor_get(v___x_4313_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4321_ = v___x_4313_;
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4313_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4324_; 
if (v_isShared_4322_ == 0)
{
v___x_4324_ = v___x_4321_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4319_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
return v___x_4324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__0___boxed(lean_object* v_sz_4327_, lean_object* v_i_4328_, lean_object* v_bs_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_){
_start:
{
size_t v_sz_boxed_4339_; size_t v_i_boxed_4340_; lean_object* v_res_4341_; 
v_sz_boxed_4339_ = lean_unbox_usize(v_sz_4327_);
lean_dec(v_sz_4327_);
v_i_boxed_4340_ = lean_unbox_usize(v_i_4328_);
lean_dec(v_i_4328_);
v_res_4341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__0(v_sz_boxed_4339_, v_i_boxed_4340_, v_bs_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
lean_dec(v___y_4335_);
lean_dec_ref(v___y_4334_);
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
lean_dec(v___y_4331_);
lean_dec_ref(v___y_4330_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec___lam__0(size_t v_sz_4342_, size_t v___x_4343_, lean_object* v_groundFacts_4344_, lean_object* v_quantifiedFacts_4345_, lean_object* v_snd_4346_, lean_object* v_fst_4347_, lean_object* v_sortMap_4348_, lean_object* v_a_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_){
_start:
{
lean_object* v___x_4359_; 
v___x_4359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__0(v_sz_4342_, v___x_4343_, v_groundFacts_4344_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_object* v_a_4360_; size_t v_sz_4361_; lean_object* v___x_4362_; 
v_a_4360_ = lean_ctor_get(v___x_4359_, 0);
lean_inc(v_a_4360_);
lean_dec_ref_known(v___x_4359_, 1);
v_sz_4361_ = lean_array_size(v_quantifiedFacts_4345_);
v___x_4362_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__1(v_sz_4361_, v___x_4343_, v_quantifiedFacts_4345_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
if (lean_obj_tag(v___x_4362_) == 0)
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4372_; 
v_a_4363_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4365_ = v___x_4362_;
v_isShared_4366_ = v_isSharedCheck_4372_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___x_4362_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4372_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4370_; 
v___x_4367_ = l_Array_append___redArg(v_a_4360_, v_snd_4346_);
v___x_4368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4368_, 0, v_fst_4347_);
lean_ctor_set(v___x_4368_, 1, v_sortMap_4348_);
lean_ctor_set(v___x_4368_, 2, v_a_4349_);
lean_ctor_set(v___x_4368_, 3, v___x_4367_);
lean_ctor_set(v___x_4368_, 4, v_a_4363_);
if (v_isShared_4366_ == 0)
{
lean_ctor_set(v___x_4365_, 0, v___x_4368_);
v___x_4370_ = v___x_4365_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___x_4368_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
lean_dec(v_a_4360_);
lean_dec_ref(v_a_4349_);
lean_dec_ref(v_sortMap_4348_);
lean_dec_ref(v_fst_4347_);
v_a_4373_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___x_4362_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4362_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
else
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4388_; 
lean_dec_ref(v_a_4349_);
lean_dec_ref(v_sortMap_4348_);
lean_dec_ref(v_fst_4347_);
lean_dec_ref(v_quantifiedFacts_4345_);
v_a_4381_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4383_ = v___x_4359_;
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4359_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4386_; 
if (v_isShared_4384_ == 0)
{
v___x_4386_ = v___x_4383_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_a_4381_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
return v___x_4386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec___lam__0___boxed(lean_object** _args){
lean_object* v_sz_4389_ = _args[0];
lean_object* v___x_4390_ = _args[1];
lean_object* v_groundFacts_4391_ = _args[2];
lean_object* v_quantifiedFacts_4392_ = _args[3];
lean_object* v_snd_4393_ = _args[4];
lean_object* v_fst_4394_ = _args[5];
lean_object* v_sortMap_4395_ = _args[6];
lean_object* v_a_4396_ = _args[7];
lean_object* v___y_4397_ = _args[8];
lean_object* v___y_4398_ = _args[9];
lean_object* v___y_4399_ = _args[10];
lean_object* v___y_4400_ = _args[11];
lean_object* v___y_4401_ = _args[12];
lean_object* v___y_4402_ = _args[13];
lean_object* v___y_4403_ = _args[14];
lean_object* v___y_4404_ = _args[15];
lean_object* v___y_4405_ = _args[16];
_start:
{
size_t v_sz_boxed_4406_; size_t v___x_3862__boxed_4407_; lean_object* v_res_4408_; 
v_sz_boxed_4406_ = lean_unbox_usize(v_sz_4389_);
lean_dec(v_sz_4389_);
v___x_3862__boxed_4407_ = lean_unbox_usize(v___x_4390_);
lean_dec(v___x_4390_);
v_res_4408_ = l_Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec___lam__0(v_sz_boxed_4406_, v___x_3862__boxed_4407_, v_groundFacts_4391_, v_quantifiedFacts_4392_, v_snd_4393_, v_fst_4394_, v_sortMap_4395_, v_a_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
lean_dec(v___y_4400_);
lean_dec_ref(v___y_4399_);
lean_dec(v___y_4398_);
lean_dec_ref(v___y_4397_);
lean_dec_ref(v_snd_4393_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec___lam__1(lean_object* v_sortInfo_4409_, uint8_t v_symBreak_4410_, lean_object* v_predInfo_4411_, lean_object* v_sortMap_4412_, lean_object* v_groundFacts_4413_, lean_object* v_quantifiedFacts_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_){
_start:
{
lean_object* v___x_4422_; 
v___x_4422_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateSorts(v_sortInfo_4409_, v_symBreak_4410_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_object* v_a_4423_; lean_object* v_fst_4424_; lean_object* v_snd_4425_; lean_object* v___x_4426_; 
v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
lean_inc(v_a_4423_);
lean_dec_ref_known(v___x_4422_, 1);
v_fst_4424_ = lean_ctor_get(v_a_4423_, 0);
lean_inc(v_fst_4424_);
v_snd_4425_ = lean_ctor_get(v_a_4423_, 1);
lean_inc(v_snd_4425_);
lean_dec(v_a_4423_);
v___x_4426_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds(v_predInfo_4411_, v_fst_4424_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_);
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_object* v_a_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; size_t v_sz_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___f_4433_; lean_object* v___x_4434_; 
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
lean_inc_n(v_a_4427_, 2);
lean_dec_ref_known(v___x_4426_, 1);
v___x_4428_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translatePreds___closed__0);
lean_inc_ref(v_sortMap_4412_);
lean_inc(v_fst_4424_);
v___x_4429_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4429_, 0, v_a_4427_);
lean_ctor_set(v___x_4429_, 1, v_fst_4424_);
lean_ctor_set(v___x_4429_, 2, v_sortMap_4412_);
lean_ctor_set(v___x_4429_, 3, v___x_4428_);
v_sz_4430_ = lean_array_size(v_groundFacts_4413_);
v___x_4431_ = lean_box_usize(v_sz_4430_);
v___x_4432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_translateQuantified___lam__1___boxed__const__1));
v___f_4433_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec___lam__0___boxed), 17, 8);
lean_closure_set(v___f_4433_, 0, v___x_4431_);
lean_closure_set(v___f_4433_, 1, v___x_4432_);
lean_closure_set(v___f_4433_, 2, v_groundFacts_4413_);
lean_closure_set(v___f_4433_, 3, v_quantifiedFacts_4414_);
lean_closure_set(v___f_4433_, 4, v_snd_4425_);
lean_closure_set(v___f_4433_, 5, v_fst_4424_);
lean_closure_set(v___f_4433_, 6, v_sortMap_4412_);
lean_closure_set(v___f_4433_, 7, v_a_4427_);
v___x_4434_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_TranslateExprM_run___redArg(v___x_4429_, v___f_4433_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_);
return v___x_4434_;
}
else
{
lean_object* v_a_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4442_; 
lean_dec(v_snd_4425_);
lean_dec(v_fst_4424_);
lean_dec_ref(v_quantifiedFacts_4414_);
lean_dec_ref(v_groundFacts_4413_);
lean_dec_ref(v_sortMap_4412_);
v_a_4435_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4437_ = v___x_4426_;
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_a_4435_);
lean_dec(v___x_4426_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v___x_4440_; 
if (v_isShared_4438_ == 0)
{
v___x_4440_ = v___x_4437_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4435_);
v___x_4440_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
return v___x_4440_;
}
}
}
}
else
{
lean_object* v_a_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4450_; 
lean_dec_ref(v_quantifiedFacts_4414_);
lean_dec_ref(v_groundFacts_4413_);
lean_dec_ref(v_sortMap_4412_);
v_a_4443_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4445_ = v___x_4422_;
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_a_4443_);
lean_dec(v___x_4422_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4448_; 
if (v_isShared_4446_ == 0)
{
v___x_4448_ = v___x_4445_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_a_4443_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec___lam__1___boxed(lean_object* v_sortInfo_4451_, lean_object* v_symBreak_4452_, lean_object* v_predInfo_4453_, lean_object* v_sortMap_4454_, lean_object* v_groundFacts_4455_, lean_object* v_quantifiedFacts_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
uint8_t v_symBreak_boxed_4464_; lean_object* v_res_4465_; 
v_symBreak_boxed_4464_ = lean_unbox(v_symBreak_4452_);
v_res_4465_ = l_Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec___lam__1(v_sortInfo_4451_, v_symBreak_boxed_4464_, v_predInfo_4453_, v_sortMap_4454_, v_groundFacts_4455_, v_quantifiedFacts_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_dec(v___y_4460_);
lean_dec_ref(v___y_4459_);
lean_dec(v___y_4458_);
lean_dec_ref(v___y_4457_);
lean_dec_ref(v_predInfo_4453_);
return v_res_4465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec(lean_object* v_problem_4466_, lean_object* v_g_4467_, uint8_t v_symBreak_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_){
_start:
{
lean_object* v_sortInfo_4476_; lean_object* v_sortMap_4477_; lean_object* v_predInfo_4478_; lean_object* v_groundFacts_4479_; lean_object* v_quantifiedFacts_4480_; lean_object* v___x_4481_; lean_object* v___f_4482_; lean_object* v___x_4483_; 
v_sortInfo_4476_ = lean_ctor_get(v_problem_4466_, 0);
lean_inc_ref(v_sortInfo_4476_);
v_sortMap_4477_ = lean_ctor_get(v_problem_4466_, 1);
lean_inc_ref(v_sortMap_4477_);
v_predInfo_4478_ = lean_ctor_get(v_problem_4466_, 2);
lean_inc_ref(v_predInfo_4478_);
v_groundFacts_4479_ = lean_ctor_get(v_problem_4466_, 3);
lean_inc_ref(v_groundFacts_4479_);
v_quantifiedFacts_4480_ = lean_ctor_get(v_problem_4466_, 4);
lean_inc_ref(v_quantifiedFacts_4480_);
lean_dec_ref(v_problem_4466_);
v___x_4481_ = lean_box(v_symBreak_4468_);
v___f_4482_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec___lam__1___boxed), 13, 6);
lean_closure_set(v___f_4482_, 0, v_sortInfo_4476_);
lean_closure_set(v___f_4482_, 1, v___x_4481_);
lean_closure_set(v___f_4482_, 2, v_predInfo_4478_);
lean_closure_set(v___f_4482_, 3, v_sortMap_4477_);
lean_closure_set(v___f_4482_, 4, v_groundFacts_4479_);
lean_closure_set(v___f_4482_, 5, v_quantifiedFacts_4480_);
v___x_4483_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec_spec__2___redArg(v_g_4467_, v___f_4482_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_, v_a_4473_, v_a_4474_);
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec___boxed(lean_object* v_problem_4484_, lean_object* v_g_4485_, lean_object* v_symBreak_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_){
_start:
{
uint8_t v_symBreak_boxed_4494_; lean_object* v_res_4495_; 
v_symBreak_boxed_4494_ = lean_unbox(v_symBreak_4486_);
v_res_4495_ = l_Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec(v_problem_4484_, v_g_4485_, v_symBreak_boxed_4494_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_);
lean_dec(v_a_4492_);
lean_dec_ref(v_a_4491_);
lean_dec(v_a_4490_);
lean_dec_ref(v_a_4489_);
lean_dec(v_a_4488_);
lean_dec_ref(v_a_4487_);
return v_res_4495_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_EPR_BitVec(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Normalize_Prop(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_BitVec(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_EPR_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Normalize_Prop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo_default);
l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo = _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo();
lean_mark_persistent(l___private_Lean_Meta_Tactic_BVDecide_EPR_BitVec_0__Lean_Meta_Tactic_BVDecide_EPR_instInhabitedVarInfo);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_EPR_BitVec(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_EPR_Basic(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_EPR_BitVec(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Normalize_Prop(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_EPR_BitVec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_EPR_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_EPR_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Normalize_Prop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_EPR_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_EPR_BitVec(builtin);
}
#ifdef __cplusplus
}
#endif
