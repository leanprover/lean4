// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.Basic
// Imports: public import Lean.Meta.Tactic.BVDecide.Attr public import Std.Tactic.BVDecide.Syntax public import Lean.Meta.Sym.ExprPtr public import Lean.Meta.Sym.SymM public import Lean.Meta.Sym.Simp.SimpM public import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InferType import Lean.Meta.Sym.InstantiateMVarsS public import Lean.Meta.Sym.DSimp.DSimpM import Lean.Meta.Sym.DSimp.Result
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_Result_getResultExpr(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_instMonadExceptOfEIO(lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
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
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instExceptToTraceResultBool___lam__0___boxed(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_lctx_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_lctx_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_enumDomain_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_enumDomain_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_structureProjection_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_structureProjection_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_andFlattened_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_andFlattened_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__1;
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "assumption "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "enum domain size lemma for "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "structure lemma projection: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "and flattening from "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setGoal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setGoal___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Learned hypothesis: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "  ==>  "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Running pass: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResultBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___boxed(lean_object**);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Fixpoint iteration solved the goal"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Pipeline reached a fixpoint"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Rerunning pipeline"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult___redArg___lam__0(lean_object* v_toPure_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v_contextDependent_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_12_; 
v_contextDependent_3_ = lean_ctor_get_uint8(v_x_2_, 1);
v_isSharedCheck_12_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_12_ == 0)
{
v___x_5_ = v_x_2_;
v_isShared_6_ = v_isSharedCheck_12_;
goto v_resetjp_4_;
}
else
{
lean_dec(v_x_2_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_12_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
uint8_t v___x_7_; lean_object* v___x_9_; 
v___x_7_ = 1;
if (v_isShared_6_ == 0)
{
v___x_9_ = v___x_5_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_11_; 
v_reuseFailAlloc_11_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_11_, 1, v_contextDependent_3_);
v___x_9_ = v_reuseFailAlloc_11_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
lean_object* v___x_10_; 
lean_ctor_set_uint8(v___x_9_, 0, v___x_7_);
v___x_10_ = lean_apply_2(v_toPure_1_, lean_box(0), v___x_9_);
return v___x_10_;
}
}
}
else
{
lean_object* v_e_x27_13_; lean_object* v_proof_14_; uint8_t v_contextDependent_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v_e_x27_13_ = lean_ctor_get(v_x_2_, 0);
v_proof_14_ = lean_ctor_get(v_x_2_, 1);
v_contextDependent_15_ = lean_ctor_get_uint8(v_x_2_, sizeof(void*)*2 + 1);
v_isSharedCheck_24_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_24_ == 0)
{
v___x_17_ = v_x_2_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_proof_14_);
lean_inc(v_e_x27_13_);
lean_dec(v_x_2_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
uint8_t v___x_19_; lean_object* v___x_21_; 
v___x_19_ = 1;
if (v_isShared_18_ == 0)
{
v___x_21_ = v___x_17_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_e_x27_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_proof_14_);
lean_ctor_set_uint8(v_reuseFailAlloc_23_, sizeof(void*)*2 + 1, v_contextDependent_15_);
v___x_21_ = v_reuseFailAlloc_23_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
lean_object* v___x_22_; 
lean_ctor_set_uint8(v___x_21_, sizeof(void*)*2, v___x_19_);
v___x_22_ = lean_apply_2(v_toPure_1_, lean_box(0), v___x_21_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult___redArg(lean_object* v_inst_25_, lean_object* v_x_26_){
_start:
{
lean_object* v_toApplicative_27_; lean_object* v_toBind_28_; lean_object* v_toPure_29_; lean_object* v___f_30_; lean_object* v___x_31_; 
v_toApplicative_27_ = lean_ctor_get(v_inst_25_, 0);
lean_inc_ref(v_toApplicative_27_);
v_toBind_28_ = lean_ctor_get(v_inst_25_, 1);
lean_inc(v_toBind_28_);
lean_dec_ref(v_inst_25_);
v_toPure_29_ = lean_ctor_get(v_toApplicative_27_, 1);
lean_inc(v_toPure_29_);
lean_dec_ref(v_toApplicative_27_);
v___f_30_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult___redArg___lam__0), 2, 1);
lean_closure_set(v___f_30_, 0, v_toPure_29_);
v___x_31_ = lean_apply_4(v_toBind_28_, lean_box(0), lean_box(0), v_x_26_, v___f_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult(lean_object* v_m_32_, lean_object* v_inst_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_toApplicative_35_; lean_object* v_toBind_36_; lean_object* v_toPure_37_; lean_object* v___f_38_; lean_object* v___x_39_; 
v_toApplicative_35_ = lean_ctor_get(v_inst_33_, 0);
lean_inc_ref(v_toApplicative_35_);
v_toBind_36_ = lean_ctor_get(v_inst_33_, 1);
lean_inc(v_toBind_36_);
lean_dec_ref(v_inst_33_);
v_toPure_37_ = lean_ctor_get(v_toApplicative_35_, 1);
lean_inc(v_toPure_37_);
lean_dec_ref(v_toApplicative_35_);
v___f_38_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult___redArg___lam__0), 2, 1);
lean_closure_set(v___f_38_, 0, v_toPure_37_);
v___x_39_ = lean_apply_4(v_toBind_36_, lean_box(0), lean_box(0), v_x_34_, v___f_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx(lean_object* v_x_40_){
_start:
{
if (lean_obj_tag(v_x_40_) == 0)
{
lean_object* v___x_41_; 
v___x_41_ = lean_unsigned_to_nat(0u);
return v___x_41_;
}
else
{
lean_object* v___x_42_; 
v___x_42_ = lean_unsigned_to_nat(1u);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx___boxed(lean_object* v_x_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx(v_x_43_);
lean_dec_ref(v_x_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(lean_object* v_t_45_, lean_object* v_k_46_){
_start:
{
lean_object* v_info_47_; lean_object* v_ctors_48_; lean_object* v___x_49_; 
v_info_47_ = lean_ctor_get(v_t_45_, 0);
lean_inc_ref(v_info_47_);
v_ctors_48_ = lean_ctor_get(v_t_45_, 1);
lean_inc_ref(v_ctors_48_);
lean_dec_ref(v_t_45_);
v___x_49_ = lean_apply_2(v_k_46_, v_info_47_, v_ctors_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(lean_object* v_motive_50_, lean_object* v_ctorIdx_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_k_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_52_, v_k_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___boxed(lean_object* v_motive_56_, lean_object* v_ctorIdx_57_, lean_object* v_t_58_, lean_object* v_h_59_, lean_object* v_k_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(v_motive_56_, v_ctorIdx_57_, v_t_58_, v_h_59_, v_k_60_);
lean_dec(v_ctorIdx_57_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim___redArg(lean_object* v_t_62_, lean_object* v_simpleEnum_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_62_, v_simpleEnum_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim(lean_object* v_motive_65_, lean_object* v_t_66_, lean_object* v_h_67_, lean_object* v_simpleEnum_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_66_, v_simpleEnum_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim___redArg(lean_object* v_t_70_, lean_object* v_enumWithDefault_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_70_, v_enumWithDefault_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim(lean_object* v_motive_73_, lean_object* v_t_74_, lean_object* v_h_75_, lean_object* v_enumWithDefault_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_74_, v_enumWithDefault_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx(lean_object* v_x_78_){
_start:
{
switch(lean_obj_tag(v_x_78_))
{
case 0:
{
lean_object* v___x_79_; 
v___x_79_ = lean_unsigned_to_nat(0u);
return v___x_79_;
}
case 1:
{
lean_object* v___x_80_; 
v___x_80_ = lean_unsigned_to_nat(1u);
return v___x_80_;
}
case 2:
{
lean_object* v___x_81_; 
v___x_81_ = lean_unsigned_to_nat(2u);
return v___x_81_;
}
default: 
{
lean_object* v___x_82_; 
v___x_82_ = lean_unsigned_to_nat(3u);
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx___boxed(lean_object* v_x_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx(v_x_83_);
lean_dec_ref(v_x_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(lean_object* v_t_85_, lean_object* v_k_86_){
_start:
{
switch(lean_obj_tag(v_t_85_))
{
case 2:
{
lean_object* v_e_87_; lean_object* v___x_88_; 
v_e_87_ = lean_ctor_get(v_t_85_, 0);
lean_inc_ref(v_e_87_);
lean_dec_ref_known(v_t_85_, 1);
v___x_88_ = lean_apply_1(v_k_86_, v_e_87_);
return v___x_88_;
}
case 3:
{
lean_object* v_s_89_; lean_object* v___x_90_; 
v_s_89_ = lean_ctor_get(v_t_85_, 0);
lean_inc_ref(v_s_89_);
lean_dec_ref_known(v_t_85_, 1);
v___x_90_ = lean_apply_1(v_k_86_, v_s_89_);
return v___x_90_;
}
default: 
{
lean_object* v_fvar_91_; lean_object* v___x_92_; 
v_fvar_91_ = lean_ctor_get(v_t_85_, 0);
lean_inc(v_fvar_91_);
lean_dec_ref(v_t_85_);
v___x_92_ = lean_apply_1(v_k_86_, v_fvar_91_);
return v___x_92_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim(lean_object* v_motive_93_, lean_object* v_ctorIdx_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_k_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_95_, v_k_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___boxed(lean_object* v_motive_99_, lean_object* v_ctorIdx_100_, lean_object* v_t_101_, lean_object* v_h_102_, lean_object* v_k_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim(v_motive_99_, v_ctorIdx_100_, v_t_101_, v_h_102_, v_k_103_);
lean_dec(v_ctorIdx_100_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_lctx_elim___redArg(lean_object* v_t_105_, lean_object* v_lctx_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_105_, v_lctx_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_lctx_elim(lean_object* v_motive_108_, lean_object* v_t_109_, lean_object* v_h_110_, lean_object* v_lctx_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_109_, v_lctx_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_enumDomain_elim___redArg(lean_object* v_t_113_, lean_object* v_enumDomain_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_113_, v_enumDomain_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_enumDomain_elim(lean_object* v_motive_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_enumDomain_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_117_, v_enumDomain_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_structureProjection_elim___redArg(lean_object* v_t_121_, lean_object* v_structureProjection_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_121_, v_structureProjection_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_structureProjection_elim(lean_object* v_motive_124_, lean_object* v_t_125_, lean_object* v_h_126_, lean_object* v_structureProjection_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_125_, v_structureProjection_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_andFlattened_elim___redArg(lean_object* v_t_129_, lean_object* v_andFlattened_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_129_, v_andFlattened_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_andFlattened_elim(lean_object* v_motive_132_, lean_object* v_t_133_, lean_object* v_h_134_, lean_object* v_andFlattened_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_133_, v_andFlattened_135_);
return v___x_136_;
}
}
static uint64_t _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0(void){
_start:
{
lean_object* v___x_141_; uint64_t v___x_142_; 
v___x_141_ = lean_unsigned_to_nat(1723u);
v___x_142_ = lean_uint64_of_nat(v___x_141_);
return v___x_142_;
}
}
static uint64_t _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__1(void){
_start:
{
uint64_t v___x_143_; uint64_t v___x_144_; uint64_t v___x_145_; 
v___x_143_ = lean_uint64_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0);
v___x_144_ = 1ULL;
v___x_145_ = lean_uint64_mix_hash(v___x_144_, v___x_143_);
return v___x_145_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(lean_object* v_x_146_){
_start:
{
switch(lean_obj_tag(v_x_146_))
{
case 0:
{
lean_object* v_fvar_147_; uint64_t v___x_148_; uint64_t v___x_149_; uint64_t v___x_150_; 
v_fvar_147_ = lean_ctor_get(v_x_146_, 0);
v___x_148_ = 0ULL;
v___x_149_ = l_Lean_instHashableFVarId_hash(v_fvar_147_);
v___x_150_ = lean_uint64_mix_hash(v___x_148_, v___x_149_);
return v___x_150_;
}
case 1:
{
lean_object* v_n_151_; uint64_t v___x_152_; 
v_n_151_ = lean_ctor_get(v_x_146_, 0);
v___x_152_ = 1ULL;
if (lean_obj_tag(v_n_151_) == 0)
{
uint64_t v___x_153_; 
v___x_153_ = lean_uint64_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__1);
return v___x_153_;
}
else
{
uint64_t v_hash_154_; uint64_t v___x_155_; 
v_hash_154_ = lean_ctor_get_uint64(v_n_151_, sizeof(void*)*2);
v___x_155_ = lean_uint64_mix_hash(v___x_152_, v_hash_154_);
return v___x_155_;
}
}
case 2:
{
lean_object* v_e_156_; uint64_t v___x_157_; uint64_t v___x_158_; uint64_t v___x_159_; 
v_e_156_ = lean_ctor_get(v_x_146_, 0);
v___x_157_ = 2ULL;
v___x_158_ = l_Lean_Expr_hash(v_e_156_);
v___x_159_ = lean_uint64_mix_hash(v___x_157_, v___x_158_);
return v___x_159_;
}
default: 
{
lean_object* v_s_160_; uint64_t v___x_161_; uint64_t v___x_162_; uint64_t v___x_163_; 
v_s_160_ = lean_ctor_get(v_x_146_, 0);
v___x_161_ = 3ULL;
v___x_162_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(v_s_160_);
v___x_163_ = lean_uint64_mix_hash(v___x_161_, v___x_162_);
return v___x_163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___boxed(lean_object* v_x_164_){
_start:
{
uint64_t v_res_165_; lean_object* v_r_166_; 
v_res_165_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(v_x_164_);
lean_dec_ref(v_x_164_);
v_r_166_ = lean_box_uint64(v_res_165_);
return v_r_166_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq(lean_object* v_x_169_, lean_object* v_x_170_){
_start:
{
switch(lean_obj_tag(v_x_169_))
{
case 0:
{
if (lean_obj_tag(v_x_170_) == 0)
{
lean_object* v_fvar_171_; lean_object* v_fvar_172_; uint8_t v___x_173_; 
v_fvar_171_ = lean_ctor_get(v_x_169_, 0);
v_fvar_172_ = lean_ctor_get(v_x_170_, 0);
v___x_173_ = l_Lean_instBEqFVarId_beq(v_fvar_171_, v_fvar_172_);
return v___x_173_;
}
else
{
uint8_t v___x_174_; 
v___x_174_ = 0;
return v___x_174_;
}
}
case 1:
{
if (lean_obj_tag(v_x_170_) == 1)
{
lean_object* v_n_175_; lean_object* v_n_176_; uint8_t v___x_177_; 
v_n_175_ = lean_ctor_get(v_x_169_, 0);
v_n_176_ = lean_ctor_get(v_x_170_, 0);
v___x_177_ = lean_name_eq(v_n_175_, v_n_176_);
return v___x_177_;
}
else
{
uint8_t v___x_178_; 
v___x_178_ = 0;
return v___x_178_;
}
}
case 2:
{
if (lean_obj_tag(v_x_170_) == 2)
{
lean_object* v_e_179_; lean_object* v_e_180_; uint8_t v___x_181_; 
v_e_179_ = lean_ctor_get(v_x_169_, 0);
v_e_180_ = lean_ctor_get(v_x_170_, 0);
v___x_181_ = lean_expr_eqv(v_e_179_, v_e_180_);
return v___x_181_;
}
else
{
uint8_t v___x_182_; 
v___x_182_ = 0;
return v___x_182_;
}
}
default: 
{
if (lean_obj_tag(v_x_170_) == 3)
{
lean_object* v_s_183_; lean_object* v_s_184_; 
v_s_183_ = lean_ctor_get(v_x_169_, 0);
v_s_184_ = lean_ctor_get(v_x_170_, 0);
v_x_169_ = v_s_183_;
v_x_170_ = v_s_184_;
goto _start;
}
else
{
uint8_t v___x_186_; 
v___x_186_ = 0;
return v___x_186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq___boxed(lean_object* v_x_187_, lean_object* v_x_188_){
_start:
{
uint8_t v_res_189_; lean_object* v_r_190_; 
v_res_189_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq(v_x_187_, v_x_188_);
lean_dec_ref(v_x_188_);
lean_dec_ref(v_x_187_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(lean_object* v_s_193_){
_start:
{
if (lean_obj_tag(v_s_193_) == 3)
{
lean_object* v_s_194_; 
v_s_194_ = lean_ctor_get(v_s_193_, 0);
v_s_193_ = v_s_194_;
goto _start;
}
else
{
lean_inc_ref(v_s_193_);
return v_s_193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten___boxed(lean_object* v_s_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(v_s_196_);
lean_dec_ref(v_s_196_);
return v_res_197_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__0));
v___x_200_ = l_Lean_stringToMessageData(v___x_199_);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__2));
v___x_203_ = l_Lean_stringToMessageData(v___x_202_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__4));
v___x_206_ = l_Lean_stringToMessageData(v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__6));
v___x_209_ = l_Lean_stringToMessageData(v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(lean_object* v_s_210_){
_start:
{
switch(lean_obj_tag(v_s_210_))
{
case 0:
{
lean_object* v_fvar_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_fvar_211_ = lean_ctor_get(v_s_210_, 0);
lean_inc(v_fvar_211_);
lean_dec_ref_known(v_s_210_, 1);
v___x_212_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1);
v___x_213_ = l_Lean_mkFVar(v_fvar_211_);
v___x_214_ = l_Lean_MessageData_ofExpr(v___x_213_);
v___x_215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_212_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
return v___x_215_;
}
case 1:
{
lean_object* v_n_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_n_216_ = lean_ctor_get(v_s_210_, 0);
lean_inc(v_n_216_);
lean_dec_ref_known(v_s_210_, 1);
v___x_217_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3);
v___x_218_ = l_Lean_MessageData_ofName(v_n_216_);
v___x_219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
return v___x_219_;
}
case 2:
{
lean_object* v_e_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_e_220_ = lean_ctor_get(v_s_210_, 0);
lean_inc_ref(v_e_220_);
lean_dec_ref_known(v_s_210_, 1);
v___x_221_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5);
v___x_222_ = l_Lean_MessageData_ofExpr(v_e_220_);
v___x_223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
return v___x_223_;
}
default: 
{
lean_object* v_s_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_s_224_ = lean_ctor_get(v_s_210_, 0);
lean_inc_ref(v_s_224_);
lean_dec_ref_known(v_s_210_, 1);
v___x_225_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7);
v___x_226_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(v_s_224_);
lean_dec_ref(v_s_224_);
v___x_227_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(v___x_226_);
v___x_228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_225_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
return v___x_228_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = lean_box(0);
v___x_235_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__1));
v___x_236_ = l_Lean_Expr_const___override(v___x_235_, v___x_234_);
return v___x_236_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_237_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default));
v___x_238_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2);
v___x_239_ = lean_box(0);
v___x_240_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_238_);
lean_ctor_set(v___x_240_, 2, v___x_238_);
lean_ctor_set(v___x_240_, 3, v___x_237_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default(void){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp(void){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default;
return v___x_242_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0(lean_object* v_lhs_243_, lean_object* v_rhs_244_){
_start:
{
lean_object* v_type_245_; lean_object* v_type_246_; uint8_t v___x_247_; 
v_type_245_ = lean_ctor_get(v_lhs_243_, 1);
v_type_246_ = lean_ctor_get(v_rhs_244_, 1);
v___x_247_ = lean_expr_eqv(v_type_245_, v_type_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0___boxed(lean_object* v_lhs_248_, lean_object* v_rhs_249_){
_start:
{
uint8_t v_res_250_; lean_object* v_r_251_; 
v_res_250_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0(v_lhs_248_, v_rhs_249_);
lean_dec_ref(v_rhs_249_);
lean_dec_ref(v_lhs_248_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0(lean_object* v_hyp_254_){
_start:
{
lean_object* v_type_255_; uint64_t v___x_256_; 
v_type_255_ = lean_ctor_get(v_hyp_254_, 1);
v___x_256_ = l_Lean_Expr_hash(v_type_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0___boxed(lean_object* v_hyp_257_){
_start:
{
uint64_t v_res_258_; lean_object* v_r_259_; 
v_res_258_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0(v_hyp_257_);
lean_dec_ref(v_hyp_257_);
v_r_259_ = lean_box_uint64(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___lam__0(lean_object* v_hyp_262_){
_start:
{
lean_object* v_type_263_; lean_object* v___x_264_; 
v_type_263_ = lean_ctor_get(v_hyp_262_, 1);
lean_inc_ref(v_type_263_);
lean_dec_ref(v_hyp_262_);
v___x_264_ = l_Lean_MessageData_ofExpr(v_type_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(lean_object* v_hyp_272_, lean_object* v_result_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
if (lean_obj_tag(v_result_273_) == 0)
{
lean_object* v___x_280_; 
lean_dec_ref_known(v_result_273_, 0);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v_hyp_272_);
return v___x_280_;
}
else
{
lean_object* v_e_x27_281_; lean_object* v_proof_282_; lean_object* v_name_283_; lean_object* v_type_284_; lean_object* v_value_285_; lean_object* v_source_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_315_; 
v_e_x27_281_ = lean_ctor_get(v_result_273_, 0);
lean_inc_ref(v_e_x27_281_);
v_proof_282_ = lean_ctor_get(v_result_273_, 1);
lean_inc_ref(v_proof_282_);
lean_dec_ref_known(v_result_273_, 2);
v_name_283_ = lean_ctor_get(v_hyp_272_, 0);
v_type_284_ = lean_ctor_get(v_hyp_272_, 1);
v_value_285_ = lean_ctor_get(v_hyp_272_, 2);
v_source_286_ = lean_ctor_get(v_hyp_272_, 3);
v_isSharedCheck_315_ = !lean_is_exclusive(v_hyp_272_);
if (v_isSharedCheck_315_ == 0)
{
v___x_288_ = v_hyp_272_;
v_isShared_289_ = v_isSharedCheck_315_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_source_286_);
lean_inc(v_value_285_);
lean_inc(v_type_284_);
lean_inc(v_name_283_);
lean_dec(v_hyp_272_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_315_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; 
lean_inc_ref(v_type_284_);
v___x_290_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_284_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_306_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_306_ == 0)
{
v___x_293_ = v___x_290_;
v_isShared_294_ = v_isSharedCheck_306_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_290_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_306_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_295_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2));
v___x_296_ = lean_box(0);
v___x_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_297_, 0, v_a_291_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = l_Lean_mkConst(v___x_295_, v___x_297_);
lean_inc_ref(v_e_x27_281_);
v___x_299_ = l_Lean_mkApp4(v___x_298_, v_type_284_, v_e_x27_281_, v_proof_282_, v_value_285_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 2, v___x_299_);
lean_ctor_set(v___x_288_, 1, v_e_x27_281_);
v___x_301_ = v___x_288_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_name_283_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_e_x27_281_);
lean_ctor_set(v_reuseFailAlloc_305_, 2, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_305_, 3, v_source_286_);
v___x_301_ = v_reuseFailAlloc_305_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_303_; 
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_301_);
v___x_303_ = v___x_293_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_del_object(v___x_288_);
lean_dec_ref(v_source_286_);
lean_dec_ref(v_value_285_);
lean_dec_ref(v_type_284_);
lean_dec(v_name_283_);
lean_dec_ref(v_proof_282_);
lean_dec_ref(v_e_x27_281_);
v_a_307_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_290_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_290_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___boxed(lean_object* v_hyp_316_, lean_object* v_result_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_316_, v_result_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult(lean_object* v_hyp_325_, lean_object* v_result_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_325_, v_result_326_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___boxed(lean_object* v_hyp_335_, lean_object* v_result_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult(v_hyp_335_, v_result_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(lean_object* v_hyp_345_, lean_object* v_result_346_){
_start:
{
lean_object* v_name_348_; lean_object* v_type_349_; lean_object* v_value_350_; lean_object* v_source_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_360_; 
v_name_348_ = lean_ctor_get(v_hyp_345_, 0);
v_type_349_ = lean_ctor_get(v_hyp_345_, 1);
v_value_350_ = lean_ctor_get(v_hyp_345_, 2);
v_source_351_ = lean_ctor_get(v_hyp_345_, 3);
v_isSharedCheck_360_ = !lean_is_exclusive(v_hyp_345_);
if (v_isSharedCheck_360_ == 0)
{
v___x_353_ = v_hyp_345_;
v_isShared_354_ = v_isSharedCheck_360_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_source_351_);
lean_inc(v_value_350_);
lean_inc(v_type_349_);
lean_inc(v_name_348_);
lean_dec(v_hyp_345_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_360_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_355_ = l_Lean_Meta_Sym_DSimp_Result_getResultExpr(v_type_349_, v_result_346_);
lean_dec_ref(v_type_349_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v___x_355_);
v___x_357_ = v___x_353_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_name_348_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_359_, 2, v_value_350_);
lean_ctor_set(v_reuseFailAlloc_359_, 3, v_source_351_);
v___x_357_ = v_reuseFailAlloc_359_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; 
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg___boxed(lean_object* v_hyp_361_, lean_object* v_result_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_361_, v_result_362_);
lean_dec_ref(v_result_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult(lean_object* v_hyp_365_, lean_object* v_result_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_365_, v_result_366_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___boxed(lean_object* v_hyp_375_, lean_object* v_result_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult(v_hyp_375_, v_result_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec_ref(v_result_376_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(lean_object* v_a_385_){
_start:
{
lean_object* v___x_387_; 
lean_inc_ref(v_a_385_);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v_a_385_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg___boxed(lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(v_a_388_);
lean_dec_ref(v_a_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___x_400_; 
lean_inc_ref(v_a_391_);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v_a_391_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___boxed(lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal___redArg(lean_object* v_a_411_){
_start:
{
lean_object* v___x_413_; lean_object* v_goal_414_; lean_object* v___x_415_; 
v___x_413_ = lean_st_ref_get(v_a_411_);
v_goal_414_ = lean_ctor_get(v___x_413_, 4);
lean_inc(v_goal_414_);
lean_dec(v___x_413_);
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v_goal_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal___redArg___boxed(lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal___redArg(v_a_416_);
lean_dec(v_a_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal(lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v___x_428_; lean_object* v_goal_429_; lean_object* v___x_430_; 
v___x_428_ = lean_st_ref_get(v_a_420_);
v_goal_429_ = lean_ctor_get(v___x_428_, 4);
lean_inc(v_goal_429_);
lean_dec(v___x_428_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v_goal_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal___boxed(lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal(v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setGoal___redArg(lean_object* v_g_441_, lean_object* v_a_442_){
_start:
{
lean_object* v___x_444_; lean_object* v_fst_446_; lean_object* v_snd_447_; lean_object* v_rewriteSimpCache_450_; lean_object* v_rewriteDSimpCache_451_; lean_object* v_acCache_452_; lean_object* v_typeAnalysis_453_; lean_object* v_goal_454_; lean_object* v_hypotheses_455_; uint8_t v_didChange_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_469_; 
v___x_444_ = lean_st_ref_take(v_a_442_);
v_rewriteSimpCache_450_ = lean_ctor_get(v___x_444_, 0);
v_rewriteDSimpCache_451_ = lean_ctor_get(v___x_444_, 1);
v_acCache_452_ = lean_ctor_get(v___x_444_, 2);
v_typeAnalysis_453_ = lean_ctor_get(v___x_444_, 3);
v_goal_454_ = lean_ctor_get(v___x_444_, 4);
v_hypotheses_455_ = lean_ctor_get(v___x_444_, 5);
v_didChange_456_ = lean_ctor_get_uint8(v___x_444_, sizeof(void*)*6);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_469_ == 0)
{
v___x_458_ = v___x_444_;
v_isShared_459_ = v_isSharedCheck_469_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_hypotheses_455_);
lean_inc(v_goal_454_);
lean_inc(v_typeAnalysis_453_);
lean_inc(v_acCache_452_);
lean_inc(v_rewriteDSimpCache_451_);
lean_inc(v_rewriteSimpCache_450_);
lean_dec(v___x_444_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_469_;
goto v_resetjp_457_;
}
v___jp_445_:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_st_ref_set(v_a_442_, v_snd_447_);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v_fst_446_);
return v___x_449_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; uint8_t v___y_462_; 
v___x_460_ = lean_box(0);
if (v_didChange_456_ == 0)
{
uint8_t v___x_466_; 
v___x_466_ = l_Lean_instBEqMVarId_beq(v_g_441_, v_goal_454_);
lean_dec(v_goal_454_);
if (v___x_466_ == 0)
{
uint8_t v___x_467_; 
v___x_467_ = 1;
v___y_462_ = v___x_467_;
goto v___jp_461_;
}
else
{
v___y_462_ = v_didChange_456_;
goto v___jp_461_;
}
}
else
{
lean_object* v___x_468_; 
lean_del_object(v___x_458_);
lean_dec(v_goal_454_);
v___x_468_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_468_, 0, v_rewriteSimpCache_450_);
lean_ctor_set(v___x_468_, 1, v_rewriteDSimpCache_451_);
lean_ctor_set(v___x_468_, 2, v_acCache_452_);
lean_ctor_set(v___x_468_, 3, v_typeAnalysis_453_);
lean_ctor_set(v___x_468_, 4, v_g_441_);
lean_ctor_set(v___x_468_, 5, v_hypotheses_455_);
lean_ctor_set_uint8(v___x_468_, sizeof(void*)*6, v_didChange_456_);
v_fst_446_ = v___x_460_;
v_snd_447_ = v___x_468_;
goto v___jp_445_;
}
v___jp_461_:
{
lean_object* v___x_464_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 4, v_g_441_);
v___x_464_ = v___x_458_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_rewriteSimpCache_450_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_rewriteDSimpCache_451_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v_acCache_452_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v_typeAnalysis_453_);
lean_ctor_set(v_reuseFailAlloc_465_, 4, v_g_441_);
lean_ctor_set(v_reuseFailAlloc_465_, 5, v_hypotheses_455_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_ctor_set_uint8(v___x_464_, sizeof(void*)*6, v___y_462_);
v_fst_446_ = v___x_460_;
v_snd_447_ = v___x_464_;
goto v___jp_445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setGoal___redArg___boxed(lean_object* v_g_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setGoal___redArg(v_g_470_, v_a_471_);
lean_dec(v_a_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setGoal(lean_object* v_g_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v___x_484_; lean_object* v_fst_486_; lean_object* v_snd_487_; lean_object* v_rewriteSimpCache_490_; lean_object* v_rewriteDSimpCache_491_; lean_object* v_acCache_492_; lean_object* v_typeAnalysis_493_; lean_object* v_goal_494_; lean_object* v_hypotheses_495_; uint8_t v_didChange_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_509_; 
v___x_484_ = lean_st_ref_take(v_a_476_);
v_rewriteSimpCache_490_ = lean_ctor_get(v___x_484_, 0);
v_rewriteDSimpCache_491_ = lean_ctor_get(v___x_484_, 1);
v_acCache_492_ = lean_ctor_get(v___x_484_, 2);
v_typeAnalysis_493_ = lean_ctor_get(v___x_484_, 3);
v_goal_494_ = lean_ctor_get(v___x_484_, 4);
v_hypotheses_495_ = lean_ctor_get(v___x_484_, 5);
v_didChange_496_ = lean_ctor_get_uint8(v___x_484_, sizeof(void*)*6);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_509_ == 0)
{
v___x_498_ = v___x_484_;
v_isShared_499_ = v_isSharedCheck_509_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_hypotheses_495_);
lean_inc(v_goal_494_);
lean_inc(v_typeAnalysis_493_);
lean_inc(v_acCache_492_);
lean_inc(v_rewriteDSimpCache_491_);
lean_inc(v_rewriteSimpCache_490_);
lean_dec(v___x_484_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_509_;
goto v_resetjp_497_;
}
v___jp_485_:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_st_ref_set(v_a_476_, v_snd_487_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v_fst_486_);
return v___x_489_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; uint8_t v___y_502_; 
v___x_500_ = lean_box(0);
if (v_didChange_496_ == 0)
{
uint8_t v___x_506_; 
v___x_506_ = l_Lean_instBEqMVarId_beq(v_g_474_, v_goal_494_);
lean_dec(v_goal_494_);
if (v___x_506_ == 0)
{
uint8_t v___x_507_; 
v___x_507_ = 1;
v___y_502_ = v___x_507_;
goto v___jp_501_;
}
else
{
v___y_502_ = v_didChange_496_;
goto v___jp_501_;
}
}
else
{
lean_object* v___x_508_; 
lean_del_object(v___x_498_);
lean_dec(v_goal_494_);
v___x_508_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_508_, 0, v_rewriteSimpCache_490_);
lean_ctor_set(v___x_508_, 1, v_rewriteDSimpCache_491_);
lean_ctor_set(v___x_508_, 2, v_acCache_492_);
lean_ctor_set(v___x_508_, 3, v_typeAnalysis_493_);
lean_ctor_set(v___x_508_, 4, v_g_474_);
lean_ctor_set(v___x_508_, 5, v_hypotheses_495_);
lean_ctor_set_uint8(v___x_508_, sizeof(void*)*6, v_didChange_496_);
v_fst_486_ = v___x_500_;
v_snd_487_ = v___x_508_;
goto v___jp_485_;
}
v___jp_501_:
{
lean_object* v___x_504_; 
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 4, v_g_474_);
v___x_504_ = v___x_498_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_rewriteSimpCache_490_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_rewriteDSimpCache_491_);
lean_ctor_set(v_reuseFailAlloc_505_, 2, v_acCache_492_);
lean_ctor_set(v_reuseFailAlloc_505_, 3, v_typeAnalysis_493_);
lean_ctor_set(v_reuseFailAlloc_505_, 4, v_g_474_);
lean_ctor_set(v_reuseFailAlloc_505_, 5, v_hypotheses_495_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*6, v___y_502_);
v_fst_486_ = v___x_500_;
v_snd_487_ = v___x_504_;
goto v___jp_485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setGoal___boxed(lean_object* v_g_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setGoal(v_g_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(lean_object* v_a_521_){
_start:
{
lean_object* v___x_523_; uint8_t v_didChange_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_523_ = lean_st_ref_get(v_a_521_);
v_didChange_524_ = lean_ctor_get_uint8(v___x_523_, sizeof(void*)*6);
lean_dec(v___x_523_);
v___x_525_ = lean_box(v_didChange_524_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg___boxed(lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(v_a_527_);
lean_dec(v_a_527_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v___x_539_; uint8_t v_didChange_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_539_ = lean_st_ref_get(v_a_531_);
v_didChange_540_ = lean_ctor_get_uint8(v___x_539_, sizeof(void*)*6);
lean_dec(v___x_539_);
v___x_541_ = lean_box(v_didChange_540_);
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___boxed(lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(lean_object* v_a_553_){
_start:
{
lean_object* v___x_555_; lean_object* v_rewriteSimpCache_556_; lean_object* v_rewriteDSimpCache_557_; lean_object* v_acCache_558_; lean_object* v_typeAnalysis_559_; lean_object* v_goal_560_; lean_object* v_hypotheses_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_572_; 
v___x_555_ = lean_st_ref_take(v_a_553_);
v_rewriteSimpCache_556_ = lean_ctor_get(v___x_555_, 0);
v_rewriteDSimpCache_557_ = lean_ctor_get(v___x_555_, 1);
v_acCache_558_ = lean_ctor_get(v___x_555_, 2);
v_typeAnalysis_559_ = lean_ctor_get(v___x_555_, 3);
v_goal_560_ = lean_ctor_get(v___x_555_, 4);
v_hypotheses_561_ = lean_ctor_get(v___x_555_, 5);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_572_ == 0)
{
v___x_563_ = v___x_555_;
v_isShared_564_ = v_isSharedCheck_572_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_hypotheses_561_);
lean_inc(v_goal_560_);
lean_inc(v_typeAnalysis_559_);
lean_inc(v_acCache_558_);
lean_inc(v_rewriteDSimpCache_557_);
lean_inc(v_rewriteSimpCache_556_);
lean_dec(v___x_555_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_572_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
uint8_t v___x_565_; lean_object* v___x_567_; 
v___x_565_ = 0;
if (v_isShared_564_ == 0)
{
v___x_567_ = v___x_563_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_rewriteSimpCache_556_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_rewriteDSimpCache_557_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_acCache_558_);
lean_ctor_set(v_reuseFailAlloc_571_, 3, v_typeAnalysis_559_);
lean_ctor_set(v_reuseFailAlloc_571_, 4, v_goal_560_);
lean_ctor_set(v_reuseFailAlloc_571_, 5, v_hypotheses_561_);
v___x_567_ = v_reuseFailAlloc_571_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
lean_ctor_set_uint8(v___x_567_, sizeof(void*)*6, v___x_565_);
v___x_568_ = lean_st_ref_set(v_a_553_, v___x_567_);
v___x_569_ = lean_box(0);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg___boxed(lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(v_a_573_);
lean_dec(v_a_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_585_; lean_object* v_rewriteSimpCache_586_; lean_object* v_rewriteDSimpCache_587_; lean_object* v_acCache_588_; lean_object* v_typeAnalysis_589_; lean_object* v_goal_590_; lean_object* v_hypotheses_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_602_; 
v___x_585_ = lean_st_ref_take(v_a_577_);
v_rewriteSimpCache_586_ = lean_ctor_get(v___x_585_, 0);
v_rewriteDSimpCache_587_ = lean_ctor_get(v___x_585_, 1);
v_acCache_588_ = lean_ctor_get(v___x_585_, 2);
v_typeAnalysis_589_ = lean_ctor_get(v___x_585_, 3);
v_goal_590_ = lean_ctor_get(v___x_585_, 4);
v_hypotheses_591_ = lean_ctor_get(v___x_585_, 5);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_602_ == 0)
{
v___x_593_ = v___x_585_;
v_isShared_594_ = v_isSharedCheck_602_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_hypotheses_591_);
lean_inc(v_goal_590_);
lean_inc(v_typeAnalysis_589_);
lean_inc(v_acCache_588_);
lean_inc(v_rewriteDSimpCache_587_);
lean_inc(v_rewriteSimpCache_586_);
lean_dec(v___x_585_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_602_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
uint8_t v___x_595_; lean_object* v___x_597_; 
v___x_595_ = 0;
if (v_isShared_594_ == 0)
{
v___x_597_ = v___x_593_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_rewriteSimpCache_586_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_rewriteDSimpCache_587_);
lean_ctor_set(v_reuseFailAlloc_601_, 2, v_acCache_588_);
lean_ctor_set(v_reuseFailAlloc_601_, 3, v_typeAnalysis_589_);
lean_ctor_set(v_reuseFailAlloc_601_, 4, v_goal_590_);
lean_ctor_set(v_reuseFailAlloc_601_, 5, v_hypotheses_591_);
v___x_597_ = v_reuseFailAlloc_601_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*6, v___x_595_);
v___x_598_ = lean_st_ref_set(v_a_577_, v___x_597_);
v___x_599_ = lean_box(0);
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___boxed(lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(lean_object* v_a_613_){
_start:
{
lean_object* v___x_615_; lean_object* v_rewriteSimpCache_616_; lean_object* v_rewriteDSimpCache_617_; lean_object* v_acCache_618_; lean_object* v_typeAnalysis_619_; lean_object* v_goal_620_; lean_object* v_hypotheses_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_632_; 
v___x_615_ = lean_st_ref_take(v_a_613_);
v_rewriteSimpCache_616_ = lean_ctor_get(v___x_615_, 0);
v_rewriteDSimpCache_617_ = lean_ctor_get(v___x_615_, 1);
v_acCache_618_ = lean_ctor_get(v___x_615_, 2);
v_typeAnalysis_619_ = lean_ctor_get(v___x_615_, 3);
v_goal_620_ = lean_ctor_get(v___x_615_, 4);
v_hypotheses_621_ = lean_ctor_get(v___x_615_, 5);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_632_ == 0)
{
v___x_623_ = v___x_615_;
v_isShared_624_ = v_isSharedCheck_632_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_hypotheses_621_);
lean_inc(v_goal_620_);
lean_inc(v_typeAnalysis_619_);
lean_inc(v_acCache_618_);
lean_inc(v_rewriteDSimpCache_617_);
lean_inc(v_rewriteSimpCache_616_);
lean_dec(v___x_615_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_632_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
uint8_t v___x_625_; lean_object* v___x_627_; 
v___x_625_ = 1;
if (v_isShared_624_ == 0)
{
v___x_627_ = v___x_623_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_rewriteSimpCache_616_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_rewriteDSimpCache_617_);
lean_ctor_set(v_reuseFailAlloc_631_, 2, v_acCache_618_);
lean_ctor_set(v_reuseFailAlloc_631_, 3, v_typeAnalysis_619_);
lean_ctor_set(v_reuseFailAlloc_631_, 4, v_goal_620_);
lean_ctor_set(v_reuseFailAlloc_631_, 5, v_hypotheses_621_);
v___x_627_ = v_reuseFailAlloc_631_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
lean_ctor_set_uint8(v___x_627_, sizeof(void*)*6, v___x_625_);
v___x_628_ = lean_st_ref_set(v_a_613_, v___x_627_);
v___x_629_ = lean_box(0);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg___boxed(lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(v_a_633_);
lean_dec(v_a_633_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v___x_645_; lean_object* v_rewriteSimpCache_646_; lean_object* v_rewriteDSimpCache_647_; lean_object* v_acCache_648_; lean_object* v_typeAnalysis_649_; lean_object* v_goal_650_; lean_object* v_hypotheses_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_662_; 
v___x_645_ = lean_st_ref_take(v_a_637_);
v_rewriteSimpCache_646_ = lean_ctor_get(v___x_645_, 0);
v_rewriteDSimpCache_647_ = lean_ctor_get(v___x_645_, 1);
v_acCache_648_ = lean_ctor_get(v___x_645_, 2);
v_typeAnalysis_649_ = lean_ctor_get(v___x_645_, 3);
v_goal_650_ = lean_ctor_get(v___x_645_, 4);
v_hypotheses_651_ = lean_ctor_get(v___x_645_, 5);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_662_ == 0)
{
v___x_653_ = v___x_645_;
v_isShared_654_ = v_isSharedCheck_662_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_hypotheses_651_);
lean_inc(v_goal_650_);
lean_inc(v_typeAnalysis_649_);
lean_inc(v_acCache_648_);
lean_inc(v_rewriteDSimpCache_647_);
lean_inc(v_rewriteSimpCache_646_);
lean_dec(v___x_645_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_662_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
uint8_t v___x_655_; lean_object* v___x_657_; 
v___x_655_ = 1;
if (v_isShared_654_ == 0)
{
v___x_657_ = v___x_653_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_rewriteSimpCache_646_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_rewriteDSimpCache_647_);
lean_ctor_set(v_reuseFailAlloc_661_, 2, v_acCache_648_);
lean_ctor_set(v_reuseFailAlloc_661_, 3, v_typeAnalysis_649_);
lean_ctor_set(v_reuseFailAlloc_661_, 4, v_goal_650_);
lean_ctor_set(v_reuseFailAlloc_661_, 5, v_hypotheses_651_);
v___x_657_ = v_reuseFailAlloc_661_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
lean_ctor_set_uint8(v___x_657_, sizeof(void*)*6, v___x_655_);
v___x_658_ = lean_st_ref_set(v_a_637_, v___x_657_);
v___x_659_ = lean_box(0);
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
return v___x_660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed(lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
return v_res_672_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__0(void){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_673_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__0);
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg(lean_object* v_a_676_){
_start:
{
lean_object* v___x_678_; lean_object* v_rewriteSimpCache_679_; lean_object* v_rewriteDSimpCache_680_; lean_object* v_acCache_681_; lean_object* v_typeAnalysis_682_; lean_object* v_goal_683_; lean_object* v_hypotheses_684_; uint8_t v_didChange_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_695_; 
v___x_678_ = lean_st_ref_take(v_a_676_);
v_rewriteSimpCache_679_ = lean_ctor_get(v___x_678_, 0);
v_rewriteDSimpCache_680_ = lean_ctor_get(v___x_678_, 1);
v_acCache_681_ = lean_ctor_get(v___x_678_, 2);
v_typeAnalysis_682_ = lean_ctor_get(v___x_678_, 3);
v_goal_683_ = lean_ctor_get(v___x_678_, 4);
v_hypotheses_684_ = lean_ctor_get(v___x_678_, 5);
v_didChange_685_ = lean_ctor_get_uint8(v___x_678_, sizeof(void*)*6);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_695_ == 0)
{
v___x_687_ = v___x_678_;
v_isShared_688_ = v_isSharedCheck_695_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_hypotheses_684_);
lean_inc(v_goal_683_);
lean_inc(v_typeAnalysis_682_);
lean_inc(v_acCache_681_);
lean_inc(v_rewriteDSimpCache_680_);
lean_inc(v_rewriteSimpCache_679_);
lean_dec(v___x_678_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_695_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_689_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_rewriteDSimpCache_680_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v_acCache_681_);
lean_ctor_set(v_reuseFailAlloc_694_, 3, v_typeAnalysis_682_);
lean_ctor_set(v_reuseFailAlloc_694_, 4, v_goal_683_);
lean_ctor_set(v_reuseFailAlloc_694_, 5, v_hypotheses_684_);
lean_ctor_set_uint8(v_reuseFailAlloc_694_, sizeof(void*)*6, v_didChange_685_);
v___x_691_ = v_reuseFailAlloc_694_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_st_ref_set(v_a_676_, v___x_691_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v_rewriteSimpCache_679_);
return v___x_693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___boxed(lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg(v_a_696_);
lean_dec(v_a_696_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache(lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v___x_708_; lean_object* v_rewriteSimpCache_709_; lean_object* v_rewriteDSimpCache_710_; lean_object* v_acCache_711_; lean_object* v_typeAnalysis_712_; lean_object* v_goal_713_; lean_object* v_hypotheses_714_; uint8_t v_didChange_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_725_; 
v___x_708_ = lean_st_ref_take(v_a_700_);
v_rewriteSimpCache_709_ = lean_ctor_get(v___x_708_, 0);
v_rewriteDSimpCache_710_ = lean_ctor_get(v___x_708_, 1);
v_acCache_711_ = lean_ctor_get(v___x_708_, 2);
v_typeAnalysis_712_ = lean_ctor_get(v___x_708_, 3);
v_goal_713_ = lean_ctor_get(v___x_708_, 4);
v_hypotheses_714_ = lean_ctor_get(v___x_708_, 5);
v_didChange_715_ = lean_ctor_get_uint8(v___x_708_, sizeof(void*)*6);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_725_ == 0)
{
v___x_717_ = v___x_708_;
v_isShared_718_ = v_isSharedCheck_725_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_hypotheses_714_);
lean_inc(v_goal_713_);
lean_inc(v_typeAnalysis_712_);
lean_inc(v_acCache_711_);
lean_inc(v_rewriteDSimpCache_710_);
lean_inc(v_rewriteSimpCache_709_);
lean_dec(v___x_708_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_725_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_719_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_719_);
v___x_721_ = v___x_717_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_rewriteDSimpCache_710_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v_acCache_711_);
lean_ctor_set(v_reuseFailAlloc_724_, 3, v_typeAnalysis_712_);
lean_ctor_set(v_reuseFailAlloc_724_, 4, v_goal_713_);
lean_ctor_set(v_reuseFailAlloc_724_, 5, v_hypotheses_714_);
lean_ctor_set_uint8(v_reuseFailAlloc_724_, sizeof(void*)*6, v_didChange_715_);
v___x_721_ = v_reuseFailAlloc_724_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_st_ref_set(v_a_700_, v___x_721_);
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v_rewriteSimpCache_709_);
return v___x_723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___boxed(lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache(v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
lean_dec_ref(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___redArg(lean_object* v_cache_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_739_; lean_object* v_rewriteDSimpCache_740_; lean_object* v_acCache_741_; lean_object* v_typeAnalysis_742_; lean_object* v_goal_743_; lean_object* v_hypotheses_744_; uint8_t v_didChange_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_755_; 
v___x_739_ = lean_st_ref_take(v_a_737_);
v_rewriteDSimpCache_740_ = lean_ctor_get(v___x_739_, 1);
v_acCache_741_ = lean_ctor_get(v___x_739_, 2);
v_typeAnalysis_742_ = lean_ctor_get(v___x_739_, 3);
v_goal_743_ = lean_ctor_get(v___x_739_, 4);
v_hypotheses_744_ = lean_ctor_get(v___x_739_, 5);
v_didChange_745_ = lean_ctor_get_uint8(v___x_739_, sizeof(void*)*6);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; 
v_unused_756_ = lean_ctor_get(v___x_739_, 0);
lean_dec(v_unused_756_);
v___x_747_ = v___x_739_;
v_isShared_748_ = v_isSharedCheck_755_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_hypotheses_744_);
lean_inc(v_goal_743_);
lean_inc(v_typeAnalysis_742_);
lean_inc(v_acCache_741_);
lean_inc(v_rewriteDSimpCache_740_);
lean_dec(v___x_739_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_755_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v_cache_736_);
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_cache_736_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_rewriteDSimpCache_740_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_acCache_741_);
lean_ctor_set(v_reuseFailAlloc_754_, 3, v_typeAnalysis_742_);
lean_ctor_set(v_reuseFailAlloc_754_, 4, v_goal_743_);
lean_ctor_set(v_reuseFailAlloc_754_, 5, v_hypotheses_744_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*6, v_didChange_745_);
v___x_750_ = v_reuseFailAlloc_754_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_751_ = lean_st_ref_set(v_a_737_, v___x_750_);
v___x_752_ = lean_box(0);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___redArg___boxed(lean_object* v_cache_757_, lean_object* v_a_758_, lean_object* v_a_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___redArg(v_cache_757_, v_a_758_);
lean_dec(v_a_758_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache(lean_object* v_cache_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v___x_771_; lean_object* v_rewriteDSimpCache_772_; lean_object* v_acCache_773_; lean_object* v_typeAnalysis_774_; lean_object* v_goal_775_; lean_object* v_hypotheses_776_; uint8_t v_didChange_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_787_; 
v___x_771_ = lean_st_ref_take(v_a_763_);
v_rewriteDSimpCache_772_ = lean_ctor_get(v___x_771_, 1);
v_acCache_773_ = lean_ctor_get(v___x_771_, 2);
v_typeAnalysis_774_ = lean_ctor_get(v___x_771_, 3);
v_goal_775_ = lean_ctor_get(v___x_771_, 4);
v_hypotheses_776_ = lean_ctor_get(v___x_771_, 5);
v_didChange_777_ = lean_ctor_get_uint8(v___x_771_, sizeof(void*)*6);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; 
v_unused_788_ = lean_ctor_get(v___x_771_, 0);
lean_dec(v_unused_788_);
v___x_779_ = v___x_771_;
v_isShared_780_ = v_isSharedCheck_787_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_hypotheses_776_);
lean_inc(v_goal_775_);
lean_inc(v_typeAnalysis_774_);
lean_inc(v_acCache_773_);
lean_inc(v_rewriteDSimpCache_772_);
lean_dec(v___x_771_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_787_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v_cache_761_);
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_cache_761_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_rewriteDSimpCache_772_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v_acCache_773_);
lean_ctor_set(v_reuseFailAlloc_786_, 3, v_typeAnalysis_774_);
lean_ctor_set(v_reuseFailAlloc_786_, 4, v_goal_775_);
lean_ctor_set(v_reuseFailAlloc_786_, 5, v_hypotheses_776_);
lean_ctor_set_uint8(v_reuseFailAlloc_786_, sizeof(void*)*6, v_didChange_777_);
v___x_782_ = v_reuseFailAlloc_786_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_783_ = lean_st_ref_set(v_a_763_, v___x_782_);
v___x_784_ = lean_box(0);
v___x_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
return v___x_785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___boxed(lean_object* v_cache_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache(v_cache_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___redArg(lean_object* v_a_800_){
_start:
{
lean_object* v___x_802_; lean_object* v_rewriteDSimpCache_803_; lean_object* v_acCache_804_; lean_object* v_typeAnalysis_805_; lean_object* v_goal_806_; lean_object* v_hypotheses_807_; uint8_t v_didChange_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_819_; 
v___x_802_ = lean_st_ref_take(v_a_800_);
v_rewriteDSimpCache_803_ = lean_ctor_get(v___x_802_, 1);
v_acCache_804_ = lean_ctor_get(v___x_802_, 2);
v_typeAnalysis_805_ = lean_ctor_get(v___x_802_, 3);
v_goal_806_ = lean_ctor_get(v___x_802_, 4);
v_hypotheses_807_ = lean_ctor_get(v___x_802_, 5);
v_didChange_808_ = lean_ctor_get_uint8(v___x_802_, sizeof(void*)*6);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v___x_802_, 0);
lean_dec(v_unused_820_);
v___x_810_ = v___x_802_;
v_isShared_811_ = v_isSharedCheck_819_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_hypotheses_807_);
lean_inc(v_goal_806_);
lean_inc(v_typeAnalysis_805_);
lean_inc(v_acCache_804_);
lean_inc(v_rewriteDSimpCache_803_);
lean_dec(v___x_802_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_819_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_812_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_812_);
v___x_814_ = v___x_810_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_rewriteDSimpCache_803_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v_acCache_804_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v_typeAnalysis_805_);
lean_ctor_set(v_reuseFailAlloc_818_, 4, v_goal_806_);
lean_ctor_set(v_reuseFailAlloc_818_, 5, v_hypotheses_807_);
lean_ctor_set_uint8(v_reuseFailAlloc_818_, sizeof(void*)*6, v_didChange_808_);
v___x_814_ = v_reuseFailAlloc_818_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = lean_st_ref_set(v_a_800_, v___x_814_);
v___x_816_ = lean_box(0);
v___x_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
return v___x_817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___redArg___boxed(lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___redArg(v_a_821_);
lean_dec(v_a_821_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache(lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v___x_833_; lean_object* v_rewriteDSimpCache_834_; lean_object* v_acCache_835_; lean_object* v_typeAnalysis_836_; lean_object* v_goal_837_; lean_object* v_hypotheses_838_; uint8_t v_didChange_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_850_; 
v___x_833_ = lean_st_ref_take(v_a_825_);
v_rewriteDSimpCache_834_ = lean_ctor_get(v___x_833_, 1);
v_acCache_835_ = lean_ctor_get(v___x_833_, 2);
v_typeAnalysis_836_ = lean_ctor_get(v___x_833_, 3);
v_goal_837_ = lean_ctor_get(v___x_833_, 4);
v_hypotheses_838_ = lean_ctor_get(v___x_833_, 5);
v_didChange_839_ = lean_ctor_get_uint8(v___x_833_, sizeof(void*)*6);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; 
v_unused_851_ = lean_ctor_get(v___x_833_, 0);
lean_dec(v_unused_851_);
v___x_841_ = v___x_833_;
v_isShared_842_ = v_isSharedCheck_850_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_hypotheses_838_);
lean_inc(v_goal_837_);
lean_inc(v_typeAnalysis_836_);
lean_inc(v_acCache_835_);
lean_inc(v_rewriteDSimpCache_834_);
lean_dec(v___x_833_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_850_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_843_);
v___x_845_ = v___x_841_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_rewriteDSimpCache_834_);
lean_ctor_set(v_reuseFailAlloc_849_, 2, v_acCache_835_);
lean_ctor_set(v_reuseFailAlloc_849_, 3, v_typeAnalysis_836_);
lean_ctor_set(v_reuseFailAlloc_849_, 4, v_goal_837_);
lean_ctor_set(v_reuseFailAlloc_849_, 5, v_hypotheses_838_);
lean_ctor_set_uint8(v_reuseFailAlloc_849_, sizeof(void*)*6, v_didChange_839_);
v___x_845_ = v_reuseFailAlloc_849_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_846_ = lean_st_ref_set(v_a_825_, v___x_845_);
v___x_847_ = lean_box(0);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___boxed(lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache(v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
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
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__0(void){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_862_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__0);
v___x_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg(lean_object* v_a_865_){
_start:
{
lean_object* v___x_867_; lean_object* v_rewriteSimpCache_868_; lean_object* v_rewriteDSimpCache_869_; lean_object* v_acCache_870_; lean_object* v_typeAnalysis_871_; lean_object* v_goal_872_; lean_object* v_hypotheses_873_; uint8_t v_didChange_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_884_; 
v___x_867_ = lean_st_ref_take(v_a_865_);
v_rewriteSimpCache_868_ = lean_ctor_get(v___x_867_, 0);
v_rewriteDSimpCache_869_ = lean_ctor_get(v___x_867_, 1);
v_acCache_870_ = lean_ctor_get(v___x_867_, 2);
v_typeAnalysis_871_ = lean_ctor_get(v___x_867_, 3);
v_goal_872_ = lean_ctor_get(v___x_867_, 4);
v_hypotheses_873_ = lean_ctor_get(v___x_867_, 5);
v_didChange_874_ = lean_ctor_get_uint8(v___x_867_, sizeof(void*)*6);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_884_ == 0)
{
v___x_876_ = v___x_867_;
v_isShared_877_ = v_isSharedCheck_884_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_hypotheses_873_);
lean_inc(v_goal_872_);
lean_inc(v_typeAnalysis_871_);
lean_inc(v_acCache_870_);
lean_inc(v_rewriteDSimpCache_869_);
lean_inc(v_rewriteSimpCache_868_);
lean_dec(v___x_867_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_884_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_878_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v___x_878_);
v___x_880_ = v___x_876_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_rewriteSimpCache_868_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_883_, 2, v_acCache_870_);
lean_ctor_set(v_reuseFailAlloc_883_, 3, v_typeAnalysis_871_);
lean_ctor_set(v_reuseFailAlloc_883_, 4, v_goal_872_);
lean_ctor_set(v_reuseFailAlloc_883_, 5, v_hypotheses_873_);
lean_ctor_set_uint8(v_reuseFailAlloc_883_, sizeof(void*)*6, v_didChange_874_);
v___x_880_ = v_reuseFailAlloc_883_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_st_ref_set(v_a_865_, v___x_880_);
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v_rewriteDSimpCache_869_);
return v___x_882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___boxed(lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg(v_a_885_);
lean_dec(v_a_885_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache(lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v___x_897_; lean_object* v_rewriteSimpCache_898_; lean_object* v_rewriteDSimpCache_899_; lean_object* v_acCache_900_; lean_object* v_typeAnalysis_901_; lean_object* v_goal_902_; lean_object* v_hypotheses_903_; uint8_t v_didChange_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_914_; 
v___x_897_ = lean_st_ref_take(v_a_889_);
v_rewriteSimpCache_898_ = lean_ctor_get(v___x_897_, 0);
v_rewriteDSimpCache_899_ = lean_ctor_get(v___x_897_, 1);
v_acCache_900_ = lean_ctor_get(v___x_897_, 2);
v_typeAnalysis_901_ = lean_ctor_get(v___x_897_, 3);
v_goal_902_ = lean_ctor_get(v___x_897_, 4);
v_hypotheses_903_ = lean_ctor_get(v___x_897_, 5);
v_didChange_904_ = lean_ctor_get_uint8(v___x_897_, sizeof(void*)*6);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_914_ == 0)
{
v___x_906_ = v___x_897_;
v_isShared_907_ = v_isSharedCheck_914_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_hypotheses_903_);
lean_inc(v_goal_902_);
lean_inc(v_typeAnalysis_901_);
lean_inc(v_acCache_900_);
lean_inc(v_rewriteDSimpCache_899_);
lean_inc(v_rewriteSimpCache_898_);
lean_dec(v___x_897_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_914_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_908_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 1, v___x_908_);
v___x_910_ = v___x_906_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_rewriteSimpCache_898_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_acCache_900_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_typeAnalysis_901_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_goal_902_);
lean_ctor_set(v_reuseFailAlloc_913_, 5, v_hypotheses_903_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*6, v_didChange_904_);
v___x_910_ = v_reuseFailAlloc_913_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_st_ref_set(v_a_889_, v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v_rewriteDSimpCache_899_);
return v___x_912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___boxed(lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache(v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___redArg(lean_object* v_cache_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___x_928_; lean_object* v_rewriteSimpCache_929_; lean_object* v_acCache_930_; lean_object* v_typeAnalysis_931_; lean_object* v_goal_932_; lean_object* v_hypotheses_933_; uint8_t v_didChange_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_944_; 
v___x_928_ = lean_st_ref_take(v_a_926_);
v_rewriteSimpCache_929_ = lean_ctor_get(v___x_928_, 0);
v_acCache_930_ = lean_ctor_get(v___x_928_, 2);
v_typeAnalysis_931_ = lean_ctor_get(v___x_928_, 3);
v_goal_932_ = lean_ctor_get(v___x_928_, 4);
v_hypotheses_933_ = lean_ctor_get(v___x_928_, 5);
v_didChange_934_ = lean_ctor_get_uint8(v___x_928_, sizeof(void*)*6);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_944_ == 0)
{
lean_object* v_unused_945_; 
v_unused_945_ = lean_ctor_get(v___x_928_, 1);
lean_dec(v_unused_945_);
v___x_936_ = v___x_928_;
v_isShared_937_ = v_isSharedCheck_944_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_hypotheses_933_);
lean_inc(v_goal_932_);
lean_inc(v_typeAnalysis_931_);
lean_inc(v_acCache_930_);
lean_inc(v_rewriteSimpCache_929_);
lean_dec(v___x_928_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_944_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 1, v_cache_925_);
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_rewriteSimpCache_929_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_cache_925_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v_acCache_930_);
lean_ctor_set(v_reuseFailAlloc_943_, 3, v_typeAnalysis_931_);
lean_ctor_set(v_reuseFailAlloc_943_, 4, v_goal_932_);
lean_ctor_set(v_reuseFailAlloc_943_, 5, v_hypotheses_933_);
lean_ctor_set_uint8(v_reuseFailAlloc_943_, sizeof(void*)*6, v_didChange_934_);
v___x_939_ = v_reuseFailAlloc_943_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = lean_st_ref_set(v_a_926_, v___x_939_);
v___x_941_ = lean_box(0);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
return v___x_942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___redArg___boxed(lean_object* v_cache_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___redArg(v_cache_946_, v_a_947_);
lean_dec(v_a_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache(lean_object* v_cache_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v___x_960_; lean_object* v_rewriteSimpCache_961_; lean_object* v_acCache_962_; lean_object* v_typeAnalysis_963_; lean_object* v_goal_964_; lean_object* v_hypotheses_965_; uint8_t v_didChange_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_976_; 
v___x_960_ = lean_st_ref_take(v_a_952_);
v_rewriteSimpCache_961_ = lean_ctor_get(v___x_960_, 0);
v_acCache_962_ = lean_ctor_get(v___x_960_, 2);
v_typeAnalysis_963_ = lean_ctor_get(v___x_960_, 3);
v_goal_964_ = lean_ctor_get(v___x_960_, 4);
v_hypotheses_965_ = lean_ctor_get(v___x_960_, 5);
v_didChange_966_ = lean_ctor_get_uint8(v___x_960_, sizeof(void*)*6);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v___x_960_, 1);
lean_dec(v_unused_977_);
v___x_968_ = v___x_960_;
v_isShared_969_ = v_isSharedCheck_976_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_hypotheses_965_);
lean_inc(v_goal_964_);
lean_inc(v_typeAnalysis_963_);
lean_inc(v_acCache_962_);
lean_inc(v_rewriteSimpCache_961_);
lean_dec(v___x_960_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_976_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 1, v_cache_950_);
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_rewriteSimpCache_961_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_cache_950_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_acCache_962_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v_typeAnalysis_963_);
lean_ctor_set(v_reuseFailAlloc_975_, 4, v_goal_964_);
lean_ctor_set(v_reuseFailAlloc_975_, 5, v_hypotheses_965_);
lean_ctor_set_uint8(v_reuseFailAlloc_975_, sizeof(void*)*6, v_didChange_966_);
v___x_971_ = v_reuseFailAlloc_975_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = lean_st_ref_set(v_a_952_, v___x_971_);
v___x_973_ = lean_box(0);
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___boxed(lean_object* v_cache_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache(v_cache_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___redArg(lean_object* v_a_989_){
_start:
{
lean_object* v___x_991_; lean_object* v_rewriteSimpCache_992_; lean_object* v_acCache_993_; lean_object* v_typeAnalysis_994_; lean_object* v_goal_995_; lean_object* v_hypotheses_996_; uint8_t v_didChange_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1008_; 
v___x_991_ = lean_st_ref_take(v_a_989_);
v_rewriteSimpCache_992_ = lean_ctor_get(v___x_991_, 0);
v_acCache_993_ = lean_ctor_get(v___x_991_, 2);
v_typeAnalysis_994_ = lean_ctor_get(v___x_991_, 3);
v_goal_995_ = lean_ctor_get(v___x_991_, 4);
v_hypotheses_996_ = lean_ctor_get(v___x_991_, 5);
v_didChange_997_ = lean_ctor_get_uint8(v___x_991_, sizeof(void*)*6);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1008_ == 0)
{
lean_object* v_unused_1009_; 
v_unused_1009_ = lean_ctor_get(v___x_991_, 1);
lean_dec(v_unused_1009_);
v___x_999_ = v___x_991_;
v_isShared_1000_ = v_isSharedCheck_1008_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_hypotheses_996_);
lean_inc(v_goal_995_);
lean_inc(v_typeAnalysis_994_);
lean_inc(v_acCache_993_);
lean_inc(v_rewriteSimpCache_992_);
lean_dec(v___x_991_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1008_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_1001_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 1, v___x_1001_);
v___x_1003_ = v___x_999_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_rewriteSimpCache_992_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v_acCache_993_);
lean_ctor_set(v_reuseFailAlloc_1007_, 3, v_typeAnalysis_994_);
lean_ctor_set(v_reuseFailAlloc_1007_, 4, v_goal_995_);
lean_ctor_set(v_reuseFailAlloc_1007_, 5, v_hypotheses_996_);
lean_ctor_set_uint8(v_reuseFailAlloc_1007_, sizeof(void*)*6, v_didChange_997_);
v___x_1003_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = lean_st_ref_set(v_a_989_, v___x_1003_);
v___x_1005_ = lean_box(0);
v___x_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___redArg___boxed(lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___redArg(v_a_1010_);
lean_dec(v_a_1010_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache(lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v___x_1022_; lean_object* v_rewriteSimpCache_1023_; lean_object* v_acCache_1024_; lean_object* v_typeAnalysis_1025_; lean_object* v_goal_1026_; lean_object* v_hypotheses_1027_; uint8_t v_didChange_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1039_; 
v___x_1022_ = lean_st_ref_take(v_a_1014_);
v_rewriteSimpCache_1023_ = lean_ctor_get(v___x_1022_, 0);
v_acCache_1024_ = lean_ctor_get(v___x_1022_, 2);
v_typeAnalysis_1025_ = lean_ctor_get(v___x_1022_, 3);
v_goal_1026_ = lean_ctor_get(v___x_1022_, 4);
v_hypotheses_1027_ = lean_ctor_get(v___x_1022_, 5);
v_didChange_1028_ = lean_ctor_get_uint8(v___x_1022_, sizeof(void*)*6);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; 
v_unused_1040_ = lean_ctor_get(v___x_1022_, 1);
lean_dec(v_unused_1040_);
v___x_1030_ = v___x_1022_;
v_isShared_1031_ = v_isSharedCheck_1039_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_hypotheses_1027_);
lean_inc(v_goal_1026_);
lean_inc(v_typeAnalysis_1025_);
lean_inc(v_acCache_1024_);
lean_inc(v_rewriteSimpCache_1023_);
lean_dec(v___x_1022_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1039_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1032_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 1, v___x_1032_);
v___x_1034_ = v___x_1030_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_rewriteSimpCache_1023_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1038_, 2, v_acCache_1024_);
lean_ctor_set(v_reuseFailAlloc_1038_, 3, v_typeAnalysis_1025_);
lean_ctor_set(v_reuseFailAlloc_1038_, 4, v_goal_1026_);
lean_ctor_set(v_reuseFailAlloc_1038_, 5, v_hypotheses_1027_);
lean_ctor_set_uint8(v_reuseFailAlloc_1038_, sizeof(void*)*6, v_didChange_1028_);
v___x_1034_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1035_ = lean_st_ref_set(v_a_1014_, v___x_1034_);
v___x_1036_ = lean_box(0);
v___x_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
return v___x_1037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___boxed(lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache(v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___redArg(lean_object* v_a_1051_){
_start:
{
lean_object* v___x_1053_; lean_object* v_rewriteSimpCache_1054_; lean_object* v_rewriteDSimpCache_1055_; lean_object* v_acCache_1056_; lean_object* v_typeAnalysis_1057_; lean_object* v_goal_1058_; lean_object* v_hypotheses_1059_; uint8_t v_didChange_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1070_; 
v___x_1053_ = lean_st_ref_take(v_a_1051_);
v_rewriteSimpCache_1054_ = lean_ctor_get(v___x_1053_, 0);
v_rewriteDSimpCache_1055_ = lean_ctor_get(v___x_1053_, 1);
v_acCache_1056_ = lean_ctor_get(v___x_1053_, 2);
v_typeAnalysis_1057_ = lean_ctor_get(v___x_1053_, 3);
v_goal_1058_ = lean_ctor_get(v___x_1053_, 4);
v_hypotheses_1059_ = lean_ctor_get(v___x_1053_, 5);
v_didChange_1060_ = lean_ctor_get_uint8(v___x_1053_, sizeof(void*)*6);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1062_ = v___x_1053_;
v_isShared_1063_ = v_isSharedCheck_1070_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_hypotheses_1059_);
lean_inc(v_goal_1058_);
lean_inc(v_typeAnalysis_1057_);
lean_inc(v_acCache_1056_);
lean_inc(v_rewriteDSimpCache_1055_);
lean_inc(v_rewriteSimpCache_1054_);
lean_dec(v___x_1053_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1070_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1064_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 2, v___x_1064_);
v___x_1066_ = v___x_1062_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_rewriteSimpCache_1054_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_rewriteDSimpCache_1055_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1069_, 3, v_typeAnalysis_1057_);
lean_ctor_set(v_reuseFailAlloc_1069_, 4, v_goal_1058_);
lean_ctor_set(v_reuseFailAlloc_1069_, 5, v_hypotheses_1059_);
lean_ctor_set_uint8(v_reuseFailAlloc_1069_, sizeof(void*)*6, v_didChange_1060_);
v___x_1066_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_st_ref_set(v_a_1051_, v___x_1066_);
v___x_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1068_, 0, v_acCache_1056_);
return v___x_1068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___redArg___boxed(lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___redArg(v_a_1071_);
lean_dec(v_a_1071_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache(lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v___x_1083_; lean_object* v_rewriteSimpCache_1084_; lean_object* v_rewriteDSimpCache_1085_; lean_object* v_acCache_1086_; lean_object* v_typeAnalysis_1087_; lean_object* v_goal_1088_; lean_object* v_hypotheses_1089_; uint8_t v_didChange_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1100_; 
v___x_1083_ = lean_st_ref_take(v_a_1075_);
v_rewriteSimpCache_1084_ = lean_ctor_get(v___x_1083_, 0);
v_rewriteDSimpCache_1085_ = lean_ctor_get(v___x_1083_, 1);
v_acCache_1086_ = lean_ctor_get(v___x_1083_, 2);
v_typeAnalysis_1087_ = lean_ctor_get(v___x_1083_, 3);
v_goal_1088_ = lean_ctor_get(v___x_1083_, 4);
v_hypotheses_1089_ = lean_ctor_get(v___x_1083_, 5);
v_didChange_1090_ = lean_ctor_get_uint8(v___x_1083_, sizeof(void*)*6);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1092_ = v___x_1083_;
v_isShared_1093_ = v_isSharedCheck_1100_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_hypotheses_1089_);
lean_inc(v_goal_1088_);
lean_inc(v_typeAnalysis_1087_);
lean_inc(v_acCache_1086_);
lean_inc(v_rewriteDSimpCache_1085_);
lean_inc(v_rewriteSimpCache_1084_);
lean_dec(v___x_1083_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1100_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1094_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 2, v___x_1094_);
v___x_1096_ = v___x_1092_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_rewriteSimpCache_1084_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_rewriteDSimpCache_1085_);
lean_ctor_set(v_reuseFailAlloc_1099_, 2, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1099_, 3, v_typeAnalysis_1087_);
lean_ctor_set(v_reuseFailAlloc_1099_, 4, v_goal_1088_);
lean_ctor_set(v_reuseFailAlloc_1099_, 5, v_hypotheses_1089_);
lean_ctor_set_uint8(v_reuseFailAlloc_1099_, sizeof(void*)*6, v_didChange_1090_);
v___x_1096_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = lean_st_ref_set(v_a_1075_, v___x_1096_);
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v_acCache_1086_);
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___boxed(lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache(v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___redArg(lean_object* v_cache_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v___x_1114_; lean_object* v_rewriteSimpCache_1115_; lean_object* v_rewriteDSimpCache_1116_; lean_object* v_typeAnalysis_1117_; lean_object* v_goal_1118_; lean_object* v_hypotheses_1119_; uint8_t v_didChange_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1130_; 
v___x_1114_ = lean_st_ref_take(v_a_1112_);
v_rewriteSimpCache_1115_ = lean_ctor_get(v___x_1114_, 0);
v_rewriteDSimpCache_1116_ = lean_ctor_get(v___x_1114_, 1);
v_typeAnalysis_1117_ = lean_ctor_get(v___x_1114_, 3);
v_goal_1118_ = lean_ctor_get(v___x_1114_, 4);
v_hypotheses_1119_ = lean_ctor_get(v___x_1114_, 5);
v_didChange_1120_ = lean_ctor_get_uint8(v___x_1114_, sizeof(void*)*6);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1130_ == 0)
{
lean_object* v_unused_1131_; 
v_unused_1131_ = lean_ctor_get(v___x_1114_, 2);
lean_dec(v_unused_1131_);
v___x_1122_ = v___x_1114_;
v_isShared_1123_ = v_isSharedCheck_1130_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_hypotheses_1119_);
lean_inc(v_goal_1118_);
lean_inc(v_typeAnalysis_1117_);
lean_inc(v_rewriteDSimpCache_1116_);
lean_inc(v_rewriteSimpCache_1115_);
lean_dec(v___x_1114_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1130_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 2, v_cache_1111_);
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_rewriteSimpCache_1115_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_rewriteDSimpCache_1116_);
lean_ctor_set(v_reuseFailAlloc_1129_, 2, v_cache_1111_);
lean_ctor_set(v_reuseFailAlloc_1129_, 3, v_typeAnalysis_1117_);
lean_ctor_set(v_reuseFailAlloc_1129_, 4, v_goal_1118_);
lean_ctor_set(v_reuseFailAlloc_1129_, 5, v_hypotheses_1119_);
lean_ctor_set_uint8(v_reuseFailAlloc_1129_, sizeof(void*)*6, v_didChange_1120_);
v___x_1125_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = lean_st_ref_set(v_a_1112_, v___x_1125_);
v___x_1127_ = lean_box(0);
v___x_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
return v___x_1128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___redArg___boxed(lean_object* v_cache_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___redArg(v_cache_1132_, v_a_1133_);
lean_dec(v_a_1133_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache(lean_object* v_cache_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v___x_1146_; lean_object* v_rewriteSimpCache_1147_; lean_object* v_rewriteDSimpCache_1148_; lean_object* v_typeAnalysis_1149_; lean_object* v_goal_1150_; lean_object* v_hypotheses_1151_; uint8_t v_didChange_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1162_; 
v___x_1146_ = lean_st_ref_take(v_a_1138_);
v_rewriteSimpCache_1147_ = lean_ctor_get(v___x_1146_, 0);
v_rewriteDSimpCache_1148_ = lean_ctor_get(v___x_1146_, 1);
v_typeAnalysis_1149_ = lean_ctor_get(v___x_1146_, 3);
v_goal_1150_ = lean_ctor_get(v___x_1146_, 4);
v_hypotheses_1151_ = lean_ctor_get(v___x_1146_, 5);
v_didChange_1152_ = lean_ctor_get_uint8(v___x_1146_, sizeof(void*)*6);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; 
v_unused_1163_ = lean_ctor_get(v___x_1146_, 2);
lean_dec(v_unused_1163_);
v___x_1154_ = v___x_1146_;
v_isShared_1155_ = v_isSharedCheck_1162_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_hypotheses_1151_);
lean_inc(v_goal_1150_);
lean_inc(v_typeAnalysis_1149_);
lean_inc(v_rewriteDSimpCache_1148_);
lean_inc(v_rewriteSimpCache_1147_);
lean_dec(v___x_1146_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1162_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 2, v_cache_1136_);
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_rewriteSimpCache_1147_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_rewriteDSimpCache_1148_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_cache_1136_);
lean_ctor_set(v_reuseFailAlloc_1161_, 3, v_typeAnalysis_1149_);
lean_ctor_set(v_reuseFailAlloc_1161_, 4, v_goal_1150_);
lean_ctor_set(v_reuseFailAlloc_1161_, 5, v_hypotheses_1151_);
lean_ctor_set_uint8(v_reuseFailAlloc_1161_, sizeof(void*)*6, v_didChange_1152_);
v___x_1157_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = lean_st_ref_set(v_a_1138_, v___x_1157_);
v___x_1159_ = lean_box(0);
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
return v___x_1160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___boxed(lean_object* v_cache_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache(v_cache_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___redArg(lean_object* v_a_1175_){
_start:
{
lean_object* v___x_1177_; lean_object* v_rewriteSimpCache_1178_; lean_object* v_rewriteDSimpCache_1179_; lean_object* v_typeAnalysis_1180_; lean_object* v_goal_1181_; lean_object* v_hypotheses_1182_; uint8_t v_didChange_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1194_; 
v___x_1177_ = lean_st_ref_take(v_a_1175_);
v_rewriteSimpCache_1178_ = lean_ctor_get(v___x_1177_, 0);
v_rewriteDSimpCache_1179_ = lean_ctor_get(v___x_1177_, 1);
v_typeAnalysis_1180_ = lean_ctor_get(v___x_1177_, 3);
v_goal_1181_ = lean_ctor_get(v___x_1177_, 4);
v_hypotheses_1182_ = lean_ctor_get(v___x_1177_, 5);
v_didChange_1183_ = lean_ctor_get_uint8(v___x_1177_, sizeof(void*)*6);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1194_ == 0)
{
lean_object* v_unused_1195_; 
v_unused_1195_ = lean_ctor_get(v___x_1177_, 2);
lean_dec(v_unused_1195_);
v___x_1185_ = v___x_1177_;
v_isShared_1186_ = v_isSharedCheck_1194_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_hypotheses_1182_);
lean_inc(v_goal_1181_);
lean_inc(v_typeAnalysis_1180_);
lean_inc(v_rewriteDSimpCache_1179_);
lean_inc(v_rewriteSimpCache_1178_);
lean_dec(v___x_1177_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1194_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1187_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 2, v___x_1187_);
v___x_1189_ = v___x_1185_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_rewriteSimpCache_1178_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_rewriteDSimpCache_1179_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1193_, 3, v_typeAnalysis_1180_);
lean_ctor_set(v_reuseFailAlloc_1193_, 4, v_goal_1181_);
lean_ctor_set(v_reuseFailAlloc_1193_, 5, v_hypotheses_1182_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*6, v_didChange_1183_);
v___x_1189_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1190_ = lean_st_ref_set(v_a_1175_, v___x_1189_);
v___x_1191_ = lean_box(0);
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
return v___x_1192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___redArg___boxed(lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___redArg(v_a_1196_);
lean_dec(v_a_1196_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache(lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v___x_1208_; lean_object* v_rewriteSimpCache_1209_; lean_object* v_rewriteDSimpCache_1210_; lean_object* v_typeAnalysis_1211_; lean_object* v_goal_1212_; lean_object* v_hypotheses_1213_; uint8_t v_didChange_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1225_; 
v___x_1208_ = lean_st_ref_take(v_a_1200_);
v_rewriteSimpCache_1209_ = lean_ctor_get(v___x_1208_, 0);
v_rewriteDSimpCache_1210_ = lean_ctor_get(v___x_1208_, 1);
v_typeAnalysis_1211_ = lean_ctor_get(v___x_1208_, 3);
v_goal_1212_ = lean_ctor_get(v___x_1208_, 4);
v_hypotheses_1213_ = lean_ctor_get(v___x_1208_, 5);
v_didChange_1214_ = lean_ctor_get_uint8(v___x_1208_, sizeof(void*)*6);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; 
v_unused_1226_ = lean_ctor_get(v___x_1208_, 2);
lean_dec(v_unused_1226_);
v___x_1216_ = v___x_1208_;
v_isShared_1217_ = v_isSharedCheck_1225_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_hypotheses_1213_);
lean_inc(v_goal_1212_);
lean_inc(v_typeAnalysis_1211_);
lean_inc(v_rewriteDSimpCache_1210_);
lean_inc(v_rewriteSimpCache_1209_);
lean_dec(v___x_1208_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1225_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1218_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 2, v___x_1218_);
v___x_1220_ = v___x_1216_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_rewriteSimpCache_1209_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_rewriteDSimpCache_1210_);
lean_ctor_set(v_reuseFailAlloc_1224_, 2, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1224_, 3, v_typeAnalysis_1211_);
lean_ctor_set(v_reuseFailAlloc_1224_, 4, v_goal_1212_);
lean_ctor_set(v_reuseFailAlloc_1224_, 5, v_hypotheses_1213_);
lean_ctor_set_uint8(v_reuseFailAlloc_1224_, sizeof(void*)*6, v_didChange_1214_);
v___x_1220_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = lean_st_ref_set(v_a_1200_, v___x_1220_);
v___x_1222_ = lean_box(0);
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
return v___x_1223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___boxed(lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache(v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg(lean_object* v_a_1237_){
_start:
{
lean_object* v___x_1239_; lean_object* v_rewriteDSimpCache_1240_; lean_object* v_acCache_1241_; lean_object* v_typeAnalysis_1242_; lean_object* v_goal_1243_; lean_object* v_hypotheses_1244_; uint8_t v_didChange_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1288_; 
v___x_1239_ = lean_st_ref_take(v_a_1237_);
v_rewriteDSimpCache_1240_ = lean_ctor_get(v___x_1239_, 1);
v_acCache_1241_ = lean_ctor_get(v___x_1239_, 2);
v_typeAnalysis_1242_ = lean_ctor_get(v___x_1239_, 3);
v_goal_1243_ = lean_ctor_get(v___x_1239_, 4);
v_hypotheses_1244_ = lean_ctor_get(v___x_1239_, 5);
v_didChange_1245_ = lean_ctor_get_uint8(v___x_1239_, sizeof(void*)*6);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; 
v_unused_1289_ = lean_ctor_get(v___x_1239_, 0);
lean_dec(v_unused_1289_);
v___x_1247_ = v___x_1239_;
v_isShared_1248_ = v_isSharedCheck_1288_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_hypotheses_1244_);
lean_inc(v_goal_1243_);
lean_inc(v_typeAnalysis_1242_);
lean_inc(v_acCache_1241_);
lean_inc(v_rewriteDSimpCache_1240_);
lean_dec(v___x_1239_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1288_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1249_);
v___x_1251_ = v___x_1247_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_rewriteDSimpCache_1240_);
lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_acCache_1241_);
lean_ctor_set(v_reuseFailAlloc_1287_, 3, v_typeAnalysis_1242_);
lean_ctor_set(v_reuseFailAlloc_1287_, 4, v_goal_1243_);
lean_ctor_set(v_reuseFailAlloc_1287_, 5, v_hypotheses_1244_);
lean_ctor_set_uint8(v_reuseFailAlloc_1287_, sizeof(void*)*6, v_didChange_1245_);
v___x_1251_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v_rewriteSimpCache_1254_; lean_object* v_acCache_1255_; lean_object* v_typeAnalysis_1256_; lean_object* v_goal_1257_; lean_object* v_hypotheses_1258_; uint8_t v_didChange_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1285_; 
v___x_1252_ = lean_st_ref_set(v_a_1237_, v___x_1251_);
v___x_1253_ = lean_st_ref_take(v_a_1237_);
v_rewriteSimpCache_1254_ = lean_ctor_get(v___x_1253_, 0);
v_acCache_1255_ = lean_ctor_get(v___x_1253_, 2);
v_typeAnalysis_1256_ = lean_ctor_get(v___x_1253_, 3);
v_goal_1257_ = lean_ctor_get(v___x_1253_, 4);
v_hypotheses_1258_ = lean_ctor_get(v___x_1253_, 5);
v_didChange_1259_ = lean_ctor_get_uint8(v___x_1253_, sizeof(void*)*6);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1285_ == 0)
{
lean_object* v_unused_1286_; 
v_unused_1286_ = lean_ctor_get(v___x_1253_, 1);
lean_dec(v_unused_1286_);
v___x_1261_ = v___x_1253_;
v_isShared_1262_ = v_isSharedCheck_1285_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_hypotheses_1258_);
lean_inc(v_goal_1257_);
lean_inc(v_typeAnalysis_1256_);
lean_inc(v_acCache_1255_);
lean_inc(v_rewriteSimpCache_1254_);
lean_dec(v___x_1253_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1285_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v___x_1249_);
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_rewriteSimpCache_1254_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_acCache_1255_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v_typeAnalysis_1256_);
lean_ctor_set(v_reuseFailAlloc_1284_, 4, v_goal_1257_);
lean_ctor_set(v_reuseFailAlloc_1284_, 5, v_hypotheses_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*6, v_didChange_1259_);
v___x_1264_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_rewriteSimpCache_1267_; lean_object* v_rewriteDSimpCache_1268_; lean_object* v_typeAnalysis_1269_; lean_object* v_goal_1270_; lean_object* v_hypotheses_1271_; uint8_t v_didChange_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1282_; 
v___x_1265_ = lean_st_ref_set(v_a_1237_, v___x_1264_);
v___x_1266_ = lean_st_ref_take(v_a_1237_);
v_rewriteSimpCache_1267_ = lean_ctor_get(v___x_1266_, 0);
v_rewriteDSimpCache_1268_ = lean_ctor_get(v___x_1266_, 1);
v_typeAnalysis_1269_ = lean_ctor_get(v___x_1266_, 3);
v_goal_1270_ = lean_ctor_get(v___x_1266_, 4);
v_hypotheses_1271_ = lean_ctor_get(v___x_1266_, 5);
v_didChange_1272_ = lean_ctor_get_uint8(v___x_1266_, sizeof(void*)*6);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1282_ == 0)
{
lean_object* v_unused_1283_; 
v_unused_1283_ = lean_ctor_get(v___x_1266_, 2);
lean_dec(v_unused_1283_);
v___x_1274_ = v___x_1266_;
v_isShared_1275_ = v_isSharedCheck_1282_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_hypotheses_1271_);
lean_inc(v_goal_1270_);
lean_inc(v_typeAnalysis_1269_);
lean_inc(v_rewriteDSimpCache_1268_);
lean_inc(v_rewriteSimpCache_1267_);
lean_dec(v___x_1266_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1282_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 2, v___x_1249_);
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_rewriteSimpCache_1267_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_rewriteDSimpCache_1268_);
lean_ctor_set(v_reuseFailAlloc_1281_, 2, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1281_, 3, v_typeAnalysis_1269_);
lean_ctor_set(v_reuseFailAlloc_1281_, 4, v_goal_1270_);
lean_ctor_set(v_reuseFailAlloc_1281_, 5, v_hypotheses_1271_);
lean_ctor_set_uint8(v_reuseFailAlloc_1281_, sizeof(void*)*6, v_didChange_1272_);
v___x_1277_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1278_ = lean_st_ref_set(v_a_1237_, v___x_1277_);
v___x_1279_ = lean_box(0);
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
return v___x_1280_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg___boxed(lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg(v_a_1290_);
lean_dec(v_a_1290_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches(lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg(v_a_1294_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___boxed(lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches(v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(lean_object* v_a_1313_){
_start:
{
lean_object* v___x_1315_; lean_object* v_typeAnalysis_1316_; lean_object* v___x_1317_; 
v___x_1315_ = lean_st_ref_get(v_a_1313_);
v_typeAnalysis_1316_ = lean_ctor_get(v___x_1315_, 3);
lean_inc_ref(v_typeAnalysis_1316_);
lean_dec(v___x_1315_);
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v_typeAnalysis_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg___boxed(lean_object* v_a_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(v_a_1318_);
lean_dec(v_a_1318_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v___x_1330_; lean_object* v_typeAnalysis_1331_; lean_object* v___x_1332_; 
v___x_1330_ = lean_st_ref_get(v_a_1322_);
v_typeAnalysis_1331_ = lean_ctor_get(v___x_1330_, 3);
lean_inc_ref(v_typeAnalysis_1331_);
lean_dec(v___x_1330_);
v___x_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1332_, 0, v_typeAnalysis_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___boxed(lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
lean_dec(v_a_1334_);
lean_dec_ref(v_a_1333_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(lean_object* v_n_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v___x_1351_; lean_object* v_typeAnalysis_1352_; lean_object* v_interestingStructures_1353_; lean_object* v_uninteresting_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1351_ = lean_st_ref_get(v_a_1349_);
v_typeAnalysis_1352_ = lean_ctor_get(v___x_1351_, 3);
lean_inc_ref(v_typeAnalysis_1352_);
lean_dec(v___x_1351_);
v_interestingStructures_1353_ = lean_ctor_get(v_typeAnalysis_1352_, 0);
lean_inc_ref(v_interestingStructures_1353_);
v_uninteresting_1354_ = lean_ctor_get(v_typeAnalysis_1352_, 3);
lean_inc_ref(v_uninteresting_1354_);
lean_dec_ref(v_typeAnalysis_1352_);
v___x_1355_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1356_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
lean_inc(v_n_1348_);
v___x_1357_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1355_, v___x_1356_, v_uninteresting_1354_, v_n_1348_);
lean_dec_ref(v_uninteresting_1354_);
if (v___x_1357_ == 0)
{
uint8_t v___x_1358_; 
v___x_1358_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1355_, v___x_1356_, v_interestingStructures_1353_, v_n_1348_);
lean_dec_ref(v_interestingStructures_1353_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = lean_box(0);
v___x_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
return v___x_1360_;
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1361_ = lean_box(v___x_1358_);
v___x_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
return v___x_1363_;
}
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_dec_ref(v_interestingStructures_1353_);
lean_dec(v_n_1348_);
v___x_1364_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2));
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
return v___x_1365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___boxed(lean_object* v_n_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(v_n_1366_, v_a_1367_);
lean_dec(v_a_1367_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(lean_object* v_n_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v___x_1380_; lean_object* v_typeAnalysis_1381_; lean_object* v_interestingStructures_1382_; lean_object* v_uninteresting_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1380_ = lean_st_ref_get(v_a_1372_);
v_typeAnalysis_1381_ = lean_ctor_get(v___x_1380_, 3);
lean_inc_ref(v_typeAnalysis_1381_);
lean_dec(v___x_1380_);
v_interestingStructures_1382_ = lean_ctor_get(v_typeAnalysis_1381_, 0);
lean_inc_ref(v_interestingStructures_1382_);
v_uninteresting_1383_ = lean_ctor_get(v_typeAnalysis_1381_, 3);
lean_inc_ref(v_uninteresting_1383_);
lean_dec_ref(v_typeAnalysis_1381_);
v___x_1384_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1385_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
lean_inc(v_n_1370_);
v___x_1386_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1384_, v___x_1385_, v_uninteresting_1383_, v_n_1370_);
lean_dec_ref(v_uninteresting_1383_);
if (v___x_1386_ == 0)
{
uint8_t v___x_1387_; 
v___x_1387_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1384_, v___x_1385_, v_interestingStructures_1382_, v_n_1370_);
lean_dec_ref(v_interestingStructures_1382_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_box(0);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
else
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = lean_box(v___x_1387_);
v___x_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
return v___x_1392_;
}
}
else
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
lean_dec_ref(v_interestingStructures_1382_);
lean_dec(v_n_1370_);
v___x_1393_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2));
v___x_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
return v___x_1394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___boxed(lean_object* v_n_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(v_n_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(lean_object* v_f_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v___x_1409_; lean_object* v_rewriteSimpCache_1410_; lean_object* v_rewriteDSimpCache_1411_; lean_object* v_acCache_1412_; lean_object* v_typeAnalysis_1413_; lean_object* v_goal_1414_; lean_object* v_hypotheses_1415_; uint8_t v_didChange_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1427_; 
v___x_1409_ = lean_st_ref_take(v_a_1407_);
v_rewriteSimpCache_1410_ = lean_ctor_get(v___x_1409_, 0);
v_rewriteDSimpCache_1411_ = lean_ctor_get(v___x_1409_, 1);
v_acCache_1412_ = lean_ctor_get(v___x_1409_, 2);
v_typeAnalysis_1413_ = lean_ctor_get(v___x_1409_, 3);
v_goal_1414_ = lean_ctor_get(v___x_1409_, 4);
v_hypotheses_1415_ = lean_ctor_get(v___x_1409_, 5);
v_didChange_1416_ = lean_ctor_get_uint8(v___x_1409_, sizeof(void*)*6);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1418_ = v___x_1409_;
v_isShared_1419_ = v_isSharedCheck_1427_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_hypotheses_1415_);
lean_inc(v_goal_1414_);
lean_inc(v_typeAnalysis_1413_);
lean_inc(v_acCache_1412_);
lean_inc(v_rewriteDSimpCache_1411_);
lean_inc(v_rewriteSimpCache_1410_);
lean_dec(v___x_1409_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1427_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1420_ = lean_apply_1(v_f_1406_, v_typeAnalysis_1413_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 3, v___x_1420_);
v___x_1422_ = v___x_1418_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_rewriteSimpCache_1410_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_rewriteDSimpCache_1411_);
lean_ctor_set(v_reuseFailAlloc_1426_, 2, v_acCache_1412_);
lean_ctor_set(v_reuseFailAlloc_1426_, 3, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1426_, 4, v_goal_1414_);
lean_ctor_set(v_reuseFailAlloc_1426_, 5, v_hypotheses_1415_);
lean_ctor_set_uint8(v_reuseFailAlloc_1426_, sizeof(void*)*6, v_didChange_1416_);
v___x_1422_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = lean_st_ref_set(v_a_1407_, v___x_1422_);
v___x_1424_ = lean_box(0);
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
return v___x_1425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg___boxed(lean_object* v_f_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(v_f_1428_, v_a_1429_);
lean_dec(v_a_1429_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(lean_object* v_f_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v___x_1442_; lean_object* v_rewriteSimpCache_1443_; lean_object* v_rewriteDSimpCache_1444_; lean_object* v_acCache_1445_; lean_object* v_typeAnalysis_1446_; lean_object* v_goal_1447_; lean_object* v_hypotheses_1448_; uint8_t v_didChange_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1460_; 
v___x_1442_ = lean_st_ref_take(v_a_1434_);
v_rewriteSimpCache_1443_ = lean_ctor_get(v___x_1442_, 0);
v_rewriteDSimpCache_1444_ = lean_ctor_get(v___x_1442_, 1);
v_acCache_1445_ = lean_ctor_get(v___x_1442_, 2);
v_typeAnalysis_1446_ = lean_ctor_get(v___x_1442_, 3);
v_goal_1447_ = lean_ctor_get(v___x_1442_, 4);
v_hypotheses_1448_ = lean_ctor_get(v___x_1442_, 5);
v_didChange_1449_ = lean_ctor_get_uint8(v___x_1442_, sizeof(void*)*6);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1451_ = v___x_1442_;
v_isShared_1452_ = v_isSharedCheck_1460_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_hypotheses_1448_);
lean_inc(v_goal_1447_);
lean_inc(v_typeAnalysis_1446_);
lean_inc(v_acCache_1445_);
lean_inc(v_rewriteDSimpCache_1444_);
lean_inc(v_rewriteSimpCache_1443_);
lean_dec(v___x_1442_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1460_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1453_ = lean_apply_1(v_f_1432_, v_typeAnalysis_1446_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 3, v___x_1453_);
v___x_1455_ = v___x_1451_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_rewriteSimpCache_1443_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_rewriteDSimpCache_1444_);
lean_ctor_set(v_reuseFailAlloc_1459_, 2, v_acCache_1445_);
lean_ctor_set(v_reuseFailAlloc_1459_, 3, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1459_, 4, v_goal_1447_);
lean_ctor_set(v_reuseFailAlloc_1459_, 5, v_hypotheses_1448_);
lean_ctor_set_uint8(v_reuseFailAlloc_1459_, sizeof(void*)*6, v_didChange_1449_);
v___x_1455_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1456_ = lean_st_ref_set(v_a_1434_, v___x_1455_);
v___x_1457_ = lean_box(0);
v___x_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
return v___x_1458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___boxed(lean_object* v_f_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(v_f_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(lean_object* v_n_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v___x_1475_; lean_object* v_typeAnalysis_1476_; lean_object* v_rewriteSimpCache_1477_; lean_object* v_rewriteDSimpCache_1478_; lean_object* v_acCache_1479_; lean_object* v_goal_1480_; lean_object* v_hypotheses_1481_; uint8_t v_didChange_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1506_; 
v___x_1475_ = lean_st_ref_take(v_a_1473_);
v_typeAnalysis_1476_ = lean_ctor_get(v___x_1475_, 3);
v_rewriteSimpCache_1477_ = lean_ctor_get(v___x_1475_, 0);
v_rewriteDSimpCache_1478_ = lean_ctor_get(v___x_1475_, 1);
v_acCache_1479_ = lean_ctor_get(v___x_1475_, 2);
v_goal_1480_ = lean_ctor_get(v___x_1475_, 4);
v_hypotheses_1481_ = lean_ctor_get(v___x_1475_, 5);
v_didChange_1482_ = lean_ctor_get_uint8(v___x_1475_, sizeof(void*)*6);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1484_ = v___x_1475_;
v_isShared_1485_ = v_isSharedCheck_1506_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_hypotheses_1481_);
lean_inc(v_goal_1480_);
lean_inc(v_typeAnalysis_1476_);
lean_inc(v_acCache_1479_);
lean_inc(v_rewriteDSimpCache_1478_);
lean_inc(v_rewriteSimpCache_1477_);
lean_dec(v___x_1475_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1506_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v_interestingStructures_1486_; lean_object* v_interestingEnums_1487_; lean_object* v_interestingMatchers_1488_; lean_object* v_uninteresting_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1505_; 
v_interestingStructures_1486_ = lean_ctor_get(v_typeAnalysis_1476_, 0);
v_interestingEnums_1487_ = lean_ctor_get(v_typeAnalysis_1476_, 1);
v_interestingMatchers_1488_ = lean_ctor_get(v_typeAnalysis_1476_, 2);
v_uninteresting_1489_ = lean_ctor_get(v_typeAnalysis_1476_, 3);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_typeAnalysis_1476_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1491_ = v_typeAnalysis_1476_;
v_isShared_1492_ = v_isSharedCheck_1505_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_uninteresting_1489_);
lean_inc(v_interestingMatchers_1488_);
lean_inc(v_interestingEnums_1487_);
lean_inc(v_interestingStructures_1486_);
lean_dec(v_typeAnalysis_1476_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1505_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1493_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1494_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1495_ = lean_box(0);
v___x_1496_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1493_, v___x_1494_, v_interestingStructures_1486_, v_n_1472_, v___x_1495_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v___x_1496_);
v___x_1498_ = v___x_1491_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_interestingEnums_1487_);
lean_ctor_set(v_reuseFailAlloc_1504_, 2, v_interestingMatchers_1488_);
lean_ctor_set(v_reuseFailAlloc_1504_, 3, v_uninteresting_1489_);
v___x_1498_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1500_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 3, v___x_1498_);
v___x_1500_ = v___x_1484_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_rewriteSimpCache_1477_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_rewriteDSimpCache_1478_);
lean_ctor_set(v_reuseFailAlloc_1503_, 2, v_acCache_1479_);
lean_ctor_set(v_reuseFailAlloc_1503_, 3, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1503_, 4, v_goal_1480_);
lean_ctor_set(v_reuseFailAlloc_1503_, 5, v_hypotheses_1481_);
lean_ctor_set_uint8(v_reuseFailAlloc_1503_, sizeof(void*)*6, v_didChange_1482_);
v___x_1500_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = lean_st_ref_set(v_a_1473_, v___x_1500_);
v___x_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1495_);
return v___x_1502_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg___boxed(lean_object* v_n_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(v_n_1507_, v_a_1508_);
lean_dec(v_a_1508_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(lean_object* v_n_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v___x_1521_; lean_object* v_typeAnalysis_1522_; lean_object* v_rewriteSimpCache_1523_; lean_object* v_rewriteDSimpCache_1524_; lean_object* v_acCache_1525_; lean_object* v_goal_1526_; lean_object* v_hypotheses_1527_; uint8_t v_didChange_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1552_; 
v___x_1521_ = lean_st_ref_take(v_a_1513_);
v_typeAnalysis_1522_ = lean_ctor_get(v___x_1521_, 3);
v_rewriteSimpCache_1523_ = lean_ctor_get(v___x_1521_, 0);
v_rewriteDSimpCache_1524_ = lean_ctor_get(v___x_1521_, 1);
v_acCache_1525_ = lean_ctor_get(v___x_1521_, 2);
v_goal_1526_ = lean_ctor_get(v___x_1521_, 4);
v_hypotheses_1527_ = lean_ctor_get(v___x_1521_, 5);
v_didChange_1528_ = lean_ctor_get_uint8(v___x_1521_, sizeof(void*)*6);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1530_ = v___x_1521_;
v_isShared_1531_ = v_isSharedCheck_1552_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_hypotheses_1527_);
lean_inc(v_goal_1526_);
lean_inc(v_typeAnalysis_1522_);
lean_inc(v_acCache_1525_);
lean_inc(v_rewriteDSimpCache_1524_);
lean_inc(v_rewriteSimpCache_1523_);
lean_dec(v___x_1521_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1552_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v_interestingStructures_1532_; lean_object* v_interestingEnums_1533_; lean_object* v_interestingMatchers_1534_; lean_object* v_uninteresting_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1551_; 
v_interestingStructures_1532_ = lean_ctor_get(v_typeAnalysis_1522_, 0);
v_interestingEnums_1533_ = lean_ctor_get(v_typeAnalysis_1522_, 1);
v_interestingMatchers_1534_ = lean_ctor_get(v_typeAnalysis_1522_, 2);
v_uninteresting_1535_ = lean_ctor_get(v_typeAnalysis_1522_, 3);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_typeAnalysis_1522_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1537_ = v_typeAnalysis_1522_;
v_isShared_1538_ = v_isSharedCheck_1551_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_uninteresting_1535_);
lean_inc(v_interestingMatchers_1534_);
lean_inc(v_interestingEnums_1533_);
lean_inc(v_interestingStructures_1532_);
lean_dec(v_typeAnalysis_1522_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1551_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1539_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1540_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1541_ = lean_box(0);
v___x_1542_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1539_, v___x_1540_, v_interestingStructures_1532_, v_n_1511_, v___x_1541_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1542_);
v___x_1544_ = v___x_1537_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_interestingEnums_1533_);
lean_ctor_set(v_reuseFailAlloc_1550_, 2, v_interestingMatchers_1534_);
lean_ctor_set(v_reuseFailAlloc_1550_, 3, v_uninteresting_1535_);
v___x_1544_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1546_; 
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 3, v___x_1544_);
v___x_1546_ = v___x_1530_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_rewriteSimpCache_1523_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_rewriteDSimpCache_1524_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_acCache_1525_);
lean_ctor_set(v_reuseFailAlloc_1549_, 3, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1549_, 4, v_goal_1526_);
lean_ctor_set(v_reuseFailAlloc_1549_, 5, v_hypotheses_1527_);
lean_ctor_set_uint8(v_reuseFailAlloc_1549_, sizeof(void*)*6, v_didChange_1528_);
v___x_1546_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = lean_st_ref_set(v_a_1513_, v___x_1546_);
v___x_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1541_);
return v___x_1548_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___boxed(lean_object* v_n_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(v_n_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(lean_object* v_n_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v___x_1567_; lean_object* v_typeAnalysis_1568_; lean_object* v_rewriteSimpCache_1569_; lean_object* v_rewriteDSimpCache_1570_; lean_object* v_acCache_1571_; lean_object* v_goal_1572_; lean_object* v_hypotheses_1573_; uint8_t v_didChange_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1598_; 
v___x_1567_ = lean_st_ref_take(v_a_1565_);
v_typeAnalysis_1568_ = lean_ctor_get(v___x_1567_, 3);
v_rewriteSimpCache_1569_ = lean_ctor_get(v___x_1567_, 0);
v_rewriteDSimpCache_1570_ = lean_ctor_get(v___x_1567_, 1);
v_acCache_1571_ = lean_ctor_get(v___x_1567_, 2);
v_goal_1572_ = lean_ctor_get(v___x_1567_, 4);
v_hypotheses_1573_ = lean_ctor_get(v___x_1567_, 5);
v_didChange_1574_ = lean_ctor_get_uint8(v___x_1567_, sizeof(void*)*6);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1576_ = v___x_1567_;
v_isShared_1577_ = v_isSharedCheck_1598_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_hypotheses_1573_);
lean_inc(v_goal_1572_);
lean_inc(v_typeAnalysis_1568_);
lean_inc(v_acCache_1571_);
lean_inc(v_rewriteDSimpCache_1570_);
lean_inc(v_rewriteSimpCache_1569_);
lean_dec(v___x_1567_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1598_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v_interestingStructures_1578_; lean_object* v_interestingEnums_1579_; lean_object* v_interestingMatchers_1580_; lean_object* v_uninteresting_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1597_; 
v_interestingStructures_1578_ = lean_ctor_get(v_typeAnalysis_1568_, 0);
v_interestingEnums_1579_ = lean_ctor_get(v_typeAnalysis_1568_, 1);
v_interestingMatchers_1580_ = lean_ctor_get(v_typeAnalysis_1568_, 2);
v_uninteresting_1581_ = lean_ctor_get(v_typeAnalysis_1568_, 3);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_typeAnalysis_1568_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1583_ = v_typeAnalysis_1568_;
v_isShared_1584_ = v_isSharedCheck_1597_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_uninteresting_1581_);
lean_inc(v_interestingMatchers_1580_);
lean_inc(v_interestingEnums_1579_);
lean_inc(v_interestingStructures_1578_);
lean_dec(v_typeAnalysis_1568_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1597_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1585_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1586_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1587_ = lean_box(0);
v___x_1588_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1585_, v___x_1586_, v_interestingEnums_1579_, v_n_1564_, v___x_1587_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 1, v___x_1588_);
v___x_1590_ = v___x_1583_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_interestingStructures_1578_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1596_, 2, v_interestingMatchers_1580_);
lean_ctor_set(v_reuseFailAlloc_1596_, 3, v_uninteresting_1581_);
v___x_1590_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v___x_1592_; 
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 3, v___x_1590_);
v___x_1592_ = v___x_1576_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_rewriteSimpCache_1569_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_rewriteDSimpCache_1570_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_acCache_1571_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1595_, 4, v_goal_1572_);
lean_ctor_set(v_reuseFailAlloc_1595_, 5, v_hypotheses_1573_);
lean_ctor_set_uint8(v_reuseFailAlloc_1595_, sizeof(void*)*6, v_didChange_1574_);
v___x_1592_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = lean_st_ref_set(v_a_1565_, v___x_1592_);
v___x_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1587_);
return v___x_1594_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg___boxed(lean_object* v_n_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(v_n_1599_, v_a_1600_);
lean_dec(v_a_1600_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(lean_object* v_n_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_){
_start:
{
lean_object* v___x_1613_; lean_object* v_typeAnalysis_1614_; lean_object* v_rewriteSimpCache_1615_; lean_object* v_rewriteDSimpCache_1616_; lean_object* v_acCache_1617_; lean_object* v_goal_1618_; lean_object* v_hypotheses_1619_; uint8_t v_didChange_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1644_; 
v___x_1613_ = lean_st_ref_take(v_a_1605_);
v_typeAnalysis_1614_ = lean_ctor_get(v___x_1613_, 3);
v_rewriteSimpCache_1615_ = lean_ctor_get(v___x_1613_, 0);
v_rewriteDSimpCache_1616_ = lean_ctor_get(v___x_1613_, 1);
v_acCache_1617_ = lean_ctor_get(v___x_1613_, 2);
v_goal_1618_ = lean_ctor_get(v___x_1613_, 4);
v_hypotheses_1619_ = lean_ctor_get(v___x_1613_, 5);
v_didChange_1620_ = lean_ctor_get_uint8(v___x_1613_, sizeof(void*)*6);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1622_ = v___x_1613_;
v_isShared_1623_ = v_isSharedCheck_1644_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_hypotheses_1619_);
lean_inc(v_goal_1618_);
lean_inc(v_typeAnalysis_1614_);
lean_inc(v_acCache_1617_);
lean_inc(v_rewriteDSimpCache_1616_);
lean_inc(v_rewriteSimpCache_1615_);
lean_dec(v___x_1613_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1644_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v_interestingStructures_1624_; lean_object* v_interestingEnums_1625_; lean_object* v_interestingMatchers_1626_; lean_object* v_uninteresting_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1643_; 
v_interestingStructures_1624_ = lean_ctor_get(v_typeAnalysis_1614_, 0);
v_interestingEnums_1625_ = lean_ctor_get(v_typeAnalysis_1614_, 1);
v_interestingMatchers_1626_ = lean_ctor_get(v_typeAnalysis_1614_, 2);
v_uninteresting_1627_ = lean_ctor_get(v_typeAnalysis_1614_, 3);
v_isSharedCheck_1643_ = !lean_is_exclusive(v_typeAnalysis_1614_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1629_ = v_typeAnalysis_1614_;
v_isShared_1630_ = v_isSharedCheck_1643_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_uninteresting_1627_);
lean_inc(v_interestingMatchers_1626_);
lean_inc(v_interestingEnums_1625_);
lean_inc(v_interestingStructures_1624_);
lean_dec(v_typeAnalysis_1614_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1643_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1631_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1632_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1633_ = lean_box(0);
v___x_1634_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1631_, v___x_1632_, v_interestingEnums_1625_, v_n_1603_, v___x_1633_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 1, v___x_1634_);
v___x_1636_ = v___x_1629_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_interestingStructures_1624_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1642_, 2, v_interestingMatchers_1626_);
lean_ctor_set(v_reuseFailAlloc_1642_, 3, v_uninteresting_1627_);
v___x_1636_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1638_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 3, v___x_1636_);
v___x_1638_ = v___x_1622_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_rewriteSimpCache_1615_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_rewriteDSimpCache_1616_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v_acCache_1617_);
lean_ctor_set(v_reuseFailAlloc_1641_, 3, v___x_1636_);
lean_ctor_set(v_reuseFailAlloc_1641_, 4, v_goal_1618_);
lean_ctor_set(v_reuseFailAlloc_1641_, 5, v_hypotheses_1619_);
lean_ctor_set_uint8(v_reuseFailAlloc_1641_, sizeof(void*)*6, v_didChange_1620_);
v___x_1638_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = lean_st_ref_set(v_a_1605_, v___x_1638_);
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1633_);
return v___x_1640_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___boxed(lean_object* v_n_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(v_n_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(lean_object* v_n_1656_, lean_object* v_k_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v___x_1660_; lean_object* v_typeAnalysis_1661_; lean_object* v_rewriteSimpCache_1662_; lean_object* v_rewriteDSimpCache_1663_; lean_object* v_acCache_1664_; lean_object* v_goal_1665_; lean_object* v_hypotheses_1666_; uint8_t v_didChange_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1691_; 
v___x_1660_ = lean_st_ref_take(v_a_1658_);
v_typeAnalysis_1661_ = lean_ctor_get(v___x_1660_, 3);
v_rewriteSimpCache_1662_ = lean_ctor_get(v___x_1660_, 0);
v_rewriteDSimpCache_1663_ = lean_ctor_get(v___x_1660_, 1);
v_acCache_1664_ = lean_ctor_get(v___x_1660_, 2);
v_goal_1665_ = lean_ctor_get(v___x_1660_, 4);
v_hypotheses_1666_ = lean_ctor_get(v___x_1660_, 5);
v_didChange_1667_ = lean_ctor_get_uint8(v___x_1660_, sizeof(void*)*6);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1669_ = v___x_1660_;
v_isShared_1670_ = v_isSharedCheck_1691_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_hypotheses_1666_);
lean_inc(v_goal_1665_);
lean_inc(v_typeAnalysis_1661_);
lean_inc(v_acCache_1664_);
lean_inc(v_rewriteDSimpCache_1663_);
lean_inc(v_rewriteSimpCache_1662_);
lean_dec(v___x_1660_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1691_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v_interestingStructures_1671_; lean_object* v_interestingEnums_1672_; lean_object* v_interestingMatchers_1673_; lean_object* v_uninteresting_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1690_; 
v_interestingStructures_1671_ = lean_ctor_get(v_typeAnalysis_1661_, 0);
v_interestingEnums_1672_ = lean_ctor_get(v_typeAnalysis_1661_, 1);
v_interestingMatchers_1673_ = lean_ctor_get(v_typeAnalysis_1661_, 2);
v_uninteresting_1674_ = lean_ctor_get(v_typeAnalysis_1661_, 3);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_typeAnalysis_1661_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1676_ = v_typeAnalysis_1661_;
v_isShared_1677_ = v_isSharedCheck_1690_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_uninteresting_1674_);
lean_inc(v_interestingMatchers_1673_);
lean_inc(v_interestingEnums_1672_);
lean_inc(v_interestingStructures_1671_);
lean_dec(v_typeAnalysis_1661_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1690_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1678_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1679_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1680_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1678_, v___x_1679_, v_interestingMatchers_1673_, v_n_1656_, v_k_1657_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 2, v___x_1680_);
v___x_1682_ = v___x_1676_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_interestingStructures_1671_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_interestingEnums_1672_);
lean_ctor_set(v_reuseFailAlloc_1689_, 2, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1689_, 3, v_uninteresting_1674_);
v___x_1682_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1684_; 
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 3, v___x_1682_);
v___x_1684_ = v___x_1669_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_rewriteSimpCache_1662_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_rewriteDSimpCache_1663_);
lean_ctor_set(v_reuseFailAlloc_1688_, 2, v_acCache_1664_);
lean_ctor_set(v_reuseFailAlloc_1688_, 3, v___x_1682_);
lean_ctor_set(v_reuseFailAlloc_1688_, 4, v_goal_1665_);
lean_ctor_set(v_reuseFailAlloc_1688_, 5, v_hypotheses_1666_);
lean_ctor_set_uint8(v_reuseFailAlloc_1688_, sizeof(void*)*6, v_didChange_1667_);
v___x_1684_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = lean_st_ref_set(v_a_1658_, v___x_1684_);
v___x_1686_ = lean_box(0);
v___x_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
return v___x_1687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg___boxed(lean_object* v_n_1692_, lean_object* v_k_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(v_n_1692_, v_k_1693_, v_a_1694_);
lean_dec(v_a_1694_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(lean_object* v_n_1697_, lean_object* v_k_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v___x_1708_; lean_object* v_typeAnalysis_1709_; lean_object* v_rewriteSimpCache_1710_; lean_object* v_rewriteDSimpCache_1711_; lean_object* v_acCache_1712_; lean_object* v_goal_1713_; lean_object* v_hypotheses_1714_; uint8_t v_didChange_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1739_; 
v___x_1708_ = lean_st_ref_take(v_a_1700_);
v_typeAnalysis_1709_ = lean_ctor_get(v___x_1708_, 3);
v_rewriteSimpCache_1710_ = lean_ctor_get(v___x_1708_, 0);
v_rewriteDSimpCache_1711_ = lean_ctor_get(v___x_1708_, 1);
v_acCache_1712_ = lean_ctor_get(v___x_1708_, 2);
v_goal_1713_ = lean_ctor_get(v___x_1708_, 4);
v_hypotheses_1714_ = lean_ctor_get(v___x_1708_, 5);
v_didChange_1715_ = lean_ctor_get_uint8(v___x_1708_, sizeof(void*)*6);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1717_ = v___x_1708_;
v_isShared_1718_ = v_isSharedCheck_1739_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_hypotheses_1714_);
lean_inc(v_goal_1713_);
lean_inc(v_typeAnalysis_1709_);
lean_inc(v_acCache_1712_);
lean_inc(v_rewriteDSimpCache_1711_);
lean_inc(v_rewriteSimpCache_1710_);
lean_dec(v___x_1708_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1739_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v_interestingStructures_1719_; lean_object* v_interestingEnums_1720_; lean_object* v_interestingMatchers_1721_; lean_object* v_uninteresting_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1738_; 
v_interestingStructures_1719_ = lean_ctor_get(v_typeAnalysis_1709_, 0);
v_interestingEnums_1720_ = lean_ctor_get(v_typeAnalysis_1709_, 1);
v_interestingMatchers_1721_ = lean_ctor_get(v_typeAnalysis_1709_, 2);
v_uninteresting_1722_ = lean_ctor_get(v_typeAnalysis_1709_, 3);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_typeAnalysis_1709_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1724_ = v_typeAnalysis_1709_;
v_isShared_1725_ = v_isSharedCheck_1738_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_uninteresting_1722_);
lean_inc(v_interestingMatchers_1721_);
lean_inc(v_interestingEnums_1720_);
lean_inc(v_interestingStructures_1719_);
lean_dec(v_typeAnalysis_1709_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1738_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1730_; 
v___x_1726_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1727_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1728_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1726_, v___x_1727_, v_interestingMatchers_1721_, v_n_1697_, v_k_1698_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 2, v___x_1728_);
v___x_1730_ = v___x_1724_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_interestingStructures_1719_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v_interestingEnums_1720_);
lean_ctor_set(v_reuseFailAlloc_1737_, 2, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1737_, 3, v_uninteresting_1722_);
v___x_1730_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1732_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 3, v___x_1730_);
v___x_1732_ = v___x_1717_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_rewriteSimpCache_1710_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_rewriteDSimpCache_1711_);
lean_ctor_set(v_reuseFailAlloc_1736_, 2, v_acCache_1712_);
lean_ctor_set(v_reuseFailAlloc_1736_, 3, v___x_1730_);
lean_ctor_set(v_reuseFailAlloc_1736_, 4, v_goal_1713_);
lean_ctor_set(v_reuseFailAlloc_1736_, 5, v_hypotheses_1714_);
lean_ctor_set_uint8(v_reuseFailAlloc_1736_, sizeof(void*)*6, v_didChange_1715_);
v___x_1732_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1733_ = lean_st_ref_set(v_a_1700_, v___x_1732_);
v___x_1734_ = lean_box(0);
v___x_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
return v___x_1735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___boxed(lean_object* v_n_1740_, lean_object* v_k_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(v_n_1740_, v_k_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
lean_dec(v_a_1749_);
lean_dec_ref(v_a_1748_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
lean_dec(v_a_1743_);
lean_dec_ref(v_a_1742_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(lean_object* v_n_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v___x_1755_; lean_object* v_typeAnalysis_1756_; lean_object* v_rewriteSimpCache_1757_; lean_object* v_rewriteDSimpCache_1758_; lean_object* v_acCache_1759_; lean_object* v_goal_1760_; lean_object* v_hypotheses_1761_; uint8_t v_didChange_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1786_; 
v___x_1755_ = lean_st_ref_take(v_a_1753_);
v_typeAnalysis_1756_ = lean_ctor_get(v___x_1755_, 3);
v_rewriteSimpCache_1757_ = lean_ctor_get(v___x_1755_, 0);
v_rewriteDSimpCache_1758_ = lean_ctor_get(v___x_1755_, 1);
v_acCache_1759_ = lean_ctor_get(v___x_1755_, 2);
v_goal_1760_ = lean_ctor_get(v___x_1755_, 4);
v_hypotheses_1761_ = lean_ctor_get(v___x_1755_, 5);
v_didChange_1762_ = lean_ctor_get_uint8(v___x_1755_, sizeof(void*)*6);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1764_ = v___x_1755_;
v_isShared_1765_ = v_isSharedCheck_1786_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_hypotheses_1761_);
lean_inc(v_goal_1760_);
lean_inc(v_typeAnalysis_1756_);
lean_inc(v_acCache_1759_);
lean_inc(v_rewriteDSimpCache_1758_);
lean_inc(v_rewriteSimpCache_1757_);
lean_dec(v___x_1755_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1786_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v_interestingStructures_1766_; lean_object* v_interestingEnums_1767_; lean_object* v_interestingMatchers_1768_; lean_object* v_uninteresting_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1785_; 
v_interestingStructures_1766_ = lean_ctor_get(v_typeAnalysis_1756_, 0);
v_interestingEnums_1767_ = lean_ctor_get(v_typeAnalysis_1756_, 1);
v_interestingMatchers_1768_ = lean_ctor_get(v_typeAnalysis_1756_, 2);
v_uninteresting_1769_ = lean_ctor_get(v_typeAnalysis_1756_, 3);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_typeAnalysis_1756_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1771_ = v_typeAnalysis_1756_;
v_isShared_1772_ = v_isSharedCheck_1785_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_uninteresting_1769_);
lean_inc(v_interestingMatchers_1768_);
lean_inc(v_interestingEnums_1767_);
lean_inc(v_interestingStructures_1766_);
lean_dec(v_typeAnalysis_1756_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1785_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1778_; 
v___x_1773_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1774_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1775_ = lean_box(0);
v___x_1776_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1773_, v___x_1774_, v_uninteresting_1769_, v_n_1752_, v___x_1775_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 3, v___x_1776_);
v___x_1778_ = v___x_1771_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_interestingStructures_1766_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_interestingEnums_1767_);
lean_ctor_set(v_reuseFailAlloc_1784_, 2, v_interestingMatchers_1768_);
lean_ctor_set(v_reuseFailAlloc_1784_, 3, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1780_; 
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 3, v___x_1778_);
v___x_1780_ = v___x_1764_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_rewriteSimpCache_1757_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_rewriteDSimpCache_1758_);
lean_ctor_set(v_reuseFailAlloc_1783_, 2, v_acCache_1759_);
lean_ctor_set(v_reuseFailAlloc_1783_, 3, v___x_1778_);
lean_ctor_set(v_reuseFailAlloc_1783_, 4, v_goal_1760_);
lean_ctor_set(v_reuseFailAlloc_1783_, 5, v_hypotheses_1761_);
lean_ctor_set_uint8(v_reuseFailAlloc_1783_, sizeof(void*)*6, v_didChange_1762_);
v___x_1780_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = lean_st_ref_set(v_a_1753_, v___x_1780_);
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1775_);
return v___x_1782_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg___boxed(lean_object* v_n_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(v_n_1787_, v_a_1788_);
lean_dec(v_a_1788_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(lean_object* v_n_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v___x_1801_; lean_object* v_typeAnalysis_1802_; lean_object* v_rewriteSimpCache_1803_; lean_object* v_rewriteDSimpCache_1804_; lean_object* v_acCache_1805_; lean_object* v_goal_1806_; lean_object* v_hypotheses_1807_; uint8_t v_didChange_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1832_; 
v___x_1801_ = lean_st_ref_take(v_a_1793_);
v_typeAnalysis_1802_ = lean_ctor_get(v___x_1801_, 3);
v_rewriteSimpCache_1803_ = lean_ctor_get(v___x_1801_, 0);
v_rewriteDSimpCache_1804_ = lean_ctor_get(v___x_1801_, 1);
v_acCache_1805_ = lean_ctor_get(v___x_1801_, 2);
v_goal_1806_ = lean_ctor_get(v___x_1801_, 4);
v_hypotheses_1807_ = lean_ctor_get(v___x_1801_, 5);
v_didChange_1808_ = lean_ctor_get_uint8(v___x_1801_, sizeof(void*)*6);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1810_ = v___x_1801_;
v_isShared_1811_ = v_isSharedCheck_1832_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_hypotheses_1807_);
lean_inc(v_goal_1806_);
lean_inc(v_typeAnalysis_1802_);
lean_inc(v_acCache_1805_);
lean_inc(v_rewriteDSimpCache_1804_);
lean_inc(v_rewriteSimpCache_1803_);
lean_dec(v___x_1801_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1832_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v_interestingStructures_1812_; lean_object* v_interestingEnums_1813_; lean_object* v_interestingMatchers_1814_; lean_object* v_uninteresting_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1831_; 
v_interestingStructures_1812_ = lean_ctor_get(v_typeAnalysis_1802_, 0);
v_interestingEnums_1813_ = lean_ctor_get(v_typeAnalysis_1802_, 1);
v_interestingMatchers_1814_ = lean_ctor_get(v_typeAnalysis_1802_, 2);
v_uninteresting_1815_ = lean_ctor_get(v_typeAnalysis_1802_, 3);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_typeAnalysis_1802_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1817_ = v_typeAnalysis_1802_;
v_isShared_1818_ = v_isSharedCheck_1831_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_uninteresting_1815_);
lean_inc(v_interestingMatchers_1814_);
lean_inc(v_interestingEnums_1813_);
lean_inc(v_interestingStructures_1812_);
lean_dec(v_typeAnalysis_1802_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1831_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1819_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1820_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1821_ = lean_box(0);
v___x_1822_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1819_, v___x_1820_, v_uninteresting_1815_, v_n_1791_, v___x_1821_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 3, v___x_1822_);
v___x_1824_ = v___x_1817_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_interestingStructures_1812_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_interestingEnums_1813_);
lean_ctor_set(v_reuseFailAlloc_1830_, 2, v_interestingMatchers_1814_);
lean_ctor_set(v_reuseFailAlloc_1830_, 3, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1826_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 3, v___x_1824_);
v___x_1826_ = v___x_1810_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_rewriteSimpCache_1803_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_rewriteDSimpCache_1804_);
lean_ctor_set(v_reuseFailAlloc_1829_, 2, v_acCache_1805_);
lean_ctor_set(v_reuseFailAlloc_1829_, 3, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1829_, 4, v_goal_1806_);
lean_ctor_set(v_reuseFailAlloc_1829_, 5, v_hypotheses_1807_);
lean_ctor_set_uint8(v_reuseFailAlloc_1829_, sizeof(void*)*6, v_didChange_1808_);
v___x_1826_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = lean_st_ref_set(v_a_1793_, v___x_1826_);
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1821_);
return v___x_1828_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___boxed(lean_object* v_n_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(v_n_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
return v_res_1843_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = lean_box(0);
v___x_1845_ = lean_unsigned_to_nat(16u);
v___x_1846_ = lean_mk_array(v___x_1845_, v___x_1844_);
return v___x_1846_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0);
v___x_1848_ = lean_unsigned_to_nat(0u);
v___x_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
lean_ctor_set(v___x_1849_, 1, v___x_1847_);
return v___x_1849_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1);
v___x_1851_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
lean_ctor_set(v___x_1851_, 2, v___x_1850_);
lean_ctor_set(v___x_1851_, 3, v___x_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(lean_object* v_cfg_1854_, lean_object* v_goal_1855_, lean_object* v_x_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1864_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
v___x_1865_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_1866_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_1867_ = 0;
v___x_1868_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1868_, 0, v___x_1864_);
lean_ctor_set(v___x_1868_, 1, v___x_1864_);
lean_ctor_set(v___x_1868_, 2, v___x_1864_);
lean_ctor_set(v___x_1868_, 3, v___x_1865_);
lean_ctor_set(v___x_1868_, 4, v_goal_1855_);
lean_ctor_set(v___x_1868_, 5, v___x_1866_);
lean_ctor_set_uint8(v___x_1868_, sizeof(void*)*6, v___x_1867_);
v___x_1869_ = lean_st_mk_ref(v___x_1868_);
lean_inc(v_a_1862_);
lean_inc_ref(v_a_1861_);
lean_inc(v_a_1860_);
lean_inc_ref(v_a_1859_);
lean_inc(v_a_1858_);
lean_inc_ref(v_a_1857_);
lean_inc(v___x_1869_);
v___x_1870_ = lean_apply_9(v_x_1856_, v_cfg_1854_, v___x_1869_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, lean_box(0));
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1880_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1880_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1880_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1875_ = lean_st_ref_get(v___x_1869_);
lean_dec(v___x_1869_);
v___x_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1876_, 0, v_a_1871_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1876_);
v___x_1878_ = v___x_1873_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec(v___x_1869_);
v_a_1881_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1870_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1870_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___boxed(lean_object* v_cfg_1889_, lean_object* v_goal_1890_, lean_object* v_x_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(v_cfg_1889_, v_goal_1890_, v_x_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(lean_object* v_00_u03b1_1900_, lean_object* v_cfg_1901_, lean_object* v_goal_1902_, lean_object* v_x_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1911_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
v___x_1912_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_1913_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_1914_ = 0;
v___x_1915_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1915_, 0, v___x_1911_);
lean_ctor_set(v___x_1915_, 1, v___x_1911_);
lean_ctor_set(v___x_1915_, 2, v___x_1911_);
lean_ctor_set(v___x_1915_, 3, v___x_1912_);
lean_ctor_set(v___x_1915_, 4, v_goal_1902_);
lean_ctor_set(v___x_1915_, 5, v___x_1913_);
lean_ctor_set_uint8(v___x_1915_, sizeof(void*)*6, v___x_1914_);
v___x_1916_ = lean_st_mk_ref(v___x_1915_);
lean_inc(v_a_1909_);
lean_inc_ref(v_a_1908_);
lean_inc(v_a_1907_);
lean_inc_ref(v_a_1906_);
lean_inc(v_a_1905_);
lean_inc_ref(v_a_1904_);
lean_inc(v___x_1916_);
v___x_1917_ = lean_apply_9(v_x_1903_, v_cfg_1901_, v___x_1916_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, lean_box(0));
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1927_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1920_ = v___x_1917_;
v_isShared_1921_ = v_isSharedCheck_1927_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1917_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1927_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1922_ = lean_st_ref_get(v___x_1916_);
lean_dec(v___x_1916_);
v___x_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1923_, 0, v_a_1918_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v___x_1923_);
v___x_1925_ = v___x_1920_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec(v___x_1916_);
v_a_1928_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1917_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1917_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___boxed(lean_object* v_00_u03b1_1936_, lean_object* v_cfg_1937_, lean_object* v_goal_1938_, lean_object* v_x_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(v_00_u03b1_1936_, v_cfg_1937_, v_goal_1938_, v_x_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(lean_object* v_cfg_1948_, lean_object* v_goal_1949_, lean_object* v_x_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1958_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
v___x_1959_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_1960_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_1961_ = 0;
v___x_1962_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1962_, 0, v___x_1958_);
lean_ctor_set(v___x_1962_, 1, v___x_1958_);
lean_ctor_set(v___x_1962_, 2, v___x_1958_);
lean_ctor_set(v___x_1962_, 3, v___x_1959_);
lean_ctor_set(v___x_1962_, 4, v_goal_1949_);
lean_ctor_set(v___x_1962_, 5, v___x_1960_);
lean_ctor_set_uint8(v___x_1962_, sizeof(void*)*6, v___x_1961_);
v___x_1963_ = lean_st_mk_ref(v___x_1962_);
lean_inc(v_a_1956_);
lean_inc_ref(v_a_1955_);
lean_inc(v_a_1954_);
lean_inc_ref(v_a_1953_);
lean_inc(v_a_1952_);
lean_inc_ref(v_a_1951_);
lean_inc(v___x_1963_);
v___x_1964_ = lean_apply_9(v_x_1950_, v_cfg_1948_, v___x_1963_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, lean_box(0));
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1973_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1967_ = v___x_1964_;
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1969_ = lean_st_ref_get(v___x_1963_);
lean_dec(v___x_1963_);
lean_dec(v___x_1969_);
if (v_isShared_1968_ == 0)
{
v___x_1971_ = v___x_1967_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1965_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
else
{
lean_dec(v___x_1963_);
return v___x_1964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg___boxed(lean_object* v_cfg_1974_, lean_object* v_goal_1975_, lean_object* v_x_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(v_cfg_1974_, v_goal_1975_, v_x_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
lean_dec(v_a_1982_);
lean_dec_ref(v_a_1981_);
lean_dec(v_a_1980_);
lean_dec_ref(v_a_1979_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(lean_object* v_00_u03b1_1985_, lean_object* v_cfg_1986_, lean_object* v_goal_1987_, lean_object* v_x_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_1996_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
v___x_1997_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_1998_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_1999_ = 0;
v___x_2000_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2000_, 0, v___x_1996_);
lean_ctor_set(v___x_2000_, 1, v___x_1996_);
lean_ctor_set(v___x_2000_, 2, v___x_1996_);
lean_ctor_set(v___x_2000_, 3, v___x_1997_);
lean_ctor_set(v___x_2000_, 4, v_goal_1987_);
lean_ctor_set(v___x_2000_, 5, v___x_1998_);
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*6, v___x_1999_);
v___x_2001_ = lean_st_mk_ref(v___x_2000_);
lean_inc(v_a_1994_);
lean_inc_ref(v_a_1993_);
lean_inc(v_a_1992_);
lean_inc_ref(v_a_1991_);
lean_inc(v_a_1990_);
lean_inc_ref(v_a_1989_);
lean_inc(v___x_2001_);
v___x_2002_ = lean_apply_9(v_x_1988_, v_cfg_1986_, v___x_2001_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, lean_box(0));
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2011_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2005_ = v___x_2002_;
v_isShared_2006_ = v_isSharedCheck_2011_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_2002_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2011_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2007_ = lean_st_ref_get(v___x_2001_);
lean_dec(v___x_2001_);
lean_dec(v___x_2007_);
if (v_isShared_2006_ == 0)
{
v___x_2009_ = v___x_2005_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2003_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
else
{
lean_dec(v___x_2001_);
return v___x_2002_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___boxed(lean_object* v_00_u03b1_2012_, lean_object* v_cfg_2013_, lean_object* v_goal_2014_, lean_object* v_x_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(v_00_u03b1_2012_, v_cfg_2013_, v_goal_2014_, v_x_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_);
lean_dec(v_a_2021_);
lean_dec_ref(v_a_2020_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg___lam__0(lean_object* v_x_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v___x_2034_; 
lean_inc(v___y_2028_);
lean_inc_ref(v___y_2027_);
lean_inc(v___y_2026_);
lean_inc_ref(v___y_2025_);
v___x_2034_ = lean_apply_9(v_x_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, lean_box(0));
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg___lam__0___boxed(lean_object* v_x_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg___lam__0(v_x_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg(lean_object* v_mvarId_2046_, lean_object* v_x_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v___f_2057_; lean_object* v___x_2058_; 
lean_inc(v___y_2051_);
lean_inc_ref(v___y_2050_);
lean_inc(v___y_2049_);
lean_inc_ref(v___y_2048_);
v___f_2057_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2057_, 0, v_x_2047_);
lean_closure_set(v___f_2057_, 1, v___y_2048_);
lean_closure_set(v___f_2057_, 2, v___y_2049_);
lean_closure_set(v___f_2057_, 3, v___y_2050_);
lean_closure_set(v___f_2057_, 4, v___y_2051_);
v___x_2058_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2046_, v___f_2057_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
if (lean_obj_tag(v___x_2058_) == 0)
{
return v___x_2058_;
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg___boxed(lean_object* v_mvarId_2067_, lean_object* v_x_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg(v_mvarId_2067_, v_x_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1(lean_object* v_00_u03b1_2079_, lean_object* v_mvarId_2080_, lean_object* v_x_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg(v_mvarId_2080_, v_x_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___boxed(lean_object* v_00_u03b1_2092_, lean_object* v_mvarId_2093_, lean_object* v_x_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1(v_00_u03b1_2092_, v_mvarId_2093_, v_x_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0___redArg(size_t v_sz_2105_, size_t v_i_2106_, lean_object* v_bs_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
uint8_t v___x_2115_; 
v___x_2115_ = lean_usize_dec_lt(v_i_2106_, v_sz_2105_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; 
v___x_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2116_, 0, v_bs_2107_);
return v___x_2116_;
}
else
{
lean_object* v_v_2117_; lean_object* v___x_2118_; 
v_v_2117_ = lean_array_uget(v_bs_2107_, v_i_2106_);
lean_inc(v_v_2117_);
v___x_2118_ = l_Lean_FVarId_getUserName___redArg(v_v_2117_, v___y_2110_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2120_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2118_, 1);
lean_inc(v_v_2117_);
v___x_2120_ = l_Lean_FVarId_getType___redArg(v_v_2117_, v___y_2110_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2122_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2120_, 1);
v___x_2122_ = l_Lean_Meta_Sym_instantiateMVarsS(v_a_2121_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2124_; lean_object* v_bs_x27_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; size_t v___x_2129_; size_t v___x_2130_; lean_object* v___x_2131_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v___x_2124_ = lean_unsigned_to_nat(0u);
v_bs_x27_2125_ = lean_array_uset(v_bs_2107_, v_i_2106_, v___x_2124_);
lean_inc(v_v_2117_);
v___x_2126_ = l_Lean_mkFVar(v_v_2117_);
v___x_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2127_, 0, v_v_2117_);
v___x_2128_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2128_, 0, v_a_2119_);
lean_ctor_set(v___x_2128_, 1, v_a_2123_);
lean_ctor_set(v___x_2128_, 2, v___x_2126_);
lean_ctor_set(v___x_2128_, 3, v___x_2127_);
v___x_2129_ = ((size_t)1ULL);
v___x_2130_ = lean_usize_add(v_i_2106_, v___x_2129_);
v___x_2131_ = lean_array_uset(v_bs_x27_2125_, v_i_2106_, v___x_2128_);
v_i_2106_ = v___x_2130_;
v_bs_2107_ = v___x_2131_;
goto _start;
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v_a_2119_);
lean_dec(v_v_2117_);
lean_dec_ref(v_bs_2107_);
v_a_2133_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2122_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2122_);
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
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec(v_a_2119_);
lean_dec(v_v_2117_);
lean_dec_ref(v_bs_2107_);
v_a_2141_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2120_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2120_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec(v_v_2117_);
lean_dec_ref(v_bs_2107_);
v_a_2149_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2118_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2118_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0___redArg___boxed(lean_object* v_sz_2157_, lean_object* v_i_2158_, lean_object* v_bs_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
size_t v_sz_boxed_2167_; size_t v_i_boxed_2168_; lean_object* v_res_2169_; 
v_sz_boxed_2167_ = lean_unbox_usize(v_sz_2157_);
lean_dec(v_sz_2157_);
v_i_boxed_2168_ = lean_unbox_usize(v_i_2158_);
lean_dec(v_i_2158_);
v_res_2169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0___redArg(v_sz_boxed_2167_, v_i_boxed_2168_, v_bs_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___lam__0(lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_Meta_getPropHyps(v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; size_t v_sz_2181_; size_t v___x_2182_; lean_object* v___x_2183_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref_known(v___x_2179_, 1);
v_sz_2181_ = lean_array_size(v_a_2180_);
v___x_2182_ = ((size_t)0ULL);
v___x_2183_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0___redArg(v_sz_2181_, v___x_2182_, v_a_2180_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2208_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2186_ = v___x_2183_;
v_isShared_2187_ = v_isSharedCheck_2208_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2183_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2208_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; lean_object* v_rewriteSimpCache_2189_; lean_object* v_rewriteDSimpCache_2190_; lean_object* v_acCache_2191_; lean_object* v_typeAnalysis_2192_; lean_object* v_goal_2193_; uint8_t v_didChange_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2206_; 
v___x_2188_ = lean_st_ref_take(v___y_2171_);
v_rewriteSimpCache_2189_ = lean_ctor_get(v___x_2188_, 0);
v_rewriteDSimpCache_2190_ = lean_ctor_get(v___x_2188_, 1);
v_acCache_2191_ = lean_ctor_get(v___x_2188_, 2);
v_typeAnalysis_2192_ = lean_ctor_get(v___x_2188_, 3);
v_goal_2193_ = lean_ctor_get(v___x_2188_, 4);
v_didChange_2194_ = lean_ctor_get_uint8(v___x_2188_, sizeof(void*)*6);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2206_ == 0)
{
lean_object* v_unused_2207_; 
v_unused_2207_ = lean_ctor_get(v___x_2188_, 5);
lean_dec(v_unused_2207_);
v___x_2196_ = v___x_2188_;
v_isShared_2197_ = v_isSharedCheck_2206_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_goal_2193_);
lean_inc(v_typeAnalysis_2192_);
lean_inc(v_acCache_2191_);
lean_inc(v_rewriteDSimpCache_2190_);
lean_inc(v_rewriteSimpCache_2189_);
lean_dec(v___x_2188_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2206_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 5, v_a_2184_);
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_rewriteSimpCache_2189_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_rewriteDSimpCache_2190_);
lean_ctor_set(v_reuseFailAlloc_2205_, 2, v_acCache_2191_);
lean_ctor_set(v_reuseFailAlloc_2205_, 3, v_typeAnalysis_2192_);
lean_ctor_set(v_reuseFailAlloc_2205_, 4, v_goal_2193_);
lean_ctor_set(v_reuseFailAlloc_2205_, 5, v_a_2184_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, sizeof(void*)*6, v_didChange_2194_);
v___x_2199_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2200_ = lean_st_ref_set(v___y_2171_, v___x_2199_);
v___x_2201_ = lean_box(0);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v___x_2201_);
v___x_2203_ = v___x_2186_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
v_a_2209_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2183_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2183_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
v_a_2217_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2179_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2179_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___lam__0___boxed(lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___lam__0(v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal(lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_){
_start:
{
lean_object* v___x_2245_; lean_object* v_rewriteSimpCache_2246_; lean_object* v_rewriteDSimpCache_2247_; lean_object* v_acCache_2248_; lean_object* v_typeAnalysis_2249_; lean_object* v_goal_2250_; lean_object* v_hypotheses_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2264_; 
v___x_2245_ = lean_st_ref_take(v_a_2237_);
v_rewriteSimpCache_2246_ = lean_ctor_get(v___x_2245_, 0);
v_rewriteDSimpCache_2247_ = lean_ctor_get(v___x_2245_, 1);
v_acCache_2248_ = lean_ctor_get(v___x_2245_, 2);
v_typeAnalysis_2249_ = lean_ctor_get(v___x_2245_, 3);
v_goal_2250_ = lean_ctor_get(v___x_2245_, 4);
v_hypotheses_2251_ = lean_ctor_get(v___x_2245_, 5);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2253_ = v___x_2245_;
v_isShared_2254_ = v_isSharedCheck_2264_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_hypotheses_2251_);
lean_inc(v_goal_2250_);
lean_inc(v_typeAnalysis_2249_);
lean_inc(v_acCache_2248_);
lean_inc(v_rewriteDSimpCache_2247_);
lean_inc(v_rewriteSimpCache_2246_);
lean_dec(v___x_2245_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2264_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
uint8_t v___x_2255_; lean_object* v___x_2257_; 
v___x_2255_ = 1;
if (v_isShared_2254_ == 0)
{
v___x_2257_ = v___x_2253_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_rewriteSimpCache_2246_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v_rewriteDSimpCache_2247_);
lean_ctor_set(v_reuseFailAlloc_2263_, 2, v_acCache_2248_);
lean_ctor_set(v_reuseFailAlloc_2263_, 3, v_typeAnalysis_2249_);
lean_ctor_set(v_reuseFailAlloc_2263_, 4, v_goal_2250_);
lean_ctor_set(v_reuseFailAlloc_2263_, 5, v_hypotheses_2251_);
v___x_2257_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v_goal_2260_; lean_object* v___f_2261_; lean_object* v___x_2262_; 
lean_ctor_set_uint8(v___x_2257_, sizeof(void*)*6, v___x_2255_);
v___x_2258_ = lean_st_ref_set(v_a_2237_, v___x_2257_);
v___x_2259_ = lean_st_ref_get(v_a_2237_);
v_goal_2260_ = lean_ctor_get(v___x_2259_, 4);
lean_inc(v_goal_2260_);
lean_dec(v___x_2259_);
v___f_2261_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___closed__0));
v___x_2262_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg(v_goal_2260_, v___f_2261_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_);
return v___x_2262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___boxed(lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal(v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
lean_dec(v_a_2272_);
lean_dec_ref(v_a_2271_);
lean_dec(v_a_2270_);
lean_dec_ref(v_a_2269_);
lean_dec(v_a_2268_);
lean_dec_ref(v_a_2267_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0(size_t v_sz_2275_, size_t v_i_2276_, lean_object* v_bs_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v___x_2287_; 
v___x_2287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0___redArg(v_sz_2275_, v_i_2276_, v_bs_2277_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0___boxed(lean_object* v_sz_2288_, lean_object* v_i_2289_, lean_object* v_bs_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
size_t v_sz_boxed_2300_; size_t v_i_boxed_2301_; lean_object* v_res_2302_; 
v_sz_boxed_2300_ = lean_unbox_usize(v_sz_2288_);
lean_dec(v_sz_2288_);
v_i_boxed_2301_ = lean_unbox_usize(v_i_2289_);
lean_dec(v_i_2289_);
v_res_2302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0(v_sz_boxed_2300_, v_i_boxed_2301_, v_bs_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
return v_res_2302_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0(void){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_instMonadEIO(lean_box(0));
return v___x_2303_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1(void){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0);
v___x_2305_ = l_StateRefT_x27_instMonad___redArg(v___x_2304_);
return v___x_2305_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8(void){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2312_ = l_Lean_Core_instMonadTraceCoreM;
v___x_2313_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2314_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2313_, v___x_2312_);
return v___x_2314_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___f_2316_; lean_object* v___x_2317_; 
v___x_2315_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8);
v___f_2316_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___x_2317_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2316_, v___x_2315_);
return v___x_2317_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10(void){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2318_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9);
v___x_2319_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2320_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2319_, v___x_2318_);
return v___x_2320_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___f_2322_; lean_object* v___x_2323_; 
v___x_2321_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___f_2322_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___x_2323_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2322_, v___x_2321_);
return v___x_2323_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2324_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11);
v___x_2325_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2326_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2325_, v___x_2324_);
return v___x_2326_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13(void){
_start:
{
lean_object* v___x_2327_; lean_object* v___f_2328_; lean_object* v___x_2329_; 
v___x_2327_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12);
v___f_2328_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___x_2329_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2328_, v___x_2327_);
return v___x_2329_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20(void){
_start:
{
lean_object* v_cls_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v_cls_2340_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___x_2341_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19));
v___x_2342_ = l_Lean_Name_append(v___x_2341_, v_cls_2340_);
return v___x_2342_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23(void){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2345_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2346_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2347_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22));
v___x_2348_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2347_, v___x_2346_, v___x_2345_);
return v___x_2348_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24(void){
_start:
{
lean_object* v___x_2349_; lean_object* v___f_2350_; lean_object* v___f_2351_; lean_object* v___x_2352_; 
v___x_2349_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23);
v___f_2350_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___f_2351_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21));
v___x_2352_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2351_, v___f_2350_, v___x_2349_);
return v___x_2352_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25(void){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2353_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24);
v___x_2354_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2355_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22));
v___x_2356_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2355_, v___x_2354_, v___x_2353_);
return v___x_2356_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26(void){
_start:
{
lean_object* v___x_2357_; lean_object* v___f_2358_; lean_object* v___f_2359_; lean_object* v___x_2360_; 
v___x_2357_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25);
v___f_2358_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___f_2359_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21));
v___x_2360_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2359_, v___f_2358_, v___x_2357_);
return v___x_2360_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27(void){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2361_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26);
v___x_2362_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2363_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22));
v___x_2364_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2363_, v___x_2362_, v___x_2361_);
return v___x_2364_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___f_2366_; lean_object* v___f_2367_; lean_object* v___x_2368_; 
v___x_2365_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27);
v___f_2366_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___f_2367_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21));
v___x_2368_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2367_, v___f_2366_, v___x_2365_);
return v___x_2368_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___f_2371_; 
v___x_2369_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2370_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2371_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2371_, 0, v___x_2370_);
lean_closure_set(v___f_2371_, 1, v___x_2369_);
return v___f_2371_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30(void){
_start:
{
lean_object* v___f_2372_; lean_object* v___f_2373_; lean_object* v___f_2374_; 
v___f_2372_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___f_2373_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29);
v___f_2374_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2374_, 0, v___f_2373_);
lean_closure_set(v___f_2374_, 1, v___f_2372_);
return v___f_2374_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31(void){
_start:
{
lean_object* v___x_2375_; lean_object* v___f_2376_; lean_object* v___f_2377_; 
v___x_2375_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___f_2376_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30);
v___f_2377_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2377_, 0, v___f_2376_);
lean_closure_set(v___f_2377_, 1, v___x_2375_);
return v___f_2377_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32(void){
_start:
{
lean_object* v___f_2378_; lean_object* v___f_2379_; lean_object* v___f_2380_; 
v___f_2378_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___f_2379_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31);
v___f_2380_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2380_, 0, v___f_2379_);
lean_closure_set(v___f_2380_, 1, v___f_2378_);
return v___f_2380_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33));
v___x_2383_ = l_Lean_stringToMessageData(v___x_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(lean_object* v_hyp_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v___y_2395_; lean_object* v___x_2415_; lean_object* v_toApplicative_2416_; lean_object* v_toFunctor_2417_; lean_object* v_toSeq_2418_; lean_object* v_toSeqLeft_2419_; lean_object* v_toSeqRight_2420_; lean_object* v___f_2421_; lean_object* v___f_2422_; lean_object* v___f_2423_; lean_object* v___f_2424_; lean_object* v___x_2425_; lean_object* v___f_2426_; lean_object* v___f_2427_; lean_object* v___f_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v_toApplicative_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2479_; 
v___x_2415_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1);
v_toApplicative_2416_ = lean_ctor_get(v___x_2415_, 0);
v_toFunctor_2417_ = lean_ctor_get(v_toApplicative_2416_, 0);
v_toSeq_2418_ = lean_ctor_get(v_toApplicative_2416_, 2);
v_toSeqLeft_2419_ = lean_ctor_get(v_toApplicative_2416_, 3);
v_toSeqRight_2420_ = lean_ctor_get(v_toApplicative_2416_, 4);
v___f_2421_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2));
v___f_2422_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3));
lean_inc_ref_n(v_toFunctor_2417_, 2);
v___f_2423_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2423_, 0, v_toFunctor_2417_);
v___f_2424_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2424_, 0, v_toFunctor_2417_);
v___x_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___f_2423_);
lean_ctor_set(v___x_2425_, 1, v___f_2424_);
lean_inc(v_toSeqRight_2420_);
v___f_2426_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2426_, 0, v_toSeqRight_2420_);
lean_inc(v_toSeqLeft_2419_);
v___f_2427_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2427_, 0, v_toSeqLeft_2419_);
lean_inc(v_toSeq_2418_);
v___f_2428_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2428_, 0, v_toSeq_2418_);
v___x_2429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2425_);
lean_ctor_set(v___x_2429_, 1, v___f_2421_);
lean_ctor_set(v___x_2429_, 2, v___f_2428_);
lean_ctor_set(v___x_2429_, 3, v___f_2427_);
lean_ctor_set(v___x_2429_, 4, v___f_2426_);
v___x_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2429_);
lean_ctor_set(v___x_2430_, 1, v___f_2422_);
v___x_2431_ = l_StateRefT_x27_instMonad___redArg(v___x_2430_);
v_toApplicative_2432_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2479_ == 0)
{
lean_object* v_unused_2480_; 
v_unused_2480_ = lean_ctor_get(v___x_2431_, 1);
lean_dec(v_unused_2480_);
v___x_2434_ = v___x_2431_;
v_isShared_2435_ = v_isSharedCheck_2479_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_toApplicative_2432_);
lean_dec(v___x_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2479_;
goto v_resetjp_2433_;
}
v___jp_2394_:
{
lean_object* v___x_2396_; lean_object* v_rewriteSimpCache_2397_; lean_object* v_rewriteDSimpCache_2398_; lean_object* v_acCache_2399_; lean_object* v_typeAnalysis_2400_; lean_object* v_goal_2401_; lean_object* v_hypotheses_2402_; uint8_t v_didChange_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2414_; 
v___x_2396_ = lean_st_ref_take(v___y_2395_);
v_rewriteSimpCache_2397_ = lean_ctor_get(v___x_2396_, 0);
v_rewriteDSimpCache_2398_ = lean_ctor_get(v___x_2396_, 1);
v_acCache_2399_ = lean_ctor_get(v___x_2396_, 2);
v_typeAnalysis_2400_ = lean_ctor_get(v___x_2396_, 3);
v_goal_2401_ = lean_ctor_get(v___x_2396_, 4);
v_hypotheses_2402_ = lean_ctor_get(v___x_2396_, 5);
v_didChange_2403_ = lean_ctor_get_uint8(v___x_2396_, sizeof(void*)*6);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2405_ = v___x_2396_;
v_isShared_2406_ = v_isSharedCheck_2414_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_hypotheses_2402_);
lean_inc(v_goal_2401_);
lean_inc(v_typeAnalysis_2400_);
lean_inc(v_acCache_2399_);
lean_inc(v_rewriteDSimpCache_2398_);
lean_inc(v_rewriteSimpCache_2397_);
lean_dec(v___x_2396_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2414_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2407_ = lean_array_push(v_hypotheses_2402_, v_hyp_2384_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 5, v___x_2407_);
v___x_2409_ = v___x_2405_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_rewriteSimpCache_2397_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v_rewriteDSimpCache_2398_);
lean_ctor_set(v_reuseFailAlloc_2413_, 2, v_acCache_2399_);
lean_ctor_set(v_reuseFailAlloc_2413_, 3, v_typeAnalysis_2400_);
lean_ctor_set(v_reuseFailAlloc_2413_, 4, v_goal_2401_);
lean_ctor_set(v_reuseFailAlloc_2413_, 5, v___x_2407_);
lean_ctor_set_uint8(v_reuseFailAlloc_2413_, sizeof(void*)*6, v_didChange_2403_);
v___x_2409_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2410_ = lean_st_ref_set(v___y_2395_, v___x_2409_);
v___x_2411_ = lean_box(0);
v___x_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
return v___x_2412_;
}
}
}
v_resetjp_2433_:
{
lean_object* v_toFunctor_2436_; lean_object* v_toSeq_2437_; lean_object* v_toSeqLeft_2438_; lean_object* v_toSeqRight_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2477_; 
v_toFunctor_2436_ = lean_ctor_get(v_toApplicative_2432_, 0);
v_toSeq_2437_ = lean_ctor_get(v_toApplicative_2432_, 2);
v_toSeqLeft_2438_ = lean_ctor_get(v_toApplicative_2432_, 3);
v_toSeqRight_2439_ = lean_ctor_get(v_toApplicative_2432_, 4);
v_isSharedCheck_2477_ = !lean_is_exclusive(v_toApplicative_2432_);
if (v_isSharedCheck_2477_ == 0)
{
lean_object* v_unused_2478_; 
v_unused_2478_ = lean_ctor_get(v_toApplicative_2432_, 1);
lean_dec(v_unused_2478_);
v___x_2441_ = v_toApplicative_2432_;
v_isShared_2442_ = v_isSharedCheck_2477_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_toSeqRight_2439_);
lean_inc(v_toSeqLeft_2438_);
lean_inc(v_toSeq_2437_);
lean_inc(v_toFunctor_2436_);
lean_dec(v_toApplicative_2432_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2477_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___f_2443_; lean_object* v___f_2444_; lean_object* v___f_2445_; lean_object* v___f_2446_; lean_object* v___x_2447_; lean_object* v___f_2448_; lean_object* v___f_2449_; lean_object* v___f_2450_; lean_object* v___x_2452_; 
v___f_2443_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4));
v___f_2444_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5));
lean_inc_ref(v_toFunctor_2436_);
v___f_2445_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2445_, 0, v_toFunctor_2436_);
v___f_2446_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2446_, 0, v_toFunctor_2436_);
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___f_2445_);
lean_ctor_set(v___x_2447_, 1, v___f_2446_);
v___f_2448_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2448_, 0, v_toSeqRight_2439_);
v___f_2449_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2449_, 0, v_toSeqLeft_2438_);
v___f_2450_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2450_, 0, v_toSeq_2437_);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 4, v___f_2448_);
lean_ctor_set(v___x_2441_, 3, v___f_2449_);
lean_ctor_set(v___x_2441_, 2, v___f_2450_);
lean_ctor_set(v___x_2441_, 1, v___f_2443_);
lean_ctor_set(v___x_2441_, 0, v___x_2447_);
v___x_2452_ = v___x_2441_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2447_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v___f_2443_);
lean_ctor_set(v_reuseFailAlloc_2476_, 2, v___f_2450_);
lean_ctor_set(v_reuseFailAlloc_2476_, 3, v___f_2449_);
lean_ctor_set(v_reuseFailAlloc_2476_, 4, v___f_2448_);
v___x_2452_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2454_; 
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 1, v___f_2444_);
lean_ctor_set(v___x_2434_, 0, v___x_2452_);
v___x_2454_ = v___x_2434_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2452_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v___f_2444_);
v___x_2454_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v_options_2460_; uint8_t v_hasTrace_2461_; 
v___x_2455_ = l_StateRefT_x27_instMonad___redArg(v___x_2454_);
v___x_2456_ = l_ReaderT_instMonad___redArg(v___x_2455_);
v___x_2457_ = l_StateRefT_x27_instMonad___redArg(v___x_2456_);
v___x_2458_ = l_ReaderT_instMonad___redArg(v___x_2457_);
v___x_2459_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13);
v_options_2460_ = lean_ctor_get(v_a_2391_, 2);
v_hasTrace_2461_ = lean_ctor_get_uint8(v_options_2460_, sizeof(void*)*1);
if (v_hasTrace_2461_ == 0)
{
lean_dec_ref(v___x_2458_);
v___y_2395_ = v_a_2386_;
goto v___jp_2394_;
}
else
{
lean_object* v_inheritedTraceOptions_2462_; lean_object* v_cls_2463_; lean_object* v___x_2464_; uint8_t v___x_2465_; 
v_inheritedTraceOptions_2462_ = lean_ctor_get(v_a_2391_, 13);
v_cls_2463_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___x_2464_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___x_2465_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2462_, v_options_2460_, v___x_2464_);
if (v___x_2465_ == 0)
{
lean_dec_ref(v___x_2458_);
v___y_2395_ = v_a_2386_;
goto v___jp_2394_;
}
else
{
lean_object* v___x_2466_; lean_object* v_toMonadRef_2467_; lean_object* v_type_2468_; lean_object* v___f_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_3853__overap_2473_; lean_object* v___x_2474_; 
v___x_2466_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v_toMonadRef_2467_ = lean_ctor_get(v___x_2466_, 0);
v_type_2468_ = lean_ctor_get(v_hyp_2384_, 1);
v___f_2469_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32);
v___x_2470_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34);
lean_inc_ref(v_type_2468_);
v___x_2471_ = l_Lean_MessageData_ofExpr(v_type_2468_);
v___x_2472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2470_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
lean_inc_ref(v_toMonadRef_2467_);
v___x_3853__overap_2473_ = l_Lean_addTrace___redArg(v___x_2458_, v___x_2459_, v_toMonadRef_2467_, v___f_2469_, v_cls_2463_, v___x_2472_);
lean_inc(v_a_2392_);
lean_inc_ref(v_a_2391_);
lean_inc(v_a_2390_);
lean_inc_ref(v_a_2389_);
lean_inc(v_a_2388_);
lean_inc_ref(v_a_2387_);
lean_inc(v_a_2386_);
lean_inc_ref(v_a_2385_);
v___x_2474_ = lean_apply_9(v___x_3853__overap_2473_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, lean_box(0));
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_dec_ref_known(v___x_2474_, 1);
v___y_2395_ = v_a_2386_;
goto v___jp_2394_;
}
else
{
lean_dec_ref(v_hyp_2384_);
return v___x_2474_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___boxed(lean_object* v_hyp_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(v_hyp_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(lean_object* v___x_2492_, lean_object* v___f_2493_, lean_object* v___x_2494_, lean_object* v___f_2495_, lean_object* v___x_2496_, lean_object* v___f_2497_, lean_object* v___x_2498_, lean_object* v___x_2499_, lean_object* v_x_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v_options_2514_; uint8_t v_hasTrace_2515_; 
v_options_2514_ = lean_ctor_get(v___y_2508_, 2);
v_hasTrace_2515_ = lean_ctor_get_uint8(v_options_2514_, sizeof(void*)*1);
if (v_hasTrace_2515_ == 0)
{
lean_dec_ref(v___y_2501_);
lean_dec_ref(v___x_2499_);
lean_dec_ref(v___x_2498_);
lean_dec(v___f_2497_);
lean_dec(v___x_2496_);
lean_dec(v___f_2495_);
lean_dec(v___x_2494_);
lean_dec(v___f_2493_);
lean_dec(v___x_2492_);
goto v___jp_2511_;
}
else
{
lean_object* v_inheritedTraceOptions_2516_; lean_object* v_cls_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
v_inheritedTraceOptions_2516_ = lean_ctor_get(v___y_2508_, 13);
v_cls_2517_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___x_2518_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___x_2519_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2516_, v_options_2514_, v___x_2518_);
if (v___x_2519_ == 0)
{
lean_dec_ref(v___y_2501_);
lean_dec_ref(v___x_2499_);
lean_dec_ref(v___x_2498_);
lean_dec(v___f_2497_);
lean_dec(v___x_2496_);
lean_dec(v___f_2495_);
lean_dec(v___x_2494_);
lean_dec(v___f_2493_);
lean_dec(v___x_2492_);
goto v___jp_2511_;
}
else
{
lean_object* v___f_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v_toMonadRef_2529_; lean_object* v_type_2530_; lean_object* v___x_2531_; lean_object* v___f_2532_; lean_object* v___f_2533_; lean_object* v___f_2534_; lean_object* v___f_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_4622__overap_2539_; lean_object* v___x_2540_; 
v___f_2520_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21));
v___x_2521_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22));
v___x_2522_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2523_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2521_, v___x_2492_, v___x_2522_);
v___x_2524_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2520_, v___f_2493_, v___x_2523_);
lean_inc(v___x_2494_);
v___x_2525_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2521_, v___x_2494_, v___x_2524_);
lean_inc(v___f_2495_);
v___x_2526_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2520_, v___f_2495_, v___x_2525_);
lean_inc(v___x_2496_);
v___x_2527_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2521_, v___x_2496_, v___x_2526_);
lean_inc(v___f_2497_);
v___x_2528_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2520_, v___f_2497_, v___x_2527_);
v_toMonadRef_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc_ref(v_toMonadRef_2529_);
lean_dec_ref(v___x_2528_);
v_type_2530_ = lean_ctor_get(v___y_2501_, 1);
lean_inc_ref(v_type_2530_);
lean_dec_ref(v___y_2501_);
v___x_2531_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2532_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2532_, 0, v___x_2531_);
lean_closure_set(v___f_2532_, 1, v___x_2494_);
v___f_2533_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2533_, 0, v___f_2532_);
lean_closure_set(v___f_2533_, 1, v___f_2495_);
v___f_2534_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2534_, 0, v___f_2533_);
lean_closure_set(v___f_2534_, 1, v___x_2496_);
v___f_2535_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2535_, 0, v___f_2534_);
lean_closure_set(v___f_2535_, 1, v___f_2497_);
v___x_2536_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34);
v___x_2537_ = l_Lean_MessageData_ofExpr(v_type_2530_);
v___x_2538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2536_);
lean_ctor_set(v___x_2538_, 1, v___x_2537_);
v___x_4622__overap_2539_ = l_Lean_addTrace___redArg(v___x_2498_, v___x_2499_, v_toMonadRef_2529_, v___f_2535_, v_cls_2517_, v___x_2538_);
lean_inc(v___y_2509_);
lean_inc_ref(v___y_2508_);
lean_inc(v___y_2507_);
lean_inc_ref(v___y_2506_);
lean_inc(v___y_2505_);
lean_inc_ref(v___y_2504_);
lean_inc(v___y_2503_);
lean_inc_ref(v___y_2502_);
v___x_2540_ = lean_apply_9(v___x_4622__overap_2539_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, lean_box(0));
return v___x_2540_;
}
}
v___jp_2511_:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = lean_box(0);
v___x_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
return v___x_2513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed(lean_object** _args){
lean_object* v___x_2541_ = _args[0];
lean_object* v___f_2542_ = _args[1];
lean_object* v___x_2543_ = _args[2];
lean_object* v___f_2544_ = _args[3];
lean_object* v___x_2545_ = _args[4];
lean_object* v___f_2546_ = _args[5];
lean_object* v___x_2547_ = _args[6];
lean_object* v___x_2548_ = _args[7];
lean_object* v_x_2549_ = _args[8];
lean_object* v___y_2550_ = _args[9];
lean_object* v___y_2551_ = _args[10];
lean_object* v___y_2552_ = _args[11];
lean_object* v___y_2553_ = _args[12];
lean_object* v___y_2554_ = _args[13];
lean_object* v___y_2555_ = _args[14];
lean_object* v___y_2556_ = _args[15];
lean_object* v___y_2557_ = _args[16];
lean_object* v___y_2558_ = _args[17];
lean_object* v___y_2559_ = _args[18];
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(v___x_2541_, v___f_2542_, v___x_2543_, v___f_2544_, v___x_2545_, v___f_2546_, v___x_2547_, v___x_2548_, v_x_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(lean_object* v_hyps_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_){
_start:
{
lean_object* v___y_2592_; lean_object* v___x_2593_; lean_object* v_toApplicative_2594_; lean_object* v_toFunctor_2595_; lean_object* v_toSeq_2596_; lean_object* v_toSeqLeft_2597_; lean_object* v_toSeqRight_2598_; lean_object* v___f_2599_; lean_object* v___f_2600_; lean_object* v___f_2601_; lean_object* v___f_2602_; lean_object* v___x_2603_; lean_object* v___f_2604_; lean_object* v___f_2605_; lean_object* v___f_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v_toApplicative_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2658_; 
v___x_2593_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1);
v_toApplicative_2594_ = lean_ctor_get(v___x_2593_, 0);
v_toFunctor_2595_ = lean_ctor_get(v_toApplicative_2594_, 0);
v_toSeq_2596_ = lean_ctor_get(v_toApplicative_2594_, 2);
v_toSeqLeft_2597_ = lean_ctor_get(v_toApplicative_2594_, 3);
v_toSeqRight_2598_ = lean_ctor_get(v_toApplicative_2594_, 4);
v___f_2599_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2));
v___f_2600_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3));
lean_inc_ref_n(v_toFunctor_2595_, 2);
v___f_2601_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2601_, 0, v_toFunctor_2595_);
v___f_2602_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2602_, 0, v_toFunctor_2595_);
v___x_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___f_2601_);
lean_ctor_set(v___x_2603_, 1, v___f_2602_);
lean_inc(v_toSeqRight_2598_);
v___f_2604_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2604_, 0, v_toSeqRight_2598_);
lean_inc(v_toSeqLeft_2597_);
v___f_2605_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2605_, 0, v_toSeqLeft_2597_);
lean_inc(v_toSeq_2596_);
v___f_2606_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2606_, 0, v_toSeq_2596_);
v___x_2607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2603_);
lean_ctor_set(v___x_2607_, 1, v___f_2599_);
lean_ctor_set(v___x_2607_, 2, v___f_2606_);
lean_ctor_set(v___x_2607_, 3, v___f_2605_);
lean_ctor_set(v___x_2607_, 4, v___f_2604_);
v___x_2608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
lean_ctor_set(v___x_2608_, 1, v___f_2600_);
v___x_2609_ = l_StateRefT_x27_instMonad___redArg(v___x_2608_);
v_toApplicative_2610_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2658_ == 0)
{
lean_object* v_unused_2659_; 
v_unused_2659_ = lean_ctor_get(v___x_2609_, 1);
lean_dec(v_unused_2659_);
v___x_2612_ = v___x_2609_;
v_isShared_2613_ = v_isSharedCheck_2658_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_toApplicative_2610_);
lean_dec(v___x_2609_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2658_;
goto v_resetjp_2611_;
}
v___jp_2571_:
{
lean_object* v___x_2572_; lean_object* v_rewriteSimpCache_2573_; lean_object* v_rewriteDSimpCache_2574_; lean_object* v_acCache_2575_; lean_object* v_typeAnalysis_2576_; lean_object* v_goal_2577_; lean_object* v_hypotheses_2578_; uint8_t v_didChange_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2590_; 
v___x_2572_ = lean_st_ref_take(v_a_2563_);
v_rewriteSimpCache_2573_ = lean_ctor_get(v___x_2572_, 0);
v_rewriteDSimpCache_2574_ = lean_ctor_get(v___x_2572_, 1);
v_acCache_2575_ = lean_ctor_get(v___x_2572_, 2);
v_typeAnalysis_2576_ = lean_ctor_get(v___x_2572_, 3);
v_goal_2577_ = lean_ctor_get(v___x_2572_, 4);
v_hypotheses_2578_ = lean_ctor_get(v___x_2572_, 5);
v_didChange_2579_ = lean_ctor_get_uint8(v___x_2572_, sizeof(void*)*6);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2581_ = v___x_2572_;
v_isShared_2582_ = v_isSharedCheck_2590_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_hypotheses_2578_);
lean_inc(v_goal_2577_);
lean_inc(v_typeAnalysis_2576_);
lean_inc(v_acCache_2575_);
lean_inc(v_rewriteDSimpCache_2574_);
lean_inc(v_rewriteSimpCache_2573_);
lean_dec(v___x_2572_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2590_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; lean_object* v___x_2585_; 
v___x_2583_ = l_Array_append___redArg(v_hypotheses_2578_, v_hyps_2561_);
lean_dec_ref(v_hyps_2561_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 5, v___x_2583_);
v___x_2585_ = v___x_2581_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_rewriteSimpCache_2573_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v_rewriteDSimpCache_2574_);
lean_ctor_set(v_reuseFailAlloc_2589_, 2, v_acCache_2575_);
lean_ctor_set(v_reuseFailAlloc_2589_, 3, v_typeAnalysis_2576_);
lean_ctor_set(v_reuseFailAlloc_2589_, 4, v_goal_2577_);
lean_ctor_set(v_reuseFailAlloc_2589_, 5, v___x_2583_);
lean_ctor_set_uint8(v_reuseFailAlloc_2589_, sizeof(void*)*6, v_didChange_2579_);
v___x_2585_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2586_ = lean_st_ref_set(v_a_2563_, v___x_2585_);
v___x_2587_ = lean_box(0);
v___x_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
return v___x_2588_;
}
}
}
v___jp_2591_:
{
if (lean_obj_tag(v___y_2592_) == 0)
{
lean_dec_ref_known(v___y_2592_, 1);
goto v___jp_2571_;
}
else
{
lean_dec_ref(v_hyps_2561_);
return v___y_2592_;
}
}
v_resetjp_2611_:
{
lean_object* v_toFunctor_2614_; lean_object* v_toSeq_2615_; lean_object* v_toSeqLeft_2616_; lean_object* v_toSeqRight_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2656_; 
v_toFunctor_2614_ = lean_ctor_get(v_toApplicative_2610_, 0);
v_toSeq_2615_ = lean_ctor_get(v_toApplicative_2610_, 2);
v_toSeqLeft_2616_ = lean_ctor_get(v_toApplicative_2610_, 3);
v_toSeqRight_2617_ = lean_ctor_get(v_toApplicative_2610_, 4);
v_isSharedCheck_2656_ = !lean_is_exclusive(v_toApplicative_2610_);
if (v_isSharedCheck_2656_ == 0)
{
lean_object* v_unused_2657_; 
v_unused_2657_ = lean_ctor_get(v_toApplicative_2610_, 1);
lean_dec(v_unused_2657_);
v___x_2619_ = v_toApplicative_2610_;
v_isShared_2620_ = v_isSharedCheck_2656_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_toSeqRight_2617_);
lean_inc(v_toSeqLeft_2616_);
lean_inc(v_toSeq_2615_);
lean_inc(v_toFunctor_2614_);
lean_dec(v_toApplicative_2610_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2656_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___f_2621_; lean_object* v___f_2622_; lean_object* v___f_2623_; lean_object* v___f_2624_; lean_object* v___x_2625_; lean_object* v___f_2626_; lean_object* v___f_2627_; lean_object* v___f_2628_; lean_object* v___x_2630_; 
v___f_2621_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4));
v___f_2622_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5));
lean_inc_ref(v_toFunctor_2614_);
v___f_2623_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2623_, 0, v_toFunctor_2614_);
v___f_2624_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2624_, 0, v_toFunctor_2614_);
v___x_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___f_2623_);
lean_ctor_set(v___x_2625_, 1, v___f_2624_);
v___f_2626_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2626_, 0, v_toSeqRight_2617_);
v___f_2627_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2627_, 0, v_toSeqLeft_2616_);
v___f_2628_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2628_, 0, v_toSeq_2615_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 4, v___f_2626_);
lean_ctor_set(v___x_2619_, 3, v___f_2627_);
lean_ctor_set(v___x_2619_, 2, v___f_2628_);
lean_ctor_set(v___x_2619_, 1, v___f_2621_);
lean_ctor_set(v___x_2619_, 0, v___x_2625_);
v___x_2630_ = v___x_2619_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2625_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v___f_2621_);
lean_ctor_set(v_reuseFailAlloc_2655_, 2, v___f_2628_);
lean_ctor_set(v_reuseFailAlloc_2655_, 3, v___f_2627_);
lean_ctor_set(v_reuseFailAlloc_2655_, 4, v___f_2626_);
v___x_2630_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
lean_object* v___x_2632_; 
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 1, v___f_2622_);
lean_ctor_set(v___x_2612_, 0, v___x_2630_);
v___x_2632_ = v___x_2612_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v___f_2622_);
v___x_2632_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___f_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2633_ = l_StateRefT_x27_instMonad___redArg(v___x_2632_);
v___x_2634_ = l_ReaderT_instMonad___redArg(v___x_2633_);
v___x_2635_ = l_StateRefT_x27_instMonad___redArg(v___x_2634_);
v___x_2636_ = l_ReaderT_instMonad___redArg(v___x_2635_);
v___f_2637_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___x_2638_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2639_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13);
v___x_2640_ = lean_unsigned_to_nat(0u);
v___x_2641_ = lean_array_get_size(v_hyps_2561_);
v___x_2642_ = lean_nat_dec_lt(v___x_2640_, v___x_2641_);
if (v___x_2642_ == 0)
{
lean_dec_ref(v___x_2636_);
goto v___jp_2571_;
}
else
{
lean_object* v___f_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
lean_inc_ref(v___x_2636_);
v___f_2643_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed), 19, 8);
lean_closure_set(v___f_2643_, 0, v___x_2638_);
lean_closure_set(v___f_2643_, 1, v___f_2637_);
lean_closure_set(v___f_2643_, 2, v___x_2638_);
lean_closure_set(v___f_2643_, 3, v___f_2637_);
lean_closure_set(v___f_2643_, 4, v___x_2638_);
lean_closure_set(v___f_2643_, 5, v___f_2637_);
lean_closure_set(v___f_2643_, 6, v___x_2636_);
lean_closure_set(v___f_2643_, 7, v___x_2639_);
v___x_2644_ = lean_box(0);
v___x_2645_ = lean_nat_dec_le(v___x_2641_, v___x_2641_);
if (v___x_2645_ == 0)
{
if (v___x_2642_ == 0)
{
lean_dec_ref(v___f_2643_);
lean_dec_ref(v___x_2636_);
goto v___jp_2571_;
}
else
{
size_t v___x_2646_; size_t v___x_2647_; lean_object* v___x_4298__overap_2648_; lean_object* v___x_2649_; 
v___x_2646_ = ((size_t)0ULL);
v___x_2647_ = lean_usize_of_nat(v___x_2641_);
lean_inc_ref(v_hyps_2561_);
v___x_4298__overap_2648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2636_, v___f_2643_, v_hyps_2561_, v___x_2646_, v___x_2647_, v___x_2644_);
lean_inc(v_a_2569_);
lean_inc_ref(v_a_2568_);
lean_inc(v_a_2567_);
lean_inc_ref(v_a_2566_);
lean_inc(v_a_2565_);
lean_inc_ref(v_a_2564_);
lean_inc(v_a_2563_);
lean_inc_ref(v_a_2562_);
v___x_2649_ = lean_apply_9(v___x_4298__overap_2648_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, lean_box(0));
v___y_2592_ = v___x_2649_;
goto v___jp_2591_;
}
}
else
{
size_t v___x_2650_; size_t v___x_2651_; lean_object* v___x_4302__overap_2652_; lean_object* v___x_2653_; 
v___x_2650_ = ((size_t)0ULL);
v___x_2651_ = lean_usize_of_nat(v___x_2641_);
lean_inc_ref(v_hyps_2561_);
v___x_4302__overap_2652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2636_, v___f_2643_, v_hyps_2561_, v___x_2650_, v___x_2651_, v___x_2644_);
lean_inc(v_a_2569_);
lean_inc_ref(v_a_2568_);
lean_inc(v_a_2567_);
lean_inc_ref(v_a_2566_);
lean_inc(v_a_2565_);
lean_inc_ref(v_a_2564_);
lean_inc(v_a_2563_);
lean_inc_ref(v_a_2562_);
v___x_2653_ = lean_apply_9(v___x_4302__overap_2652_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, lean_box(0));
v___y_2592_ = v___x_2653_;
goto v___jp_2591_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___boxed(lean_object* v_hyps_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(v_hyps_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(lean_object* v_a_2671_){
_start:
{
lean_object* v___x_2673_; lean_object* v_hypotheses_2674_; lean_object* v___x_2675_; 
v___x_2673_ = lean_st_ref_get(v_a_2671_);
v_hypotheses_2674_ = lean_ctor_get(v___x_2673_, 5);
lean_inc_ref(v_hypotheses_2674_);
lean_dec(v___x_2673_);
v___x_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2675_, 0, v_hypotheses_2674_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg___boxed(lean_object* v_a_2676_, lean_object* v_a_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(v_a_2676_);
lean_dec(v_a_2676_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
lean_object* v___x_2688_; lean_object* v_hypotheses_2689_; lean_object* v___x_2690_; 
v___x_2688_ = lean_st_ref_get(v_a_2680_);
v_hypotheses_2689_ = lean_ctor_get(v___x_2688_, 5);
lean_inc_ref(v_hypotheses_2689_);
lean_dec(v___x_2688_);
v___x_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2690_, 0, v_hypotheses_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed(lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
lean_dec(v_a_2698_);
lean_dec_ref(v_a_2697_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
lean_dec(v_a_2694_);
lean_dec_ref(v_a_2693_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(lean_object* v_hyps_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v___x_2711_; lean_object* v_rewriteSimpCache_2712_; lean_object* v_rewriteDSimpCache_2713_; lean_object* v_acCache_2714_; lean_object* v_typeAnalysis_2715_; lean_object* v_goal_2716_; uint8_t v_didChange_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2727_; 
v___x_2711_ = lean_st_ref_take(v___y_2703_);
v_rewriteSimpCache_2712_ = lean_ctor_get(v___x_2711_, 0);
v_rewriteDSimpCache_2713_ = lean_ctor_get(v___x_2711_, 1);
v_acCache_2714_ = lean_ctor_get(v___x_2711_, 2);
v_typeAnalysis_2715_ = lean_ctor_get(v___x_2711_, 3);
v_goal_2716_ = lean_ctor_get(v___x_2711_, 4);
v_didChange_2717_ = lean_ctor_get_uint8(v___x_2711_, sizeof(void*)*6);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2727_ == 0)
{
lean_object* v_unused_2728_; 
v_unused_2728_ = lean_ctor_get(v___x_2711_, 5);
lean_dec(v_unused_2728_);
v___x_2719_ = v___x_2711_;
v_isShared_2720_ = v_isSharedCheck_2727_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_goal_2716_);
lean_inc(v_typeAnalysis_2715_);
lean_inc(v_acCache_2714_);
lean_inc(v_rewriteDSimpCache_2713_);
lean_inc(v_rewriteSimpCache_2712_);
lean_dec(v___x_2711_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2727_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 5, v_hyps_2701_);
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_rewriteSimpCache_2712_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_rewriteDSimpCache_2713_);
lean_ctor_set(v_reuseFailAlloc_2726_, 2, v_acCache_2714_);
lean_ctor_set(v_reuseFailAlloc_2726_, 3, v_typeAnalysis_2715_);
lean_ctor_set(v_reuseFailAlloc_2726_, 4, v_goal_2716_);
lean_ctor_set(v_reuseFailAlloc_2726_, 5, v_hyps_2701_);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, sizeof(void*)*6, v_didChange_2717_);
v___x_2722_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2723_ = lean_st_ref_set(v___y_2703_, v___x_2722_);
v___x_2724_ = lean_box(0);
v___x_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
return v___x_2725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed(lean_object* v_hyps_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(v_hyps_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1(lean_object* v_inst_2740_, lean_object* v_hyps_2741_){
_start:
{
lean_object* v___f_2742_; lean_object* v___x_2743_; 
v___f_2742_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2742_, 0, v_hyps_2741_);
v___x_2743_ = lean_apply_2(v_inst_2740_, lean_box(0), v___f_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v___x_2753_; lean_object* v_rewriteSimpCache_2754_; lean_object* v_rewriteDSimpCache_2755_; lean_object* v_acCache_2756_; lean_object* v_typeAnalysis_2757_; lean_object* v_goal_2758_; uint8_t v_didChange_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2770_; 
v___x_2753_ = lean_st_ref_take(v___y_2745_);
v_rewriteSimpCache_2754_ = lean_ctor_get(v___x_2753_, 0);
v_rewriteDSimpCache_2755_ = lean_ctor_get(v___x_2753_, 1);
v_acCache_2756_ = lean_ctor_get(v___x_2753_, 2);
v_typeAnalysis_2757_ = lean_ctor_get(v___x_2753_, 3);
v_goal_2758_ = lean_ctor_get(v___x_2753_, 4);
v_didChange_2759_ = lean_ctor_get_uint8(v___x_2753_, sizeof(void*)*6);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2770_ == 0)
{
lean_object* v_unused_2771_; 
v_unused_2771_ = lean_ctor_get(v___x_2753_, 5);
lean_dec(v_unused_2771_);
v___x_2761_ = v___x_2753_;
v_isShared_2762_ = v_isSharedCheck_2770_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_goal_2758_);
lean_inc(v_typeAnalysis_2757_);
lean_inc(v_acCache_2756_);
lean_inc(v_rewriteDSimpCache_2755_);
lean_inc(v_rewriteSimpCache_2754_);
lean_dec(v___x_2753_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2770_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; lean_object* v___x_2765_; 
v___x_2763_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 5, v___x_2763_);
v___x_2765_ = v___x_2761_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_rewriteSimpCache_2754_);
lean_ctor_set(v_reuseFailAlloc_2769_, 1, v_rewriteDSimpCache_2755_);
lean_ctor_set(v_reuseFailAlloc_2769_, 2, v_acCache_2756_);
lean_ctor_set(v_reuseFailAlloc_2769_, 3, v_typeAnalysis_2757_);
lean_ctor_set(v_reuseFailAlloc_2769_, 4, v_goal_2758_);
lean_ctor_set(v_reuseFailAlloc_2769_, 5, v___x_2763_);
lean_ctor_set_uint8(v_reuseFailAlloc_2769_, sizeof(void*)*6, v_didChange_2759_);
v___x_2765_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2766_ = lean_st_ref_set(v___y_2745_, v___x_2765_);
v___x_2767_ = lean_box(0);
v___x_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
return v___x_2768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2___boxed(lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(lean_object* v_toPure_2782_, lean_object* v_cls_2783_, lean_object* v_____do__lift_2784_, lean_object* v_____do__lift_2785_){
_start:
{
uint8_t v_hasTrace_2786_; 
v_hasTrace_2786_ = lean_ctor_get_uint8(v_____do__lift_2785_, sizeof(void*)*1);
if (v_hasTrace_2786_ == 0)
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
lean_dec(v_cls_2783_);
v___x_2787_ = lean_box(v_hasTrace_2786_);
v___x_2788_ = lean_apply_2(v_toPure_2782_, lean_box(0), v___x_2787_);
return v___x_2788_;
}
else
{
lean_object* v___x_2789_; lean_object* v___x_2790_; uint8_t v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2789_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19));
v___x_2790_ = l_Lean_Name_append(v___x_2789_, v_cls_2783_);
v___x_2791_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2784_, v_____do__lift_2785_, v___x_2790_);
lean_dec(v___x_2790_);
v___x_2792_ = lean_box(v___x_2791_);
v___x_2793_ = lean_apply_2(v_toPure_2782_, lean_box(0), v___x_2792_);
return v___x_2793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed(lean_object* v_toPure_2794_, lean_object* v_cls_2795_, lean_object* v_____do__lift_2796_, lean_object* v_____do__lift_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(v_toPure_2794_, v_cls_2795_, v_____do__lift_2796_, v_____do__lift_2797_);
lean_dec_ref(v_____do__lift_2797_);
lean_dec_ref(v_____do__lift_2796_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4(lean_object* v_toPure_2799_, lean_object* v_cls_2800_, lean_object* v_toBind_2801_, lean_object* v_inst_2802_, lean_object* v_____do__lift_2803_){
_start:
{
lean_object* v___f_2804_; lean_object* v___x_2805_; 
v___f_2804_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_2804_, 0, v_toPure_2799_);
lean_closure_set(v___f_2804_, 1, v_cls_2800_);
lean_closure_set(v___f_2804_, 2, v_____do__lift_2803_);
v___x_2805_ = lean_apply_4(v_toBind_2801_, lean_box(0), lean_box(0), v_inst_2802_, v___f_2804_);
return v___x_2805_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0));
v___x_2808_ = l_Lean_stringToMessageData(v___x_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(lean_object* v_toPure_2809_, lean_object* v_a_2810_, lean_object* v___y_2811_, lean_object* v_inst_2812_, lean_object* v_inst_2813_, lean_object* v_inst_2814_, lean_object* v_inst_2815_, lean_object* v_cls_2816_, uint8_t v_____do__lift_2817_){
_start:
{
if (v_____do__lift_2817_ == 0)
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
lean_dec(v_cls_2816_);
lean_dec(v_inst_2815_);
lean_dec_ref(v_inst_2814_);
lean_dec_ref(v_inst_2813_);
lean_dec_ref(v_inst_2812_);
lean_dec_ref(v___y_2811_);
lean_dec_ref(v_a_2810_);
v___x_2818_ = lean_box(0);
v___x_2819_ = lean_apply_2(v_toPure_2809_, lean_box(0), v___x_2818_);
return v___x_2819_;
}
else
{
lean_object* v_type_2820_; lean_object* v_type_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
lean_dec(v_toPure_2809_);
v_type_2820_ = lean_ctor_get(v_a_2810_, 1);
lean_inc_ref(v_type_2820_);
lean_dec_ref(v_a_2810_);
v_type_2821_ = lean_ctor_get(v___y_2811_, 1);
lean_inc_ref(v_type_2821_);
lean_dec_ref(v___y_2811_);
v___x_2822_ = l_Lean_MessageData_ofExpr(v_type_2820_);
v___x_2823_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_2824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2822_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = l_Lean_MessageData_ofExpr(v_type_2821_);
v___x_2826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2824_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = l_Lean_addTrace___redArg(v_inst_2812_, v_inst_2813_, v_inst_2814_, v_inst_2815_, v_cls_2816_, v___x_2826_);
return v___x_2827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed(lean_object* v_toPure_2828_, lean_object* v_a_2829_, lean_object* v___y_2830_, lean_object* v_inst_2831_, lean_object* v_inst_2832_, lean_object* v_inst_2833_, lean_object* v_inst_2834_, lean_object* v_cls_2835_, lean_object* v_____do__lift_2836_){
_start:
{
uint8_t v_____do__lift_3068__boxed_2837_; lean_object* v_res_2838_; 
v_____do__lift_3068__boxed_2837_ = lean_unbox(v_____do__lift_2836_);
v_res_2838_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(v_toPure_2828_, v_a_2829_, v___y_2830_, v_inst_2831_, v_inst_2832_, v_inst_2833_, v_inst_2834_, v_cls_2835_, v_____do__lift_3068__boxed_2837_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6(lean_object* v_inst_2839_, lean_object* v_toPure_2840_, lean_object* v_toBind_2841_, lean_object* v_inst_2842_, lean_object* v_a_2843_, lean_object* v_inst_2844_, lean_object* v_inst_2845_, lean_object* v_inst_2846_, lean_object* v_x_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v_getInheritedTraceOptions_2849_; lean_object* v_cls_2850_; lean_object* v___f_2851_; lean_object* v___f_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v_getInheritedTraceOptions_2849_ = lean_ctor_get(v_inst_2839_, 2);
lean_inc(v_getInheritedTraceOptions_2849_);
v_cls_2850_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
lean_inc_n(v_toBind_2841_, 2);
lean_inc(v_toPure_2840_);
v___f_2851_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_2851_, 0, v_toPure_2840_);
lean_closure_set(v___f_2851_, 1, v_cls_2850_);
lean_closure_set(v___f_2851_, 2, v_toBind_2841_);
lean_closure_set(v___f_2851_, 3, v_inst_2842_);
v___f_2852_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_2852_, 0, v_toPure_2840_);
lean_closure_set(v___f_2852_, 1, v_a_2843_);
lean_closure_set(v___f_2852_, 2, v___y_2848_);
lean_closure_set(v___f_2852_, 3, v_inst_2844_);
lean_closure_set(v___f_2852_, 4, v_inst_2839_);
lean_closure_set(v___f_2852_, 5, v_inst_2845_);
lean_closure_set(v___f_2852_, 6, v_inst_2846_);
lean_closure_set(v___f_2852_, 7, v_cls_2850_);
v___x_2853_ = lean_apply_4(v_toBind_2841_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_2849_, v___f_2851_);
v___x_2854_ = lean_apply_4(v_toBind_2841_, lean_box(0), lean_box(0), v___x_2853_, v___f_2852_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11(lean_object* v_toPure_2855_, lean_object* v_res_2856_, lean_object* v_____r_2857_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = lean_apply_2(v_toPure_2855_, lean_box(0), v_res_2856_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7(lean_object* v_inst_2859_, lean_object* v_toBind_2860_, lean_object* v___f_2861_, lean_object* v_____r_2862_){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2863_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed), 9, 0);
v___x_2864_ = lean_apply_2(v_inst_2859_, lean_box(0), v___x_2863_);
v___x_2865_ = lean_apply_4(v_toBind_2860_, lean_box(0), lean_box(0), v___x_2864_, v___f_2861_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10(lean_object* v___f_2866_, lean_object* v_____r_2867_){
_start:
{
lean_object* v___x_2868_; 
v___x_2868_ = lean_apply_1(v___f_2866_, v_____r_2867_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(lean_object* v___f_2869_, lean_object* v_type_2870_, lean_object* v_type_2871_, lean_object* v_inst_2872_, lean_object* v_inst_2873_, lean_object* v_inst_2874_, lean_object* v_inst_2875_, lean_object* v_cls_2876_, lean_object* v_toBind_2877_, lean_object* v___f_2878_, uint8_t v_____do__lift_2879_){
_start:
{
if (v_____do__lift_2879_ == 0)
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
lean_dec(v___f_2878_);
lean_dec(v_toBind_2877_);
lean_dec(v_cls_2876_);
lean_dec(v_inst_2875_);
lean_dec_ref(v_inst_2874_);
lean_dec_ref(v_inst_2873_);
lean_dec_ref(v_inst_2872_);
lean_dec_ref(v_type_2871_);
lean_dec_ref(v_type_2870_);
v___x_2880_ = lean_box(0);
v___x_2881_ = lean_apply_1(v___f_2869_, v___x_2880_);
return v___x_2881_;
}
else
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
lean_dec(v___f_2869_);
v___x_2882_ = l_Lean_MessageData_ofExpr(v_type_2870_);
v___x_2883_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_2884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2882_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
v___x_2885_ = l_Lean_MessageData_ofExpr(v_type_2871_);
v___x_2886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2884_);
lean_ctor_set(v___x_2886_, 1, v___x_2885_);
v___x_2887_ = l_Lean_addTrace___redArg(v_inst_2872_, v_inst_2873_, v_inst_2874_, v_inst_2875_, v_cls_2876_, v___x_2886_);
v___x_2888_ = lean_apply_4(v_toBind_2877_, lean_box(0), lean_box(0), v___x_2887_, v___f_2878_);
return v___x_2888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed(lean_object* v___f_2889_, lean_object* v_type_2890_, lean_object* v_type_2891_, lean_object* v_inst_2892_, lean_object* v_inst_2893_, lean_object* v_inst_2894_, lean_object* v_inst_2895_, lean_object* v_cls_2896_, lean_object* v_toBind_2897_, lean_object* v___f_2898_, lean_object* v_____do__lift_2899_){
_start:
{
uint8_t v_____do__lift_3168__boxed_2900_; lean_object* v_res_2901_; 
v_____do__lift_3168__boxed_2900_ = lean_unbox(v_____do__lift_2899_);
v_res_2901_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(v___f_2889_, v_type_2890_, v_type_2891_, v_inst_2892_, v_inst_2893_, v_inst_2894_, v_inst_2895_, v_cls_2896_, v_toBind_2897_, v___f_2898_, v_____do__lift_3168__boxed_2900_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13(lean_object* v_toPure_2902_, lean_object* v_inst_2903_, lean_object* v_toBind_2904_, lean_object* v_inst_2905_, lean_object* v___f_2906_, lean_object* v_a_2907_, lean_object* v_inst_2908_, lean_object* v_inst_2909_, lean_object* v_inst_2910_, lean_object* v_inst_2911_, lean_object* v___f_2912_, lean_object* v_res_2913_){
_start:
{
lean_object* v___x_2914_; lean_object* v_zero_2915_; uint8_t v_isZero_2916_; 
v___x_2914_ = lean_array_get_size(v_res_2913_);
v_zero_2915_ = lean_unsigned_to_nat(0u);
v_isZero_2916_ = lean_nat_dec_eq(v___x_2914_, v_zero_2915_);
if (v_isZero_2916_ == 1)
{
lean_object* v___f_2917_; lean_object* v___f_2918_; lean_object* v___x_2919_; uint8_t v___x_2920_; 
lean_dec(v___f_2912_);
lean_dec(v_inst_2911_);
lean_dec_ref(v_inst_2910_);
lean_dec(v_inst_2909_);
lean_dec_ref(v_inst_2908_);
lean_dec_ref(v_a_2907_);
lean_inc_ref(v_res_2913_);
lean_inc(v_toPure_2902_);
v___f_2917_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_2917_, 0, v_toPure_2902_);
lean_closure_set(v___f_2917_, 1, v_res_2913_);
lean_inc(v_toBind_2904_);
v___f_2918_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_2918_, 0, v_inst_2903_);
lean_closure_set(v___f_2918_, 1, v_toBind_2904_);
lean_closure_set(v___f_2918_, 2, v___f_2917_);
v___x_2919_ = lean_box(0);
v___x_2920_ = lean_nat_dec_lt(v_zero_2915_, v___x_2914_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
lean_dec_ref(v_res_2913_);
lean_dec(v___f_2906_);
lean_dec_ref(v_inst_2905_);
v___x_2921_ = lean_apply_2(v_toPure_2902_, lean_box(0), v___x_2919_);
v___x_2922_ = lean_apply_4(v_toBind_2904_, lean_box(0), lean_box(0), v___x_2921_, v___f_2918_);
return v___x_2922_;
}
else
{
uint8_t v___x_2923_; 
v___x_2923_ = lean_nat_dec_le(v___x_2914_, v___x_2914_);
if (v___x_2923_ == 0)
{
if (v___x_2920_ == 0)
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
lean_dec_ref(v_res_2913_);
lean_dec(v___f_2906_);
lean_dec_ref(v_inst_2905_);
v___x_2924_ = lean_apply_2(v_toPure_2902_, lean_box(0), v___x_2919_);
v___x_2925_ = lean_apply_4(v_toBind_2904_, lean_box(0), lean_box(0), v___x_2924_, v___f_2918_);
return v___x_2925_;
}
else
{
size_t v___x_2926_; size_t v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
lean_dec(v_toPure_2902_);
v___x_2926_ = ((size_t)0ULL);
v___x_2927_ = lean_usize_of_nat(v___x_2914_);
v___x_2928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2905_, v___f_2906_, v_res_2913_, v___x_2926_, v___x_2927_, v___x_2919_);
v___x_2929_ = lean_apply_4(v_toBind_2904_, lean_box(0), lean_box(0), v___x_2928_, v___f_2918_);
return v___x_2929_;
}
}
else
{
size_t v___x_2930_; size_t v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
lean_dec(v_toPure_2902_);
v___x_2930_ = ((size_t)0ULL);
v___x_2931_ = lean_usize_of_nat(v___x_2914_);
v___x_2932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2905_, v___f_2906_, v_res_2913_, v___x_2930_, v___x_2931_, v___x_2919_);
v___x_2933_ = lean_apply_4(v_toBind_2904_, lean_box(0), lean_box(0), v___x_2932_, v___f_2918_);
return v___x_2933_;
}
}
}
else
{
lean_object* v_one_2934_; lean_object* v_n_2935_; uint8_t v_isZero_2936_; 
lean_dec(v___f_2906_);
v_one_2934_ = lean_unsigned_to_nat(1u);
v_n_2935_ = lean_nat_sub(v___x_2914_, v_one_2934_);
v_isZero_2936_ = lean_nat_dec_eq(v_n_2935_, v_zero_2915_);
lean_dec(v_n_2935_);
if (v_isZero_2936_ == 1)
{
lean_object* v_newHyp_2937_; lean_object* v_type_2938_; lean_object* v_type_2939_; uint8_t v___x_2940_; 
lean_dec(v___f_2912_);
v_newHyp_2937_ = lean_array_fget_borrowed(v_res_2913_, v_zero_2915_);
v_type_2938_ = lean_ctor_get(v_newHyp_2937_, 1);
v_type_2939_ = lean_ctor_get(v_a_2907_, 1);
lean_inc_ref(v_type_2939_);
lean_dec_ref(v_a_2907_);
v___x_2940_ = lean_expr_eqv(v_type_2938_, v_type_2939_);
if (v___x_2940_ == 0)
{
lean_object* v_getInheritedTraceOptions_2941_; lean_object* v___f_2942_; lean_object* v___f_2943_; lean_object* v___f_2944_; lean_object* v_cls_2945_; lean_object* v___f_2946_; lean_object* v___f_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
lean_inc_ref(v_type_2938_);
v_getInheritedTraceOptions_2941_ = lean_ctor_get(v_inst_2908_, 2);
lean_inc(v_getInheritedTraceOptions_2941_);
lean_inc(v_toPure_2902_);
v___f_2942_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_2942_, 0, v_toPure_2902_);
lean_closure_set(v___f_2942_, 1, v_res_2913_);
lean_inc_n(v_toBind_2904_, 4);
v___f_2943_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_2943_, 0, v_inst_2903_);
lean_closure_set(v___f_2943_, 1, v_toBind_2904_);
lean_closure_set(v___f_2943_, 2, v___f_2942_);
lean_inc_ref(v___f_2943_);
v___f_2944_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_2944_, 0, v___f_2943_);
v_cls_2945_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___f_2946_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_2946_, 0, v_toPure_2902_);
lean_closure_set(v___f_2946_, 1, v_cls_2945_);
lean_closure_set(v___f_2946_, 2, v_toBind_2904_);
lean_closure_set(v___f_2946_, 3, v_inst_2909_);
v___f_2947_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_2947_, 0, v___f_2943_);
lean_closure_set(v___f_2947_, 1, v_type_2939_);
lean_closure_set(v___f_2947_, 2, v_type_2938_);
lean_closure_set(v___f_2947_, 3, v_inst_2905_);
lean_closure_set(v___f_2947_, 4, v_inst_2908_);
lean_closure_set(v___f_2947_, 5, v_inst_2910_);
lean_closure_set(v___f_2947_, 6, v_inst_2911_);
lean_closure_set(v___f_2947_, 7, v_cls_2945_);
lean_closure_set(v___f_2947_, 8, v_toBind_2904_);
lean_closure_set(v___f_2947_, 9, v___f_2944_);
v___x_2948_ = lean_apply_4(v_toBind_2904_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_2941_, v___f_2946_);
v___x_2949_ = lean_apply_4(v_toBind_2904_, lean_box(0), lean_box(0), v___x_2948_, v___f_2947_);
return v___x_2949_;
}
else
{
lean_object* v___x_2950_; 
lean_dec_ref(v_type_2939_);
lean_dec(v_inst_2911_);
lean_dec_ref(v_inst_2910_);
lean_dec(v_inst_2909_);
lean_dec_ref(v_inst_2908_);
lean_dec_ref(v_inst_2905_);
lean_dec(v_toBind_2904_);
lean_dec(v_inst_2903_);
v___x_2950_ = lean_apply_2(v_toPure_2902_, lean_box(0), v_res_2913_);
return v___x_2950_;
}
}
else
{
lean_object* v___f_2951_; lean_object* v___f_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; 
lean_dec(v_inst_2911_);
lean_dec_ref(v_inst_2910_);
lean_dec(v_inst_2909_);
lean_dec_ref(v_inst_2908_);
lean_dec_ref(v_a_2907_);
lean_inc_ref(v_res_2913_);
lean_inc(v_toPure_2902_);
v___f_2951_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_2951_, 0, v_toPure_2902_);
lean_closure_set(v___f_2951_, 1, v_res_2913_);
lean_inc(v_toBind_2904_);
v___f_2952_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_2952_, 0, v_inst_2903_);
lean_closure_set(v___f_2952_, 1, v_toBind_2904_);
lean_closure_set(v___f_2952_, 2, v___f_2951_);
v___x_2953_ = lean_box(0);
v___x_2954_ = lean_nat_dec_lt(v_zero_2915_, v___x_2914_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
lean_dec_ref(v_res_2913_);
lean_dec(v___f_2912_);
lean_dec_ref(v_inst_2905_);
v___x_2955_ = lean_apply_2(v_toPure_2902_, lean_box(0), v___x_2953_);
v___x_2956_ = lean_apply_4(v_toBind_2904_, lean_box(0), lean_box(0), v___x_2955_, v___f_2952_);
return v___x_2956_;
}
else
{
uint8_t v___x_2957_; 
v___x_2957_ = lean_nat_dec_le(v___x_2914_, v___x_2914_);
if (v___x_2957_ == 0)
{
if (v___x_2954_ == 0)
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
lean_dec_ref(v_res_2913_);
lean_dec(v___f_2912_);
lean_dec_ref(v_inst_2905_);
v___x_2958_ = lean_apply_2(v_toPure_2902_, lean_box(0), v___x_2953_);
v___x_2959_ = lean_apply_4(v_toBind_2904_, lean_box(0), lean_box(0), v___x_2958_, v___f_2952_);
return v___x_2959_;
}
else
{
size_t v___x_2960_; size_t v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
lean_dec(v_toPure_2902_);
v___x_2960_ = ((size_t)0ULL);
v___x_2961_ = lean_usize_of_nat(v___x_2914_);
v___x_2962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2905_, v___f_2912_, v_res_2913_, v___x_2960_, v___x_2961_, v___x_2953_);
v___x_2963_ = lean_apply_4(v_toBind_2904_, lean_box(0), lean_box(0), v___x_2962_, v___f_2952_);
return v___x_2963_;
}
}
else
{
size_t v___x_2964_; size_t v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
lean_dec(v_toPure_2902_);
v___x_2964_ = ((size_t)0ULL);
v___x_2965_ = lean_usize_of_nat(v___x_2914_);
v___x_2966_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2905_, v___f_2912_, v_res_2913_, v___x_2964_, v___x_2965_, v___x_2953_);
v___x_2967_ = lean_apply_4(v_toBind_2904_, lean_box(0), lean_box(0), v___x_2966_, v___f_2952_);
return v___x_2967_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(lean_object* v_bs_2968_, lean_object* v_toPure_2969_, lean_object* v_____do__lift_2970_){
_start:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2971_ = l_Array_append___redArg(v_bs_2968_, v_____do__lift_2970_);
v___x_2972_ = lean_apply_2(v_toPure_2969_, lean_box(0), v___x_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed(lean_object* v_bs_2973_, lean_object* v_toPure_2974_, lean_object* v_____do__lift_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(v_bs_2973_, v_toPure_2974_, v_____do__lift_2975_);
lean_dec_ref(v_____do__lift_2975_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9(lean_object* v_inst_2977_, lean_object* v_toPure_2978_, lean_object* v_toBind_2979_, lean_object* v_inst_2980_, lean_object* v_inst_2981_, lean_object* v_inst_2982_, lean_object* v_inst_2983_, lean_object* v_inst_2984_, lean_object* v_f_2985_, lean_object* v_bs_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v___f_2988_; lean_object* v___f_2989_; lean_object* v___f_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
lean_inc(v_inst_2983_);
lean_inc_ref(v_inst_2982_);
lean_inc_ref(v_inst_2981_);
lean_inc_ref_n(v_a_2987_, 2);
lean_inc(v_inst_2980_);
lean_inc_n(v_toBind_2979_, 3);
lean_inc_n(v_toPure_2978_, 2);
lean_inc_ref(v_inst_2977_);
v___f_2988_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6), 10, 8);
lean_closure_set(v___f_2988_, 0, v_inst_2977_);
lean_closure_set(v___f_2988_, 1, v_toPure_2978_);
lean_closure_set(v___f_2988_, 2, v_toBind_2979_);
lean_closure_set(v___f_2988_, 3, v_inst_2980_);
lean_closure_set(v___f_2988_, 4, v_a_2987_);
lean_closure_set(v___f_2988_, 5, v_inst_2981_);
lean_closure_set(v___f_2988_, 6, v_inst_2982_);
lean_closure_set(v___f_2988_, 7, v_inst_2983_);
lean_inc_ref(v___f_2988_);
v___f_2989_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13), 12, 11);
lean_closure_set(v___f_2989_, 0, v_toPure_2978_);
lean_closure_set(v___f_2989_, 1, v_inst_2984_);
lean_closure_set(v___f_2989_, 2, v_toBind_2979_);
lean_closure_set(v___f_2989_, 3, v_inst_2981_);
lean_closure_set(v___f_2989_, 4, v___f_2988_);
lean_closure_set(v___f_2989_, 5, v_a_2987_);
lean_closure_set(v___f_2989_, 6, v_inst_2977_);
lean_closure_set(v___f_2989_, 7, v_inst_2980_);
lean_closure_set(v___f_2989_, 8, v_inst_2982_);
lean_closure_set(v___f_2989_, 9, v_inst_2983_);
lean_closure_set(v___f_2989_, 10, v___f_2988_);
v___f_2990_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed), 3, 2);
lean_closure_set(v___f_2990_, 0, v_bs_2986_);
lean_closure_set(v___f_2990_, 1, v_toPure_2978_);
v___x_2991_ = lean_apply_1(v_f_2985_, v_a_2987_);
v___x_2992_ = lean_apply_4(v_toBind_2979_, lean_box(0), lean_box(0), v___x_2991_, v___f_2989_);
v___x_2993_ = lean_apply_4(v_toBind_2979_, lean_box(0), lean_box(0), v___x_2992_, v___f_2990_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14(lean_object* v_hyps_2996_, lean_object* v_toPure_2997_, lean_object* v_toBind_2998_, lean_object* v___f_2999_, lean_object* v_inst_3000_, lean_object* v___f_3001_, lean_object* v_____r_3002_){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; 
v___x_3003_ = lean_unsigned_to_nat(0u);
v___x_3004_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0));
v___x_3005_ = lean_array_get_size(v_hyps_2996_);
v___x_3006_ = lean_nat_dec_lt(v___x_3003_, v___x_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
lean_dec(v___f_3001_);
lean_dec_ref(v_inst_3000_);
lean_dec_ref(v_hyps_2996_);
v___x_3007_ = lean_apply_2(v_toPure_2997_, lean_box(0), v___x_3004_);
v___x_3008_ = lean_apply_4(v_toBind_2998_, lean_box(0), lean_box(0), v___x_3007_, v___f_2999_);
return v___x_3008_;
}
else
{
uint8_t v___x_3009_; 
v___x_3009_ = lean_nat_dec_le(v___x_3005_, v___x_3005_);
if (v___x_3009_ == 0)
{
if (v___x_3006_ == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
lean_dec(v___f_3001_);
lean_dec_ref(v_inst_3000_);
lean_dec_ref(v_hyps_2996_);
v___x_3010_ = lean_apply_2(v_toPure_2997_, lean_box(0), v___x_3004_);
v___x_3011_ = lean_apply_4(v_toBind_2998_, lean_box(0), lean_box(0), v___x_3010_, v___f_2999_);
return v___x_3011_;
}
else
{
size_t v___x_3012_; size_t v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
lean_dec(v_toPure_2997_);
v___x_3012_ = ((size_t)0ULL);
v___x_3013_ = lean_usize_of_nat(v___x_3005_);
v___x_3014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3000_, v___f_3001_, v_hyps_2996_, v___x_3012_, v___x_3013_, v___x_3004_);
v___x_3015_ = lean_apply_4(v_toBind_2998_, lean_box(0), lean_box(0), v___x_3014_, v___f_2999_);
return v___x_3015_;
}
}
else
{
size_t v___x_3016_; size_t v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
lean_dec(v_toPure_2997_);
v___x_3016_ = ((size_t)0ULL);
v___x_3017_ = lean_usize_of_nat(v___x_3005_);
v___x_3018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3000_, v___f_3001_, v_hyps_2996_, v___x_3016_, v___x_3017_, v___x_3004_);
v___x_3019_ = lean_apply_4(v_toBind_2998_, lean_box(0), lean_box(0), v___x_3018_, v___f_2999_);
return v___x_3019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15(lean_object* v_toPure_3020_, lean_object* v_toBind_3021_, lean_object* v___f_3022_, lean_object* v_inst_3023_, lean_object* v___f_3024_, lean_object* v_inst_3025_, lean_object* v___f_3026_, lean_object* v_hyps_3027_){
_start:
{
lean_object* v___f_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
lean_inc(v_toBind_3021_);
v___f_3028_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14), 7, 6);
lean_closure_set(v___f_3028_, 0, v_hyps_3027_);
lean_closure_set(v___f_3028_, 1, v_toPure_3020_);
lean_closure_set(v___f_3028_, 2, v_toBind_3021_);
lean_closure_set(v___f_3028_, 3, v___f_3022_);
lean_closure_set(v___f_3028_, 4, v_inst_3023_);
lean_closure_set(v___f_3028_, 5, v___f_3024_);
v___x_3029_ = lean_apply_2(v_inst_3025_, lean_box(0), v___f_3026_);
v___x_3030_ = lean_apply_4(v_toBind_3021_, lean_box(0), lean_box(0), v___x_3029_, v___f_3028_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg(lean_object* v_inst_3032_, lean_object* v_inst_3033_, lean_object* v_inst_3034_, lean_object* v_inst_3035_, lean_object* v_inst_3036_, lean_object* v_inst_3037_, lean_object* v_f_3038_){
_start:
{
lean_object* v_toApplicative_3039_; lean_object* v_toBind_3040_; lean_object* v_toPure_3041_; lean_object* v___f_3042_; lean_object* v___f_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___f_3046_; lean_object* v___f_3047_; lean_object* v___x_3048_; 
v_toApplicative_3039_ = lean_ctor_get(v_inst_3032_, 0);
v_toBind_3040_ = lean_ctor_get(v_inst_3032_, 1);
lean_inc_n(v_toBind_3040_, 3);
v_toPure_3041_ = lean_ctor_get(v_toApplicative_3039_, 1);
lean_inc_n(v_toPure_3041_, 2);
lean_inc_n(v_inst_3037_, 3);
v___f_3042_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3042_, 0, v_inst_3037_);
v___f_3043_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3044_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 9, 0);
v___x_3045_ = lean_apply_2(v_inst_3037_, lean_box(0), v___x_3044_);
lean_inc_ref(v_inst_3032_);
v___f_3046_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3046_, 0, v_inst_3033_);
lean_closure_set(v___f_3046_, 1, v_toPure_3041_);
lean_closure_set(v___f_3046_, 2, v_toBind_3040_);
lean_closure_set(v___f_3046_, 3, v_inst_3034_);
lean_closure_set(v___f_3046_, 4, v_inst_3032_);
lean_closure_set(v___f_3046_, 5, v_inst_3036_);
lean_closure_set(v___f_3046_, 6, v_inst_3035_);
lean_closure_set(v___f_3046_, 7, v_inst_3037_);
lean_closure_set(v___f_3046_, 8, v_f_3038_);
v___f_3047_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3047_, 0, v_toPure_3041_);
lean_closure_set(v___f_3047_, 1, v_toBind_3040_);
lean_closure_set(v___f_3047_, 2, v___f_3042_);
lean_closure_set(v___f_3047_, 3, v_inst_3032_);
lean_closure_set(v___f_3047_, 4, v___f_3046_);
lean_closure_set(v___f_3047_, 5, v_inst_3037_);
lean_closure_set(v___f_3047_, 6, v___f_3043_);
v___x_3048_ = lean_apply_4(v_toBind_3040_, lean_box(0), lean_box(0), v___x_3045_, v___f_3047_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps(lean_object* v_m_3049_, lean_object* v_inst_3050_, lean_object* v_inst_3051_, lean_object* v_inst_3052_, lean_object* v_inst_3053_, lean_object* v_inst_3054_, lean_object* v_inst_3055_, lean_object* v_f_3056_){
_start:
{
lean_object* v_toApplicative_3057_; lean_object* v_toBind_3058_; lean_object* v_toPure_3059_; lean_object* v___f_3060_; lean_object* v___f_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___f_3064_; lean_object* v___f_3065_; lean_object* v___x_3066_; 
v_toApplicative_3057_ = lean_ctor_get(v_inst_3050_, 0);
v_toBind_3058_ = lean_ctor_get(v_inst_3050_, 1);
lean_inc_n(v_toBind_3058_, 3);
v_toPure_3059_ = lean_ctor_get(v_toApplicative_3057_, 1);
lean_inc_n(v_toPure_3059_, 2);
lean_inc_n(v_inst_3055_, 3);
v___f_3060_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3060_, 0, v_inst_3055_);
v___f_3061_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3062_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 9, 0);
v___x_3063_ = lean_apply_2(v_inst_3055_, lean_box(0), v___x_3062_);
lean_inc_ref(v_inst_3050_);
v___f_3064_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3064_, 0, v_inst_3051_);
lean_closure_set(v___f_3064_, 1, v_toPure_3059_);
lean_closure_set(v___f_3064_, 2, v_toBind_3058_);
lean_closure_set(v___f_3064_, 3, v_inst_3052_);
lean_closure_set(v___f_3064_, 4, v_inst_3050_);
lean_closure_set(v___f_3064_, 5, v_inst_3054_);
lean_closure_set(v___f_3064_, 6, v_inst_3053_);
lean_closure_set(v___f_3064_, 7, v_inst_3055_);
lean_closure_set(v___f_3064_, 8, v_f_3056_);
v___f_3065_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3065_, 0, v_toPure_3059_);
lean_closure_set(v___f_3065_, 1, v_toBind_3058_);
lean_closure_set(v___f_3065_, 2, v___f_3060_);
lean_closure_set(v___f_3065_, 3, v_inst_3050_);
lean_closure_set(v___f_3065_, 4, v___f_3064_);
lean_closure_set(v___f_3065_, 5, v_inst_3055_);
lean_closure_set(v___f_3065_, 6, v___f_3061_);
v___x_3066_ = lean_apply_4(v_toBind_3058_, lean_box(0), lean_box(0), v___x_3063_, v___f_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0(lean_object* v_toPure_3067_, lean_object* v_____do__lift_3068_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = lean_apply_2(v_toPure_3067_, lean_box(0), v_____do__lift_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(lean_object* v_toPure_3070_, lean_object* v_____r_3071_){
_start:
{
uint8_t v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3072_ = 0;
v___x_3073_ = lean_box(v___x_3072_);
v___x_3074_ = lean_apply_2(v_toPure_3070_, lean_box(0), v___x_3073_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(lean_object* v_snd_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v___x_3085_; lean_object* v_rewriteSimpCache_3086_; lean_object* v_rewriteDSimpCache_3087_; lean_object* v_acCache_3088_; lean_object* v_typeAnalysis_3089_; lean_object* v_goal_3090_; uint8_t v_didChange_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3101_; 
v___x_3085_ = lean_st_ref_take(v___y_3077_);
v_rewriteSimpCache_3086_ = lean_ctor_get(v___x_3085_, 0);
v_rewriteDSimpCache_3087_ = lean_ctor_get(v___x_3085_, 1);
v_acCache_3088_ = lean_ctor_get(v___x_3085_, 2);
v_typeAnalysis_3089_ = lean_ctor_get(v___x_3085_, 3);
v_goal_3090_ = lean_ctor_get(v___x_3085_, 4);
v_didChange_3091_ = lean_ctor_get_uint8(v___x_3085_, sizeof(void*)*6);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3101_ == 0)
{
lean_object* v_unused_3102_; 
v_unused_3102_ = lean_ctor_get(v___x_3085_, 5);
lean_dec(v_unused_3102_);
v___x_3093_ = v___x_3085_;
v_isShared_3094_ = v_isSharedCheck_3101_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_goal_3090_);
lean_inc(v_typeAnalysis_3089_);
lean_inc(v_acCache_3088_);
lean_inc(v_rewriteDSimpCache_3087_);
lean_inc(v_rewriteSimpCache_3086_);
lean_dec(v___x_3085_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3101_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 5, v_snd_3075_);
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_rewriteSimpCache_3086_);
lean_ctor_set(v_reuseFailAlloc_3100_, 1, v_rewriteDSimpCache_3087_);
lean_ctor_set(v_reuseFailAlloc_3100_, 2, v_acCache_3088_);
lean_ctor_set(v_reuseFailAlloc_3100_, 3, v_typeAnalysis_3089_);
lean_ctor_set(v_reuseFailAlloc_3100_, 4, v_goal_3090_);
lean_ctor_set(v_reuseFailAlloc_3100_, 5, v_snd_3075_);
lean_ctor_set_uint8(v_reuseFailAlloc_3100_, sizeof(void*)*6, v_didChange_3091_);
v___x_3096_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3097_ = lean_st_ref_set(v___y_3077_, v___x_3096_);
v___x_3098_ = lean_box(0);
v___x_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
return v___x_3099_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2___boxed(lean_object* v_snd_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(v_snd_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3(lean_object* v_inst_3114_, lean_object* v_toBind_3115_, lean_object* v___f_3116_, lean_object* v_toPure_3117_, lean_object* v_____s_3118_){
_start:
{
lean_object* v_fst_3119_; 
v_fst_3119_ = lean_ctor_get(v_____s_3118_, 0);
if (lean_obj_tag(v_fst_3119_) == 0)
{
lean_object* v_snd_3120_; lean_object* v___f_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
lean_dec(v_toPure_3117_);
v_snd_3120_ = lean_ctor_get(v_____s_3118_, 1);
lean_inc(v_snd_3120_);
lean_dec_ref(v_____s_3118_);
v___f_3121_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2___boxed), 10, 1);
lean_closure_set(v___f_3121_, 0, v_snd_3120_);
v___x_3122_ = lean_apply_2(v_inst_3114_, lean_box(0), v___f_3121_);
v___x_3123_ = lean_apply_4(v_toBind_3115_, lean_box(0), lean_box(0), v___x_3122_, v___f_3116_);
return v___x_3123_;
}
else
{
lean_object* v_val_3124_; lean_object* v___x_3125_; 
lean_inc_ref(v_fst_3119_);
lean_dec_ref(v_____s_3118_);
lean_dec(v___f_3116_);
lean_dec(v_toBind_3115_);
lean_dec(v_inst_3114_);
v_val_3124_ = lean_ctor_get(v_fst_3119_, 0);
lean_inc(v_val_3124_);
lean_dec_ref_known(v_fst_3119_, 1);
v___x_3125_ = lean_apply_2(v_toPure_3117_, lean_box(0), v_val_3124_);
return v___x_3125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(lean_object* v_toPure_3126_, lean_object* v_next_3127_, lean_object* v_G_3128_, lean_object* v_____do__lift_3129_){
_start:
{
if (lean_obj_tag(v_____do__lift_3129_) == 0)
{
lean_object* v_a_3130_; lean_object* v___x_3131_; 
lean_dec(v_G_3128_);
v_a_3130_ = lean_ctor_get(v_____do__lift_3129_, 0);
lean_inc(v_a_3130_);
lean_dec_ref_known(v_____do__lift_3129_, 1);
v___x_3131_ = lean_apply_2(v_toPure_3126_, lean_box(0), v_a_3130_);
return v___x_3131_;
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
lean_dec(v_toPure_3126_);
v_a_3132_ = lean_ctor_get(v_____do__lift_3129_, 0);
lean_inc(v_a_3132_);
lean_dec_ref_known(v_____do__lift_3129_, 1);
v___x_3133_ = lean_unsigned_to_nat(1u);
v___x_3134_ = lean_nat_add(v_next_3127_, v___x_3133_);
v___x_3135_ = lean_apply_4(v_G_3128_, v___x_3134_, v_a_3132_, lean_box(0), lean_box(0));
return v___x_3135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed(lean_object* v_toPure_3136_, lean_object* v_next_3137_, lean_object* v_G_3138_, lean_object* v_____do__lift_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(v_toPure_3136_, v_next_3137_, v_G_3138_, v_____do__lift_3139_);
lean_dec(v_next_3137_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(lean_object* v_snd_3141_, lean_object* v_newHyp_3142_, lean_object* v___x_3143_, lean_object* v_toPure_3144_, lean_object* v_____r_3145_){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3146_ = lean_array_push(v_snd_3141_, v_newHyp_3142_);
v___x_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3143_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
v___x_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
v___x_3149_ = lean_apply_2(v_toPure_3144_, lean_box(0), v___x_3148_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(lean_object* v_toPure_3150_, lean_object* v___x_3151_, lean_object* v_____do__lift_3152_, lean_object* v_____do__lift_3153_){
_start:
{
uint8_t v_hasTrace_3154_; 
v_hasTrace_3154_ = lean_ctor_get_uint8(v_____do__lift_3153_, sizeof(void*)*1);
if (v_hasTrace_3154_ == 0)
{
lean_object* v___x_3155_; lean_object* v___x_3156_; 
lean_dec(v___x_3151_);
v___x_3155_ = lean_box(v_hasTrace_3154_);
v___x_3156_ = lean_apply_2(v_toPure_3150_, lean_box(0), v___x_3155_);
return v___x_3156_;
}
else
{
lean_object* v___x_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3157_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19));
v___x_3158_ = l_Lean_Name_append(v___x_3157_, v___x_3151_);
v___x_3159_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_3152_, v_____do__lift_3153_, v___x_3158_);
lean_dec(v___x_3158_);
v___x_3160_ = lean_box(v___x_3159_);
v___x_3161_ = lean_apply_2(v_toPure_3150_, lean_box(0), v___x_3160_);
return v___x_3161_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9___boxed(lean_object* v_toPure_3162_, lean_object* v___x_3163_, lean_object* v_____do__lift_3164_, lean_object* v_____do__lift_3165_){
_start:
{
lean_object* v_res_3166_; 
v_res_3166_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(v_toPure_3162_, v___x_3163_, v_____do__lift_3164_, v_____do__lift_3165_);
lean_dec_ref(v_____do__lift_3165_);
lean_dec_ref(v_____do__lift_3164_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(lean_object* v_toPure_3167_, lean_object* v___x_3168_, lean_object* v_toBind_3169_, lean_object* v_inst_3170_, lean_object* v_____do__lift_3171_){
_start:
{
lean_object* v___f_3172_; lean_object* v___x_3173_; 
v___f_3172_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9___boxed), 4, 3);
lean_closure_set(v___f_3172_, 0, v_toPure_3167_);
lean_closure_set(v___f_3172_, 1, v___x_3168_);
lean_closure_set(v___f_3172_, 2, v_____do__lift_3171_);
v___x_3173_ = lean_apply_4(v_toBind_3169_, lean_box(0), lean_box(0), v_inst_3170_, v___f_3172_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(lean_object* v___f_3174_, lean_object* v_inst_3175_, lean_object* v___x_3176_, lean_object* v_type_3177_, lean_object* v_inst_3178_, lean_object* v_inst_3179_, lean_object* v_inst_3180_, lean_object* v___x_3181_, lean_object* v_toBind_3182_, lean_object* v___f_3183_, uint8_t v_____do__lift_3184_){
_start:
{
if (v_____do__lift_3184_ == 0)
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
lean_dec(v___f_3183_);
lean_dec(v_toBind_3182_);
lean_dec(v___x_3181_);
lean_dec(v_inst_3180_);
lean_dec_ref(v_inst_3179_);
lean_dec_ref(v_inst_3178_);
lean_dec_ref(v_type_3177_);
lean_dec_ref(v___x_3176_);
lean_dec_ref(v_inst_3175_);
v___x_3185_ = lean_box(0);
v___x_3186_ = lean_apply_1(v___f_3174_, v___x_3185_);
return v___x_3186_;
}
else
{
lean_object* v_toMonadRef_3187_; lean_object* v_type_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
lean_dec(v___f_3174_);
v_toMonadRef_3187_ = lean_ctor_get(v_inst_3175_, 1);
lean_inc_ref(v_toMonadRef_3187_);
lean_dec_ref(v_inst_3175_);
v_type_3188_ = lean_ctor_get(v___x_3176_, 1);
lean_inc_ref(v_type_3188_);
lean_dec_ref(v___x_3176_);
v___x_3189_ = l_Lean_MessageData_ofExpr(v_type_3188_);
v___x_3190_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3189_);
lean_ctor_set(v___x_3191_, 1, v___x_3190_);
v___x_3192_ = l_Lean_MessageData_ofExpr(v_type_3177_);
v___x_3193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3191_);
lean_ctor_set(v___x_3193_, 1, v___x_3192_);
v___x_3194_ = l_Lean_addTrace___redArg(v_inst_3178_, v_inst_3179_, v_toMonadRef_3187_, v_inst_3180_, v___x_3181_, v___x_3193_);
v___x_3195_ = lean_apply_4(v_toBind_3182_, lean_box(0), lean_box(0), v___x_3194_, v___f_3183_);
return v___x_3195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7___boxed(lean_object* v___f_3196_, lean_object* v_inst_3197_, lean_object* v___x_3198_, lean_object* v_type_3199_, lean_object* v_inst_3200_, lean_object* v_inst_3201_, lean_object* v_inst_3202_, lean_object* v___x_3203_, lean_object* v_toBind_3204_, lean_object* v___f_3205_, lean_object* v_____do__lift_3206_){
_start:
{
uint8_t v_____do__lift_1962__boxed_3207_; lean_object* v_res_3208_; 
v_____do__lift_1962__boxed_3207_ = lean_unbox(v_____do__lift_3206_);
v_res_3208_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(v___f_3196_, v_inst_3197_, v___x_3198_, v_type_3199_, v_inst_3200_, v_inst_3201_, v_inst_3202_, v___x_3203_, v_toBind_3204_, v___f_3205_, v_____do__lift_1962__boxed_3207_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(uint8_t v___x_3209_, lean_object* v_snd_3210_, lean_object* v_toPure_3211_, lean_object* v_____r_3212_){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3213_ = lean_box(v___x_3209_);
v___x_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
v___x_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
lean_ctor_set(v___x_3215_, 1, v_snd_3210_);
v___x_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
v___x_3217_ = lean_apply_2(v_toPure_3211_, lean_box(0), v___x_3216_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed(lean_object* v___x_3218_, lean_object* v_snd_3219_, lean_object* v_toPure_3220_, lean_object* v_____r_3221_){
_start:
{
uint8_t v___x_2000__boxed_3222_; lean_object* v_res_3223_; 
v___x_2000__boxed_3222_ = lean_unbox(v___x_3218_);
v_res_3223_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(v___x_2000__boxed_3222_, v_snd_3219_, v_toPure_3220_, v_____r_3221_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(lean_object* v_inst_3224_, lean_object* v_value_3225_, lean_object* v_toBind_3226_, lean_object* v___f_3227_, lean_object* v_____do__lift_3228_){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3229_ = l_Lean_MVarId_assign___redArg(v_inst_3224_, v_____do__lift_3228_, v_value_3225_);
v___x_3230_ = lean_apply_4(v_toBind_3226_, lean_box(0), lean_box(0), v___x_3229_, v___f_3227_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(lean_object* v___x_3231_, lean_object* v_snd_3232_, lean_object* v___x_3233_, lean_object* v_toPure_3234_, lean_object* v_inst_3235_, lean_object* v_toBind_3236_, lean_object* v_inst_3237_, lean_object* v_inst_3238_, lean_object* v_inst_3239_, lean_object* v_inst_3240_, lean_object* v_inst_3241_, lean_object* v_inst_3242_, lean_object* v_newHyp_3243_){
_start:
{
lean_object* v_type_3244_; lean_object* v_value_3245_; uint8_t v___x_3246_; 
v_type_3244_ = lean_ctor_get(v_newHyp_3243_, 1);
v_value_3245_ = lean_ctor_get(v_newHyp_3243_, 2);
lean_inc_ref(v_type_3244_);
v___x_3246_ = l_Lean_Expr_isFalse(v_type_3244_);
if (v___x_3246_ == 0)
{
lean_object* v_type_3247_; lean_object* v___f_3248_; lean_object* v___f_3249_; lean_object* v___f_3250_; lean_object* v___f_3251_; uint8_t v___x_3259_; 
lean_dec_ref(v_inst_3242_);
v_type_3247_ = lean_ctor_get(v___x_3231_, 1);
lean_inc(v_toPure_3234_);
lean_inc(v___x_3233_);
lean_inc_ref(v_newHyp_3243_);
lean_inc(v_snd_3232_);
v___f_3248_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5), 5, 4);
lean_closure_set(v___f_3248_, 0, v_snd_3232_);
lean_closure_set(v___f_3248_, 1, v_newHyp_3243_);
lean_closure_set(v___f_3248_, 2, v___x_3233_);
lean_closure_set(v___f_3248_, 3, v_toPure_3234_);
v___f_3249_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3249_, 0, v___f_3248_);
lean_inc(v_toBind_3236_);
v___f_3250_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3250_, 0, v_inst_3235_);
lean_closure_set(v___f_3250_, 1, v_toBind_3236_);
lean_closure_set(v___f_3250_, 2, v___f_3249_);
lean_inc_ref(v___f_3250_);
v___f_3251_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3251_, 0, v___f_3250_);
v___x_3259_ = lean_expr_eqv(v_type_3247_, v_type_3244_);
if (v___x_3259_ == 0)
{
lean_inc_ref(v_type_3244_);
lean_dec_ref(v_newHyp_3243_);
lean_dec(v___x_3233_);
lean_dec(v_snd_3232_);
goto v___jp_3252_;
}
else
{
if (v___x_3246_ == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
lean_dec_ref(v___f_3251_);
lean_dec_ref(v___f_3250_);
lean_dec(v_inst_3241_);
lean_dec_ref(v_inst_3240_);
lean_dec_ref(v_inst_3239_);
lean_dec(v_inst_3238_);
lean_dec_ref(v_inst_3237_);
lean_dec(v_toBind_3236_);
lean_dec_ref(v___x_3231_);
v___x_3260_ = lean_box(0);
v___x_3261_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(v_snd_3232_, v_newHyp_3243_, v___x_3233_, v_toPure_3234_, v___x_3260_);
return v___x_3261_;
}
else
{
lean_inc_ref(v_type_3244_);
lean_dec_ref(v_newHyp_3243_);
lean_dec(v___x_3233_);
lean_dec(v_snd_3232_);
goto v___jp_3252_;
}
}
v___jp_3252_:
{
lean_object* v_getInheritedTraceOptions_3253_; lean_object* v___x_3254_; lean_object* v___f_3255_; lean_object* v___f_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v_getInheritedTraceOptions_3253_ = lean_ctor_get(v_inst_3237_, 2);
lean_inc(v_getInheritedTraceOptions_3253_);
v___x_3254_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
lean_inc_n(v_toBind_3236_, 3);
v___f_3255_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3255_, 0, v_toPure_3234_);
lean_closure_set(v___f_3255_, 1, v___x_3254_);
lean_closure_set(v___f_3255_, 2, v_toBind_3236_);
lean_closure_set(v___f_3255_, 3, v_inst_3238_);
v___f_3256_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7___boxed), 11, 10);
lean_closure_set(v___f_3256_, 0, v___f_3250_);
lean_closure_set(v___f_3256_, 1, v_inst_3239_);
lean_closure_set(v___f_3256_, 2, v___x_3231_);
lean_closure_set(v___f_3256_, 3, v_type_3244_);
lean_closure_set(v___f_3256_, 4, v_inst_3240_);
lean_closure_set(v___f_3256_, 5, v_inst_3237_);
lean_closure_set(v___f_3256_, 6, v_inst_3241_);
lean_closure_set(v___f_3256_, 7, v___x_3254_);
lean_closure_set(v___f_3256_, 8, v_toBind_3236_);
lean_closure_set(v___f_3256_, 9, v___f_3251_);
v___x_3257_ = lean_apply_4(v_toBind_3236_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3253_, v___f_3255_);
v___x_3258_ = lean_apply_4(v_toBind_3236_, lean_box(0), lean_box(0), v___x_3257_, v___f_3256_);
return v___x_3258_;
}
}
else
{
lean_object* v___x_3262_; lean_object* v___f_3263_; lean_object* v___f_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
lean_inc_ref(v_value_3245_);
lean_dec_ref(v_newHyp_3243_);
lean_dec(v_inst_3241_);
lean_dec_ref(v_inst_3240_);
lean_dec_ref(v_inst_3239_);
lean_dec(v_inst_3238_);
lean_dec_ref(v_inst_3237_);
lean_dec(v___x_3233_);
lean_dec_ref(v___x_3231_);
v___x_3262_ = lean_box(v___x_3246_);
v___f_3263_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 4, 3);
lean_closure_set(v___f_3263_, 0, v___x_3262_);
lean_closure_set(v___f_3263_, 1, v_snd_3232_);
lean_closure_set(v___f_3263_, 2, v_toPure_3234_);
lean_inc(v_toBind_3236_);
v___f_3264_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10), 5, 4);
lean_closure_set(v___f_3264_, 0, v_inst_3242_);
lean_closure_set(v___f_3264_, 1, v_value_3245_);
lean_closure_set(v___f_3264_, 2, v_toBind_3236_);
lean_closure_set(v___f_3264_, 3, v___f_3263_);
v___x_3265_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal___boxed), 9, 0);
v___x_3266_ = lean_apply_2(v_inst_3235_, lean_box(0), v___x_3265_);
v___x_3267_ = lean_apply_4(v_toBind_3236_, lean_box(0), lean_box(0), v___x_3266_, v___f_3264_);
return v___x_3267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12(lean_object* v___x_3268_, lean_object* v_toPure_3269_, lean_object* v_hyps_3270_, lean_object* v___x_3271_, lean_object* v_inst_3272_, lean_object* v_toBind_3273_, lean_object* v_inst_3274_, lean_object* v_inst_3275_, lean_object* v_inst_3276_, lean_object* v_inst_3277_, lean_object* v_inst_3278_, lean_object* v_inst_3279_, lean_object* v_f_3280_, lean_object* v___f_3281_, lean_object* v_next_3282_, lean_object* v_acc_3283_, lean_object* v_h_3284_, lean_object* v_G_3285_){
_start:
{
uint8_t v___x_3286_; 
v___x_3286_ = lean_nat_dec_lt(v_next_3282_, v___x_3268_);
if (v___x_3286_ == 0)
{
lean_object* v___x_3287_; 
lean_dec(v_G_3285_);
lean_dec(v_next_3282_);
lean_dec(v___f_3281_);
lean_dec(v_f_3280_);
lean_dec_ref(v_inst_3279_);
lean_dec(v_inst_3278_);
lean_dec_ref(v_inst_3277_);
lean_dec_ref(v_inst_3276_);
lean_dec(v_inst_3275_);
lean_dec_ref(v_inst_3274_);
lean_dec(v_toBind_3273_);
lean_dec(v_inst_3272_);
lean_dec(v___x_3271_);
v___x_3287_ = lean_apply_2(v_toPure_3269_, lean_box(0), v_acc_3283_);
return v___x_3287_;
}
else
{
lean_object* v_snd_3288_; lean_object* v___f_3289_; lean_object* v___x_3290_; lean_object* v___f_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v_snd_3288_ = lean_ctor_get(v_acc_3283_, 1);
lean_inc(v_snd_3288_);
lean_dec_ref(v_acc_3283_);
lean_inc(v_next_3282_);
lean_inc(v_toPure_3269_);
v___f_3289_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3289_, 0, v_toPure_3269_);
lean_closure_set(v___f_3289_, 1, v_next_3282_);
lean_closure_set(v___f_3289_, 2, v_G_3285_);
v___x_3290_ = lean_array_fget_borrowed(v_hyps_3270_, v_next_3282_);
lean_inc_n(v_toBind_3273_, 3);
lean_inc_n(v___x_3290_, 2);
v___f_3291_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11), 13, 12);
lean_closure_set(v___f_3291_, 0, v___x_3290_);
lean_closure_set(v___f_3291_, 1, v_snd_3288_);
lean_closure_set(v___f_3291_, 2, v___x_3271_);
lean_closure_set(v___f_3291_, 3, v_toPure_3269_);
lean_closure_set(v___f_3291_, 4, v_inst_3272_);
lean_closure_set(v___f_3291_, 5, v_toBind_3273_);
lean_closure_set(v___f_3291_, 6, v_inst_3274_);
lean_closure_set(v___f_3291_, 7, v_inst_3275_);
lean_closure_set(v___f_3291_, 8, v_inst_3276_);
lean_closure_set(v___f_3291_, 9, v_inst_3277_);
lean_closure_set(v___f_3291_, 10, v_inst_3278_);
lean_closure_set(v___f_3291_, 11, v_inst_3279_);
v___x_3292_ = lean_apply_2(v_f_3280_, v_next_3282_, v___x_3290_);
v___x_3293_ = lean_apply_4(v_toBind_3273_, lean_box(0), lean_box(0), v___x_3292_, v___f_3291_);
v___x_3294_ = lean_apply_4(v_toBind_3273_, lean_box(0), lean_box(0), v___x_3293_, v___f_3281_);
v___x_3295_ = lean_apply_4(v_toBind_3273_, lean_box(0), lean_box(0), v___x_3294_, v___f_3289_);
return v___x_3295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12___boxed(lean_object** _args){
lean_object* v___x_3296_ = _args[0];
lean_object* v_toPure_3297_ = _args[1];
lean_object* v_hyps_3298_ = _args[2];
lean_object* v___x_3299_ = _args[3];
lean_object* v_inst_3300_ = _args[4];
lean_object* v_toBind_3301_ = _args[5];
lean_object* v_inst_3302_ = _args[6];
lean_object* v_inst_3303_ = _args[7];
lean_object* v_inst_3304_ = _args[8];
lean_object* v_inst_3305_ = _args[9];
lean_object* v_inst_3306_ = _args[10];
lean_object* v_inst_3307_ = _args[11];
lean_object* v_f_3308_ = _args[12];
lean_object* v___f_3309_ = _args[13];
lean_object* v_next_3310_ = _args[14];
lean_object* v_acc_3311_ = _args[15];
lean_object* v_h_3312_ = _args[16];
lean_object* v_G_3313_ = _args[17];
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12(v___x_3296_, v_toPure_3297_, v_hyps_3298_, v___x_3299_, v_inst_3300_, v_toBind_3301_, v_inst_3302_, v_inst_3303_, v_inst_3304_, v_inst_3305_, v_inst_3306_, v_inst_3307_, v_f_3308_, v___f_3309_, v_next_3310_, v_acc_3311_, v_h_3312_, v_G_3313_);
lean_dec_ref(v_hyps_3298_);
lean_dec(v___x_3296_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__13(lean_object* v_toPure_3315_, lean_object* v_inst_3316_, lean_object* v_toBind_3317_, lean_object* v_inst_3318_, lean_object* v_inst_3319_, lean_object* v_inst_3320_, lean_object* v_inst_3321_, lean_object* v_inst_3322_, lean_object* v_inst_3323_, lean_object* v_f_3324_, lean_object* v___f_3325_, lean_object* v___f_3326_, lean_object* v_hyps_3327_){
_start:
{
lean_object* v___x_3328_; lean_object* v_newHyps_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___f_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3328_ = lean_array_get_size(v_hyps_3327_);
v_newHyps_3329_ = lean_mk_empty_array_with_capacity(v___x_3328_);
v___x_3330_ = lean_unsigned_to_nat(0u);
v___x_3331_ = lean_box(0);
lean_inc(v_toBind_3317_);
v___f_3332_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12___boxed), 18, 14);
lean_closure_set(v___f_3332_, 0, v___x_3328_);
lean_closure_set(v___f_3332_, 1, v_toPure_3315_);
lean_closure_set(v___f_3332_, 2, v_hyps_3327_);
lean_closure_set(v___f_3332_, 3, v___x_3331_);
lean_closure_set(v___f_3332_, 4, v_inst_3316_);
lean_closure_set(v___f_3332_, 5, v_toBind_3317_);
lean_closure_set(v___f_3332_, 6, v_inst_3318_);
lean_closure_set(v___f_3332_, 7, v_inst_3319_);
lean_closure_set(v___f_3332_, 8, v_inst_3320_);
lean_closure_set(v___f_3332_, 9, v_inst_3321_);
lean_closure_set(v___f_3332_, 10, v_inst_3322_);
lean_closure_set(v___f_3332_, 11, v_inst_3323_);
lean_closure_set(v___f_3332_, 12, v_f_3324_);
lean_closure_set(v___f_3332_, 13, v___f_3325_);
v___x_3333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3331_);
lean_ctor_set(v___x_3333_, 1, v_newHyps_3329_);
v___x_3334_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3332_, v___x_3330_, v___x_3333_, lean_box(0));
v___x_3335_ = lean_apply_4(v_toBind_3317_, lean_box(0), lean_box(0), v___x_3334_, v___f_3326_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg(lean_object* v_inst_3336_, lean_object* v_inst_3337_, lean_object* v_inst_3338_, lean_object* v_inst_3339_, lean_object* v_inst_3340_, lean_object* v_inst_3341_, lean_object* v_inst_3342_, lean_object* v_f_3343_){
_start:
{
lean_object* v_toApplicative_3344_; lean_object* v_toBind_3345_; lean_object* v_toPure_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___f_3349_; lean_object* v___f_3350_; lean_object* v___f_3351_; lean_object* v___f_3352_; lean_object* v___x_3353_; 
v_toApplicative_3344_ = lean_ctor_get(v_inst_3336_, 0);
v_toBind_3345_ = lean_ctor_get(v_inst_3336_, 1);
lean_inc_n(v_toBind_3345_, 3);
v_toPure_3346_ = lean_ctor_get(v_toApplicative_3344_, 1);
lean_inc_n(v_toPure_3346_, 4);
v___x_3347_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 9, 0);
lean_inc_n(v_inst_3337_, 2);
v___x_3348_ = lean_apply_2(v_inst_3337_, lean_box(0), v___x_3347_);
v___f_3349_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3349_, 0, v_toPure_3346_);
v___f_3350_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3350_, 0, v_toPure_3346_);
v___f_3351_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3351_, 0, v_inst_3337_);
lean_closure_set(v___f_3351_, 1, v_toBind_3345_);
lean_closure_set(v___f_3351_, 2, v___f_3350_);
lean_closure_set(v___f_3351_, 3, v_toPure_3346_);
v___f_3352_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__13), 13, 12);
lean_closure_set(v___f_3352_, 0, v_toPure_3346_);
lean_closure_set(v___f_3352_, 1, v_inst_3337_);
lean_closure_set(v___f_3352_, 2, v_toBind_3345_);
lean_closure_set(v___f_3352_, 3, v_inst_3340_);
lean_closure_set(v___f_3352_, 4, v_inst_3341_);
lean_closure_set(v___f_3352_, 5, v_inst_3338_);
lean_closure_set(v___f_3352_, 6, v_inst_3336_);
lean_closure_set(v___f_3352_, 7, v_inst_3342_);
lean_closure_set(v___f_3352_, 8, v_inst_3339_);
lean_closure_set(v___f_3352_, 9, v_f_3343_);
lean_closure_set(v___f_3352_, 10, v___f_3349_);
lean_closure_set(v___f_3352_, 11, v___f_3351_);
v___x_3353_ = lean_apply_4(v_toBind_3345_, lean_box(0), lean_box(0), v___x_3348_, v___f_3352_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(lean_object* v_m_3354_, lean_object* v_inst_3355_, lean_object* v_inst_3356_, lean_object* v_inst_3357_, lean_object* v_inst_3358_, lean_object* v_inst_3359_, lean_object* v_inst_3360_, lean_object* v_inst_3361_, lean_object* v_inst_3362_, lean_object* v_f_3363_){
_start:
{
lean_object* v_toApplicative_3364_; lean_object* v_toBind_3365_; lean_object* v_toPure_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___f_3369_; lean_object* v___f_3370_; lean_object* v___f_3371_; lean_object* v___f_3372_; lean_object* v___x_3373_; 
v_toApplicative_3364_ = lean_ctor_get(v_inst_3355_, 0);
v_toBind_3365_ = lean_ctor_get(v_inst_3355_, 1);
lean_inc_n(v_toBind_3365_, 3);
v_toPure_3366_ = lean_ctor_get(v_toApplicative_3364_, 1);
lean_inc_n(v_toPure_3366_, 4);
v___x_3367_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 9, 0);
lean_inc_n(v_inst_3356_, 2);
v___x_3368_ = lean_apply_2(v_inst_3356_, lean_box(0), v___x_3367_);
v___f_3369_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3369_, 0, v_toPure_3366_);
v___f_3370_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3370_, 0, v_toPure_3366_);
v___f_3371_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3371_, 0, v_inst_3356_);
lean_closure_set(v___f_3371_, 1, v_toBind_3365_);
lean_closure_set(v___f_3371_, 2, v___f_3370_);
lean_closure_set(v___f_3371_, 3, v_toPure_3366_);
v___f_3372_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__13), 13, 12);
lean_closure_set(v___f_3372_, 0, v_toPure_3366_);
lean_closure_set(v___f_3372_, 1, v_inst_3356_);
lean_closure_set(v___f_3372_, 2, v_toBind_3365_);
lean_closure_set(v___f_3372_, 3, v_inst_3359_);
lean_closure_set(v___f_3372_, 4, v_inst_3360_);
lean_closure_set(v___f_3372_, 5, v_inst_3357_);
lean_closure_set(v___f_3372_, 6, v_inst_3355_);
lean_closure_set(v___f_3372_, 7, v_inst_3361_);
lean_closure_set(v___f_3372_, 8, v_inst_3358_);
lean_closure_set(v___f_3372_, 9, v_f_3363_);
lean_closure_set(v___f_3372_, 10, v___f_3369_);
lean_closure_set(v___f_3372_, 11, v___f_3371_);
v___x_3373_ = lean_apply_4(v_toBind_3365_, lean_box(0), lean_box(0), v___x_3368_, v___f_3372_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___boxed(lean_object* v_m_3374_, lean_object* v_inst_3375_, lean_object* v_inst_3376_, lean_object* v_inst_3377_, lean_object* v_inst_3378_, lean_object* v_inst_3379_, lean_object* v_inst_3380_, lean_object* v_inst_3381_, lean_object* v_inst_3382_, lean_object* v_f_3383_){
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(v_m_3374_, v_inst_3375_, v_inst_3376_, v_inst_3377_, v_inst_3378_, v_inst_3379_, v_inst_3380_, v_inst_3381_, v_inst_3382_, v_f_3383_);
lean_dec_ref(v_inst_3382_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__14(lean_object* v___x_3385_, lean_object* v_snd_3386_, lean_object* v___x_3387_, lean_object* v_toPure_3388_, lean_object* v_inst_3389_, lean_object* v_toBind_3390_, lean_object* v_inst_3391_, lean_object* v_inst_3392_, lean_object* v_inst_3393_, lean_object* v_inst_3394_, lean_object* v_inst_3395_, lean_object* v_inst_3396_, lean_object* v_newHyp_3397_){
_start:
{
lean_object* v_type_3398_; lean_object* v_value_3399_; uint8_t v___x_3400_; 
v_type_3398_ = lean_ctor_get(v_newHyp_3397_, 1);
v_value_3399_ = lean_ctor_get(v_newHyp_3397_, 2);
lean_inc_ref(v_type_3398_);
v___x_3400_ = l_Lean_Expr_isFalse(v_type_3398_);
if (v___x_3400_ == 0)
{
lean_object* v_type_3401_; lean_object* v___f_3402_; lean_object* v___f_3403_; lean_object* v___f_3404_; lean_object* v___f_3405_; uint8_t v___x_3413_; 
lean_dec_ref(v_inst_3396_);
v_type_3401_ = lean_ctor_get(v___x_3385_, 1);
lean_inc(v_toPure_3388_);
lean_inc(v___x_3387_);
lean_inc_ref(v_newHyp_3397_);
lean_inc(v_snd_3386_);
v___f_3402_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5), 5, 4);
lean_closure_set(v___f_3402_, 0, v_snd_3386_);
lean_closure_set(v___f_3402_, 1, v_newHyp_3397_);
lean_closure_set(v___f_3402_, 2, v___x_3387_);
lean_closure_set(v___f_3402_, 3, v_toPure_3388_);
v___f_3403_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3403_, 0, v___f_3402_);
lean_inc(v_toBind_3390_);
v___f_3404_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3404_, 0, v_inst_3389_);
lean_closure_set(v___f_3404_, 1, v_toBind_3390_);
lean_closure_set(v___f_3404_, 2, v___f_3403_);
lean_inc_ref(v___f_3404_);
v___f_3405_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3405_, 0, v___f_3404_);
v___x_3413_ = lean_expr_eqv(v_type_3401_, v_type_3398_);
if (v___x_3413_ == 0)
{
lean_inc_ref(v_type_3398_);
lean_dec_ref(v_newHyp_3397_);
lean_dec(v___x_3387_);
lean_dec(v_snd_3386_);
goto v___jp_3406_;
}
else
{
if (v___x_3400_ == 0)
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
lean_dec_ref(v___f_3405_);
lean_dec_ref(v___f_3404_);
lean_dec(v_inst_3395_);
lean_dec(v_inst_3394_);
lean_dec_ref(v_inst_3393_);
lean_dec_ref(v_inst_3392_);
lean_dec_ref(v_inst_3391_);
lean_dec(v_toBind_3390_);
lean_dec_ref(v___x_3385_);
v___x_3414_ = lean_box(0);
v___x_3415_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(v_snd_3386_, v_newHyp_3397_, v___x_3387_, v_toPure_3388_, v___x_3414_);
return v___x_3415_;
}
else
{
lean_inc_ref(v_type_3398_);
lean_dec_ref(v_newHyp_3397_);
lean_dec(v___x_3387_);
lean_dec(v_snd_3386_);
goto v___jp_3406_;
}
}
v___jp_3406_:
{
lean_object* v_getInheritedTraceOptions_3407_; lean_object* v___x_3408_; lean_object* v___f_3409_; lean_object* v___f_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v_getInheritedTraceOptions_3407_ = lean_ctor_get(v_inst_3391_, 2);
lean_inc(v_getInheritedTraceOptions_3407_);
v___x_3408_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
lean_inc_n(v_toBind_3390_, 3);
v___f_3409_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7___boxed), 11, 10);
lean_closure_set(v___f_3409_, 0, v___f_3404_);
lean_closure_set(v___f_3409_, 1, v_inst_3392_);
lean_closure_set(v___f_3409_, 2, v___x_3385_);
lean_closure_set(v___f_3409_, 3, v_type_3398_);
lean_closure_set(v___f_3409_, 4, v_inst_3393_);
lean_closure_set(v___f_3409_, 5, v_inst_3391_);
lean_closure_set(v___f_3409_, 6, v_inst_3394_);
lean_closure_set(v___f_3409_, 7, v___x_3408_);
lean_closure_set(v___f_3409_, 8, v_toBind_3390_);
lean_closure_set(v___f_3409_, 9, v___f_3405_);
v___f_3410_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3410_, 0, v_toPure_3388_);
lean_closure_set(v___f_3410_, 1, v___x_3408_);
lean_closure_set(v___f_3410_, 2, v_toBind_3390_);
lean_closure_set(v___f_3410_, 3, v_inst_3395_);
v___x_3411_ = lean_apply_4(v_toBind_3390_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3407_, v___f_3410_);
v___x_3412_ = lean_apply_4(v_toBind_3390_, lean_box(0), lean_box(0), v___x_3411_, v___f_3409_);
return v___x_3412_;
}
}
else
{
lean_object* v___x_3416_; lean_object* v___f_3417_; lean_object* v___f_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
lean_inc_ref(v_value_3399_);
lean_dec_ref(v_newHyp_3397_);
lean_dec(v_inst_3395_);
lean_dec(v_inst_3394_);
lean_dec_ref(v_inst_3393_);
lean_dec_ref(v_inst_3392_);
lean_dec_ref(v_inst_3391_);
lean_dec(v___x_3387_);
lean_dec_ref(v___x_3385_);
v___x_3416_ = lean_box(v___x_3400_);
v___f_3417_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 4, 3);
lean_closure_set(v___f_3417_, 0, v___x_3416_);
lean_closure_set(v___f_3417_, 1, v_snd_3386_);
lean_closure_set(v___f_3417_, 2, v_toPure_3388_);
lean_inc(v_toBind_3390_);
v___f_3418_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10), 5, 4);
lean_closure_set(v___f_3418_, 0, v_inst_3396_);
lean_closure_set(v___f_3418_, 1, v_value_3399_);
lean_closure_set(v___f_3418_, 2, v_toBind_3390_);
lean_closure_set(v___f_3418_, 3, v___f_3417_);
v___x_3419_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal___boxed), 9, 0);
v___x_3420_ = lean_apply_2(v_inst_3389_, lean_box(0), v___x_3419_);
v___x_3421_ = lean_apply_4(v_toBind_3390_, lean_box(0), lean_box(0), v___x_3420_, v___f_3418_);
return v___x_3421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(lean_object* v___x_3422_, lean_object* v_toPure_3423_, lean_object* v_hyps_3424_, lean_object* v___x_3425_, lean_object* v_inst_3426_, lean_object* v_toBind_3427_, lean_object* v_inst_3428_, lean_object* v_inst_3429_, lean_object* v_inst_3430_, lean_object* v_inst_3431_, lean_object* v_inst_3432_, lean_object* v_inst_3433_, lean_object* v_f_3434_, lean_object* v___f_3435_, lean_object* v_next_3436_, lean_object* v_acc_3437_, lean_object* v_h_3438_, lean_object* v_G_3439_){
_start:
{
uint8_t v___x_3440_; 
v___x_3440_ = lean_nat_dec_lt(v_next_3436_, v___x_3422_);
if (v___x_3440_ == 0)
{
lean_object* v___x_3441_; 
lean_dec(v_G_3439_);
lean_dec(v_next_3436_);
lean_dec(v___f_3435_);
lean_dec(v_f_3434_);
lean_dec_ref(v_inst_3433_);
lean_dec(v_inst_3432_);
lean_dec(v_inst_3431_);
lean_dec_ref(v_inst_3430_);
lean_dec_ref(v_inst_3429_);
lean_dec_ref(v_inst_3428_);
lean_dec(v_toBind_3427_);
lean_dec(v_inst_3426_);
lean_dec(v___x_3425_);
v___x_3441_ = lean_apply_2(v_toPure_3423_, lean_box(0), v_acc_3437_);
return v___x_3441_;
}
else
{
lean_object* v_snd_3442_; lean_object* v___f_3443_; lean_object* v___x_3444_; lean_object* v___f_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v_snd_3442_ = lean_ctor_get(v_acc_3437_, 1);
lean_inc(v_snd_3442_);
lean_dec_ref(v_acc_3437_);
lean_inc(v_next_3436_);
lean_inc(v_toPure_3423_);
v___f_3443_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3443_, 0, v_toPure_3423_);
lean_closure_set(v___f_3443_, 1, v_next_3436_);
lean_closure_set(v___f_3443_, 2, v_G_3439_);
v___x_3444_ = lean_array_fget_borrowed(v_hyps_3424_, v_next_3436_);
lean_dec(v_next_3436_);
lean_inc_n(v_toBind_3427_, 3);
lean_inc_n(v___x_3444_, 2);
v___f_3445_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__14), 13, 12);
lean_closure_set(v___f_3445_, 0, v___x_3444_);
lean_closure_set(v___f_3445_, 1, v_snd_3442_);
lean_closure_set(v___f_3445_, 2, v___x_3425_);
lean_closure_set(v___f_3445_, 3, v_toPure_3423_);
lean_closure_set(v___f_3445_, 4, v_inst_3426_);
lean_closure_set(v___f_3445_, 5, v_toBind_3427_);
lean_closure_set(v___f_3445_, 6, v_inst_3428_);
lean_closure_set(v___f_3445_, 7, v_inst_3429_);
lean_closure_set(v___f_3445_, 8, v_inst_3430_);
lean_closure_set(v___f_3445_, 9, v_inst_3431_);
lean_closure_set(v___f_3445_, 10, v_inst_3432_);
lean_closure_set(v___f_3445_, 11, v_inst_3433_);
v___x_3446_ = lean_apply_1(v_f_3434_, v___x_3444_);
v___x_3447_ = lean_apply_4(v_toBind_3427_, lean_box(0), lean_box(0), v___x_3446_, v___f_3445_);
v___x_3448_ = lean_apply_4(v_toBind_3427_, lean_box(0), lean_box(0), v___x_3447_, v___f_3435_);
v___x_3449_ = lean_apply_4(v_toBind_3427_, lean_box(0), lean_box(0), v___x_3448_, v___f_3443_);
return v___x_3449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3450_ = _args[0];
lean_object* v_toPure_3451_ = _args[1];
lean_object* v_hyps_3452_ = _args[2];
lean_object* v___x_3453_ = _args[3];
lean_object* v_inst_3454_ = _args[4];
lean_object* v_toBind_3455_ = _args[5];
lean_object* v_inst_3456_ = _args[6];
lean_object* v_inst_3457_ = _args[7];
lean_object* v_inst_3458_ = _args[8];
lean_object* v_inst_3459_ = _args[9];
lean_object* v_inst_3460_ = _args[10];
lean_object* v_inst_3461_ = _args[11];
lean_object* v_f_3462_ = _args[12];
lean_object* v___f_3463_ = _args[13];
lean_object* v_next_3464_ = _args[14];
lean_object* v_acc_3465_ = _args[15];
lean_object* v_h_3466_ = _args[16];
lean_object* v_G_3467_ = _args[17];
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(v___x_3450_, v_toPure_3451_, v_hyps_3452_, v___x_3453_, v_inst_3454_, v_toBind_3455_, v_inst_3456_, v_inst_3457_, v_inst_3458_, v_inst_3459_, v_inst_3460_, v_inst_3461_, v_f_3462_, v___f_3463_, v_next_3464_, v_acc_3465_, v_h_3466_, v_G_3467_);
lean_dec_ref(v_hyps_3452_);
lean_dec(v___x_3450_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1(lean_object* v_toPure_3469_, lean_object* v_inst_3470_, lean_object* v_toBind_3471_, lean_object* v_inst_3472_, lean_object* v_inst_3473_, lean_object* v_inst_3474_, lean_object* v_inst_3475_, lean_object* v_inst_3476_, lean_object* v_inst_3477_, lean_object* v_f_3478_, lean_object* v___f_3479_, lean_object* v___f_3480_, lean_object* v_hyps_3481_){
_start:
{
lean_object* v___x_3482_; lean_object* v_newHyps_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___f_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3482_ = lean_array_get_size(v_hyps_3481_);
v_newHyps_3483_ = lean_mk_empty_array_with_capacity(v___x_3482_);
v___x_3484_ = lean_unsigned_to_nat(0u);
v___x_3485_ = lean_box(0);
lean_inc(v_toBind_3471_);
v___f_3486_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed), 18, 14);
lean_closure_set(v___f_3486_, 0, v___x_3482_);
lean_closure_set(v___f_3486_, 1, v_toPure_3469_);
lean_closure_set(v___f_3486_, 2, v_hyps_3481_);
lean_closure_set(v___f_3486_, 3, v___x_3485_);
lean_closure_set(v___f_3486_, 4, v_inst_3470_);
lean_closure_set(v___f_3486_, 5, v_toBind_3471_);
lean_closure_set(v___f_3486_, 6, v_inst_3472_);
lean_closure_set(v___f_3486_, 7, v_inst_3473_);
lean_closure_set(v___f_3486_, 8, v_inst_3474_);
lean_closure_set(v___f_3486_, 9, v_inst_3475_);
lean_closure_set(v___f_3486_, 10, v_inst_3476_);
lean_closure_set(v___f_3486_, 11, v_inst_3477_);
lean_closure_set(v___f_3486_, 12, v_f_3478_);
lean_closure_set(v___f_3486_, 13, v___f_3479_);
v___x_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3485_);
lean_ctor_set(v___x_3487_, 1, v_newHyps_3483_);
v___x_3488_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3486_, v___x_3484_, v___x_3487_, lean_box(0));
v___x_3489_ = lean_apply_4(v_toBind_3471_, lean_box(0), lean_box(0), v___x_3488_, v___f_3480_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg(lean_object* v_inst_3490_, lean_object* v_inst_3491_, lean_object* v_inst_3492_, lean_object* v_inst_3493_, lean_object* v_inst_3494_, lean_object* v_inst_3495_, lean_object* v_inst_3496_, lean_object* v_f_3497_){
_start:
{
lean_object* v_toApplicative_3498_; lean_object* v_toBind_3499_; lean_object* v_toPure_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___f_3503_; lean_object* v___f_3504_; lean_object* v___f_3505_; lean_object* v___f_3506_; lean_object* v___x_3507_; 
v_toApplicative_3498_ = lean_ctor_get(v_inst_3490_, 0);
v_toBind_3499_ = lean_ctor_get(v_inst_3490_, 1);
lean_inc_n(v_toBind_3499_, 3);
v_toPure_3500_ = lean_ctor_get(v_toApplicative_3498_, 1);
lean_inc_n(v_toPure_3500_, 4);
v___x_3501_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 9, 0);
lean_inc_n(v_inst_3491_, 2);
v___x_3502_ = lean_apply_2(v_inst_3491_, lean_box(0), v___x_3501_);
v___f_3503_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3503_, 0, v_toPure_3500_);
v___f_3504_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3504_, 0, v_inst_3491_);
lean_closure_set(v___f_3504_, 1, v_toBind_3499_);
lean_closure_set(v___f_3504_, 2, v___f_3503_);
lean_closure_set(v___f_3504_, 3, v_toPure_3500_);
v___f_3505_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3505_, 0, v_toPure_3500_);
v___f_3506_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 13, 12);
lean_closure_set(v___f_3506_, 0, v_toPure_3500_);
lean_closure_set(v___f_3506_, 1, v_inst_3491_);
lean_closure_set(v___f_3506_, 2, v_toBind_3499_);
lean_closure_set(v___f_3506_, 3, v_inst_3494_);
lean_closure_set(v___f_3506_, 4, v_inst_3492_);
lean_closure_set(v___f_3506_, 5, v_inst_3490_);
lean_closure_set(v___f_3506_, 6, v_inst_3496_);
lean_closure_set(v___f_3506_, 7, v_inst_3495_);
lean_closure_set(v___f_3506_, 8, v_inst_3493_);
lean_closure_set(v___f_3506_, 9, v_f_3497_);
lean_closure_set(v___f_3506_, 10, v___f_3505_);
lean_closure_set(v___f_3506_, 11, v___f_3504_);
v___x_3507_ = lean_apply_4(v_toBind_3499_, lean_box(0), lean_box(0), v___x_3502_, v___f_3506_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(lean_object* v_m_3508_, lean_object* v_inst_3509_, lean_object* v_inst_3510_, lean_object* v_inst_3511_, lean_object* v_inst_3512_, lean_object* v_inst_3513_, lean_object* v_inst_3514_, lean_object* v_inst_3515_, lean_object* v_inst_3516_, lean_object* v_f_3517_){
_start:
{
lean_object* v_toApplicative_3518_; lean_object* v_toBind_3519_; lean_object* v_toPure_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___f_3523_; lean_object* v___f_3524_; lean_object* v___f_3525_; lean_object* v___f_3526_; lean_object* v___x_3527_; 
v_toApplicative_3518_ = lean_ctor_get(v_inst_3509_, 0);
v_toBind_3519_ = lean_ctor_get(v_inst_3509_, 1);
lean_inc_n(v_toBind_3519_, 3);
v_toPure_3520_ = lean_ctor_get(v_toApplicative_3518_, 1);
lean_inc_n(v_toPure_3520_, 4);
v___x_3521_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 9, 0);
lean_inc_n(v_inst_3510_, 2);
v___x_3522_ = lean_apply_2(v_inst_3510_, lean_box(0), v___x_3521_);
v___f_3523_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3523_, 0, v_toPure_3520_);
v___f_3524_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3524_, 0, v_inst_3510_);
lean_closure_set(v___f_3524_, 1, v_toBind_3519_);
lean_closure_set(v___f_3524_, 2, v___f_3523_);
lean_closure_set(v___f_3524_, 3, v_toPure_3520_);
v___f_3525_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3525_, 0, v_toPure_3520_);
v___f_3526_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 13, 12);
lean_closure_set(v___f_3526_, 0, v_toPure_3520_);
lean_closure_set(v___f_3526_, 1, v_inst_3510_);
lean_closure_set(v___f_3526_, 2, v_toBind_3519_);
lean_closure_set(v___f_3526_, 3, v_inst_3513_);
lean_closure_set(v___f_3526_, 4, v_inst_3511_);
lean_closure_set(v___f_3526_, 5, v_inst_3509_);
lean_closure_set(v___f_3526_, 6, v_inst_3515_);
lean_closure_set(v___f_3526_, 7, v_inst_3514_);
lean_closure_set(v___f_3526_, 8, v_inst_3512_);
lean_closure_set(v___f_3526_, 9, v_f_3517_);
lean_closure_set(v___f_3526_, 10, v___f_3525_);
lean_closure_set(v___f_3526_, 11, v___f_3524_);
v___x_3527_ = lean_apply_4(v_toBind_3519_, lean_box(0), lean_box(0), v___x_3522_, v___f_3526_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___boxed(lean_object* v_m_3528_, lean_object* v_inst_3529_, lean_object* v_inst_3530_, lean_object* v_inst_3531_, lean_object* v_inst_3532_, lean_object* v_inst_3533_, lean_object* v_inst_3534_, lean_object* v_inst_3535_, lean_object* v_inst_3536_, lean_object* v_f_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(v_m_3528_, v_inst_3529_, v_inst_3530_, v_inst_3531_, v_inst_3532_, v_inst_3533_, v_inst_3534_, v_inst_3535_, v_inst_3536_, v_f_3537_);
lean_dec_ref(v_inst_3536_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0(lean_object* v_f_3539_, lean_object* v_x_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v___x_3542_; 
v___x_3542_ = lean_apply_1(v_f_3539_, v___y_3541_);
return v___x_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1(lean_object* v_toApplicative_3543_, lean_object* v_inst_3544_, lean_object* v___f_3545_, lean_object* v_hyps_3546_){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; uint8_t v___x_3550_; 
v___x_3547_ = lean_unsigned_to_nat(0u);
v___x_3548_ = lean_array_get_size(v_hyps_3546_);
v___x_3549_ = lean_box(0);
v___x_3550_ = lean_nat_dec_lt(v___x_3547_, v___x_3548_);
if (v___x_3550_ == 0)
{
lean_object* v_toPure_3551_; lean_object* v___x_3552_; 
lean_dec_ref(v_hyps_3546_);
lean_dec(v___f_3545_);
lean_dec_ref(v_inst_3544_);
v_toPure_3551_ = lean_ctor_get(v_toApplicative_3543_, 1);
lean_inc(v_toPure_3551_);
lean_dec_ref(v_toApplicative_3543_);
v___x_3552_ = lean_apply_2(v_toPure_3551_, lean_box(0), v___x_3549_);
return v___x_3552_;
}
else
{
uint8_t v___x_3553_; 
v___x_3553_ = lean_nat_dec_le(v___x_3548_, v___x_3548_);
if (v___x_3553_ == 0)
{
if (v___x_3550_ == 0)
{
lean_object* v_toPure_3554_; lean_object* v___x_3555_; 
lean_dec_ref(v_hyps_3546_);
lean_dec(v___f_3545_);
lean_dec_ref(v_inst_3544_);
v_toPure_3554_ = lean_ctor_get(v_toApplicative_3543_, 1);
lean_inc(v_toPure_3554_);
lean_dec_ref(v_toApplicative_3543_);
v___x_3555_ = lean_apply_2(v_toPure_3554_, lean_box(0), v___x_3549_);
return v___x_3555_;
}
else
{
size_t v___x_3556_; size_t v___x_3557_; lean_object* v___x_3558_; 
lean_dec_ref(v_toApplicative_3543_);
v___x_3556_ = ((size_t)0ULL);
v___x_3557_ = lean_usize_of_nat(v___x_3548_);
v___x_3558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3544_, v___f_3545_, v_hyps_3546_, v___x_3556_, v___x_3557_, v___x_3549_);
return v___x_3558_;
}
}
else
{
size_t v___x_3559_; size_t v___x_3560_; lean_object* v___x_3561_; 
lean_dec_ref(v_toApplicative_3543_);
v___x_3559_ = ((size_t)0ULL);
v___x_3560_ = lean_usize_of_nat(v___x_3548_);
v___x_3561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3544_, v___f_3545_, v_hyps_3546_, v___x_3559_, v___x_3560_, v___x_3549_);
return v___x_3561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg(lean_object* v_inst_3562_, lean_object* v_inst_3563_, lean_object* v_f_3564_){
_start:
{
lean_object* v_toApplicative_3565_; lean_object* v_toBind_3566_; lean_object* v___f_3567_; lean_object* v___f_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v_toApplicative_3565_ = lean_ctor_get(v_inst_3562_, 0);
lean_inc_ref(v_toApplicative_3565_);
v_toBind_3566_ = lean_ctor_get(v_inst_3562_, 1);
lean_inc(v_toBind_3566_);
v___f_3567_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3567_, 0, v_f_3564_);
v___f_3568_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3568_, 0, v_toApplicative_3565_);
lean_closure_set(v___f_3568_, 1, v_inst_3562_);
lean_closure_set(v___f_3568_, 2, v___f_3567_);
v___x_3569_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 9, 0);
v___x_3570_ = lean_apply_2(v_inst_3563_, lean_box(0), v___x_3569_);
v___x_3571_ = lean_apply_4(v_toBind_3566_, lean_box(0), lean_box(0), v___x_3570_, v___f_3568_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(lean_object* v_m_3572_, lean_object* v_inst_3573_, lean_object* v_inst_3574_, lean_object* v_inst_3575_, lean_object* v_f_3576_){
_start:
{
lean_object* v_toApplicative_3577_; lean_object* v_toBind_3578_; lean_object* v___f_3579_; lean_object* v___f_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
v_toApplicative_3577_ = lean_ctor_get(v_inst_3573_, 0);
lean_inc_ref(v_toApplicative_3577_);
v_toBind_3578_ = lean_ctor_get(v_inst_3573_, 1);
lean_inc(v_toBind_3578_);
v___f_3579_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3579_, 0, v_f_3576_);
v___f_3580_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3580_, 0, v_toApplicative_3577_);
lean_closure_set(v___f_3580_, 1, v_inst_3573_);
lean_closure_set(v___f_3580_, 2, v___f_3579_);
v___x_3581_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 9, 0);
v___x_3582_ = lean_apply_2(v_inst_3574_, lean_box(0), v___x_3581_);
v___x_3583_ = lean_apply_4(v_toBind_3578_, lean_box(0), lean_box(0), v___x_3582_, v___f_3580_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___boxed(lean_object* v_m_3584_, lean_object* v_inst_3585_, lean_object* v_inst_3586_, lean_object* v_inst_3587_, lean_object* v_f_3588_){
_start:
{
lean_object* v_res_3589_; 
v_res_3589_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(v_m_3584_, v_inst_3585_, v_inst_3586_, v_inst_3587_, v_f_3588_);
lean_dec_ref(v_inst_3587_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(lean_object* v_msgData_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v___x_3596_; lean_object* v_env_3597_; lean_object* v___x_3598_; lean_object* v_mctx_3599_; lean_object* v_lctx_3600_; lean_object* v_options_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3596_ = lean_st_ref_get(v___y_3594_);
v_env_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc_ref(v_env_3597_);
lean_dec(v___x_3596_);
v___x_3598_ = lean_st_ref_get(v___y_3592_);
v_mctx_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc_ref(v_mctx_3599_);
lean_dec(v___x_3598_);
v_lctx_3600_ = lean_ctor_get(v___y_3591_, 2);
v_options_3601_ = lean_ctor_get(v___y_3593_, 2);
lean_inc_ref(v_options_3601_);
lean_inc_ref(v_lctx_3600_);
v___x_3602_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3602_, 0, v_env_3597_);
lean_ctor_set(v___x_3602_, 1, v_mctx_3599_);
lean_ctor_set(v___x_3602_, 2, v_lctx_3600_);
lean_ctor_set(v___x_3602_, 3, v_options_3601_);
v___x_3603_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
lean_ctor_set(v___x_3603_, 1, v_msgData_3590_);
v___x_3604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3603_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0___boxed(lean_object* v_msgData_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msgData_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
return v_res_3611_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3612_; double v___x_3613_; 
v___x_3612_ = lean_unsigned_to_nat(0u);
v___x_3613_ = lean_float_of_nat(v___x_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(lean_object* v_cls_3617_, lean_object* v_msg_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v_ref_3624_; lean_object* v___x_3625_; lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3670_; 
v_ref_3624_ = lean_ctor_get(v___y_3621_, 5);
v___x_3625_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3628_ = v___x_3625_;
v_isShared_3629_ = v_isSharedCheck_3670_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3625_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3670_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3630_; lean_object* v_traceState_3631_; lean_object* v_env_3632_; lean_object* v_nextMacroScope_3633_; lean_object* v_ngen_3634_; lean_object* v_auxDeclNGen_3635_; lean_object* v_cache_3636_; lean_object* v_messages_3637_; lean_object* v_infoState_3638_; lean_object* v_snapshotTasks_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3669_; 
v___x_3630_ = lean_st_ref_take(v___y_3622_);
v_traceState_3631_ = lean_ctor_get(v___x_3630_, 4);
v_env_3632_ = lean_ctor_get(v___x_3630_, 0);
v_nextMacroScope_3633_ = lean_ctor_get(v___x_3630_, 1);
v_ngen_3634_ = lean_ctor_get(v___x_3630_, 2);
v_auxDeclNGen_3635_ = lean_ctor_get(v___x_3630_, 3);
v_cache_3636_ = lean_ctor_get(v___x_3630_, 5);
v_messages_3637_ = lean_ctor_get(v___x_3630_, 6);
v_infoState_3638_ = lean_ctor_get(v___x_3630_, 7);
v_snapshotTasks_3639_ = lean_ctor_get(v___x_3630_, 8);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3641_ = v___x_3630_;
v_isShared_3642_ = v_isSharedCheck_3669_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_snapshotTasks_3639_);
lean_inc(v_infoState_3638_);
lean_inc(v_messages_3637_);
lean_inc(v_cache_3636_);
lean_inc(v_traceState_3631_);
lean_inc(v_auxDeclNGen_3635_);
lean_inc(v_ngen_3634_);
lean_inc(v_nextMacroScope_3633_);
lean_inc(v_env_3632_);
lean_dec(v___x_3630_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3669_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
uint64_t v_tid_3643_; lean_object* v_traces_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3668_; 
v_tid_3643_ = lean_ctor_get_uint64(v_traceState_3631_, sizeof(void*)*1);
v_traces_3644_ = lean_ctor_get(v_traceState_3631_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v_traceState_3631_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3646_ = v_traceState_3631_;
v_isShared_3647_ = v_isSharedCheck_3668_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_traces_3644_);
lean_dec(v_traceState_3631_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3668_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3648_; double v___x_3649_; uint8_t v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3658_; 
v___x_3648_ = lean_box(0);
v___x_3649_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_3650_ = 0;
v___x_3651_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_3652_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3652_, 0, v_cls_3617_);
lean_ctor_set(v___x_3652_, 1, v___x_3648_);
lean_ctor_set(v___x_3652_, 2, v___x_3651_);
lean_ctor_set_float(v___x_3652_, sizeof(void*)*3, v___x_3649_);
lean_ctor_set_float(v___x_3652_, sizeof(void*)*3 + 8, v___x_3649_);
lean_ctor_set_uint8(v___x_3652_, sizeof(void*)*3 + 16, v___x_3650_);
v___x_3653_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_3654_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3652_);
lean_ctor_set(v___x_3654_, 1, v_a_3626_);
lean_ctor_set(v___x_3654_, 2, v___x_3653_);
lean_inc(v_ref_3624_);
v___x_3655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3655_, 0, v_ref_3624_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
v___x_3656_ = l_Lean_PersistentArray_push___redArg(v_traces_3644_, v___x_3655_);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 0, v___x_3656_);
v___x_3658_ = v___x_3646_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3656_);
lean_ctor_set_uint64(v_reuseFailAlloc_3667_, sizeof(void*)*1, v_tid_3643_);
v___x_3658_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3660_; 
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 4, v___x_3658_);
v___x_3660_ = v___x_3641_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_env_3632_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v_nextMacroScope_3633_);
lean_ctor_set(v_reuseFailAlloc_3666_, 2, v_ngen_3634_);
lean_ctor_set(v_reuseFailAlloc_3666_, 3, v_auxDeclNGen_3635_);
lean_ctor_set(v_reuseFailAlloc_3666_, 4, v___x_3658_);
lean_ctor_set(v_reuseFailAlloc_3666_, 5, v_cache_3636_);
lean_ctor_set(v_reuseFailAlloc_3666_, 6, v_messages_3637_);
lean_ctor_set(v_reuseFailAlloc_3666_, 7, v_infoState_3638_);
lean_ctor_set(v_reuseFailAlloc_3666_, 8, v_snapshotTasks_3639_);
v___x_3660_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3664_; 
v___x_3661_ = lean_st_ref_set(v___y_3622_, v___x_3660_);
v___x_3662_ = lean_box(0);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 0, v___x_3662_);
v___x_3664_ = v___x_3628_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3662_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_3671_, lean_object* v_msg_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_3671_, v_msg_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_3679_, lean_object* v_x_3680_, lean_object* v_x_3681_, lean_object* v_x_3682_){
_start:
{
lean_object* v_ks_3683_; lean_object* v_vs_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3708_; 
v_ks_3683_ = lean_ctor_get(v_x_3679_, 0);
v_vs_3684_ = lean_ctor_get(v_x_3679_, 1);
v_isSharedCheck_3708_ = !lean_is_exclusive(v_x_3679_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3686_ = v_x_3679_;
v_isShared_3687_ = v_isSharedCheck_3708_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_vs_3684_);
lean_inc(v_ks_3683_);
lean_dec(v_x_3679_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3708_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3688_; uint8_t v___x_3689_; 
v___x_3688_ = lean_array_get_size(v_ks_3683_);
v___x_3689_ = lean_nat_dec_lt(v_x_3680_, v___x_3688_);
if (v___x_3689_ == 0)
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3693_; 
lean_dec(v_x_3680_);
v___x_3690_ = lean_array_push(v_ks_3683_, v_x_3681_);
v___x_3691_ = lean_array_push(v_vs_3684_, v_x_3682_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 1, v___x_3691_);
lean_ctor_set(v___x_3686_, 0, v___x_3690_);
v___x_3693_ = v___x_3686_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3690_);
lean_ctor_set(v_reuseFailAlloc_3694_, 1, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
else
{
lean_object* v_k_x27_3695_; uint8_t v___x_3696_; 
v_k_x27_3695_ = lean_array_fget_borrowed(v_ks_3683_, v_x_3680_);
v___x_3696_ = l_Lean_instBEqMVarId_beq(v_x_3681_, v_k_x27_3695_);
if (v___x_3696_ == 0)
{
lean_object* v___x_3698_; 
if (v_isShared_3687_ == 0)
{
v___x_3698_ = v___x_3686_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_ks_3683_);
lean_ctor_set(v_reuseFailAlloc_3702_, 1, v_vs_3684_);
v___x_3698_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3699_ = lean_unsigned_to_nat(1u);
v___x_3700_ = lean_nat_add(v_x_3680_, v___x_3699_);
lean_dec(v_x_3680_);
v_x_3679_ = v___x_3698_;
v_x_3680_ = v___x_3700_;
goto _start;
}
}
else
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3706_; 
v___x_3703_ = lean_array_fset(v_ks_3683_, v_x_3680_, v_x_3681_);
v___x_3704_ = lean_array_fset(v_vs_3684_, v_x_3680_, v_x_3682_);
lean_dec(v_x_3680_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 1, v___x_3704_);
lean_ctor_set(v___x_3686_, 0, v___x_3703_);
v___x_3706_ = v___x_3686_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3703_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v___x_3704_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_n_3709_, lean_object* v_k_3710_, lean_object* v_v_3711_){
_start:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3712_ = lean_unsigned_to_nat(0u);
v___x_3713_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(v_n_3709_, v___x_3712_, v_k_3710_, v_v_3711_);
return v___x_3713_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_3714_; 
v___x_3714_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg(lean_object* v_x_3715_, size_t v_x_3716_, size_t v_x_3717_, lean_object* v_x_3718_, lean_object* v_x_3719_){
_start:
{
if (lean_obj_tag(v_x_3715_) == 0)
{
lean_object* v_es_3720_; size_t v___x_3721_; size_t v___x_3722_; lean_object* v_j_3723_; lean_object* v___x_3724_; uint8_t v___x_3725_; 
v_es_3720_ = lean_ctor_get(v_x_3715_, 0);
v___x_3721_ = ((size_t)31ULL);
v___x_3722_ = lean_usize_land(v_x_3716_, v___x_3721_);
v_j_3723_ = lean_usize_to_nat(v___x_3722_);
v___x_3724_ = lean_array_get_size(v_es_3720_);
v___x_3725_ = lean_nat_dec_lt(v_j_3723_, v___x_3724_);
if (v___x_3725_ == 0)
{
lean_dec(v_j_3723_);
lean_dec(v_x_3719_);
lean_dec(v_x_3718_);
return v_x_3715_;
}
else
{
lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3764_; 
lean_inc_ref(v_es_3720_);
v_isSharedCheck_3764_ = !lean_is_exclusive(v_x_3715_);
if (v_isSharedCheck_3764_ == 0)
{
lean_object* v_unused_3765_; 
v_unused_3765_ = lean_ctor_get(v_x_3715_, 0);
lean_dec(v_unused_3765_);
v___x_3727_ = v_x_3715_;
v_isShared_3728_ = v_isSharedCheck_3764_;
goto v_resetjp_3726_;
}
else
{
lean_dec(v_x_3715_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3764_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v_v_3729_; lean_object* v___x_3730_; lean_object* v_xs_x27_3731_; lean_object* v___y_3733_; 
v_v_3729_ = lean_array_fget(v_es_3720_, v_j_3723_);
v___x_3730_ = lean_box(0);
v_xs_x27_3731_ = lean_array_fset(v_es_3720_, v_j_3723_, v___x_3730_);
switch(lean_obj_tag(v_v_3729_))
{
case 0:
{
lean_object* v_key_3738_; lean_object* v_val_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3749_; 
v_key_3738_ = lean_ctor_get(v_v_3729_, 0);
v_val_3739_ = lean_ctor_get(v_v_3729_, 1);
v_isSharedCheck_3749_ = !lean_is_exclusive(v_v_3729_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3741_ = v_v_3729_;
v_isShared_3742_ = v_isSharedCheck_3749_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_val_3739_);
lean_inc(v_key_3738_);
lean_dec(v_v_3729_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3749_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
uint8_t v___x_3743_; 
v___x_3743_ = l_Lean_instBEqMVarId_beq(v_x_3718_, v_key_3738_);
if (v___x_3743_ == 0)
{
lean_object* v___x_3744_; lean_object* v___x_3745_; 
lean_del_object(v___x_3741_);
v___x_3744_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3738_, v_val_3739_, v_x_3718_, v_x_3719_);
v___x_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3744_);
v___y_3733_ = v___x_3745_;
goto v___jp_3732_;
}
else
{
lean_object* v___x_3747_; 
lean_dec(v_val_3739_);
lean_dec(v_key_3738_);
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 1, v_x_3719_);
lean_ctor_set(v___x_3741_, 0, v_x_3718_);
v___x_3747_ = v___x_3741_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_x_3718_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v_x_3719_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
v___y_3733_ = v___x_3747_;
goto v___jp_3732_;
}
}
}
}
case 1:
{
lean_object* v_node_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3762_; 
v_node_3750_ = lean_ctor_get(v_v_3729_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_v_3729_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3752_ = v_v_3729_;
v_isShared_3753_ = v_isSharedCheck_3762_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_node_3750_);
lean_dec(v_v_3729_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3762_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
size_t v___x_3754_; size_t v___x_3755_; size_t v___x_3756_; size_t v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3760_; 
v___x_3754_ = ((size_t)5ULL);
v___x_3755_ = lean_usize_shift_right(v_x_3716_, v___x_3754_);
v___x_3756_ = ((size_t)1ULL);
v___x_3757_ = lean_usize_add(v_x_3717_, v___x_3756_);
v___x_3758_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg(v_node_3750_, v___x_3755_, v___x_3757_, v_x_3718_, v_x_3719_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 0, v___x_3758_);
v___x_3760_ = v___x_3752_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3758_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
v___y_3733_ = v___x_3760_;
goto v___jp_3732_;
}
}
}
default: 
{
lean_object* v___x_3763_; 
v___x_3763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3763_, 0, v_x_3718_);
lean_ctor_set(v___x_3763_, 1, v_x_3719_);
v___y_3733_ = v___x_3763_;
goto v___jp_3732_;
}
}
v___jp_3732_:
{
lean_object* v___x_3734_; lean_object* v___x_3736_; 
v___x_3734_ = lean_array_fset(v_xs_x27_3731_, v_j_3723_, v___y_3733_);
lean_dec(v_j_3723_);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 0, v___x_3734_);
v___x_3736_ = v___x_3727_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3734_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
}
else
{
lean_object* v_ks_3766_; lean_object* v_vs_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3787_; 
v_ks_3766_ = lean_ctor_get(v_x_3715_, 0);
v_vs_3767_ = lean_ctor_get(v_x_3715_, 1);
v_isSharedCheck_3787_ = !lean_is_exclusive(v_x_3715_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3769_ = v_x_3715_;
v_isShared_3770_ = v_isSharedCheck_3787_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_vs_3767_);
lean_inc(v_ks_3766_);
lean_dec(v_x_3715_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3787_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_ks_3766_);
lean_ctor_set(v_reuseFailAlloc_3786_, 1, v_vs_3767_);
v___x_3772_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
lean_object* v_newNode_3773_; uint8_t v___y_3775_; size_t v___x_3781_; uint8_t v___x_3782_; 
v_newNode_3773_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5___redArg(v___x_3772_, v_x_3718_, v_x_3719_);
v___x_3781_ = ((size_t)7ULL);
v___x_3782_ = lean_usize_dec_le(v___x_3781_, v_x_3717_);
if (v___x_3782_ == 0)
{
lean_object* v___x_3783_; lean_object* v___x_3784_; uint8_t v___x_3785_; 
v___x_3783_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3773_);
v___x_3784_ = lean_unsigned_to_nat(4u);
v___x_3785_ = lean_nat_dec_lt(v___x_3783_, v___x_3784_);
lean_dec(v___x_3783_);
v___y_3775_ = v___x_3785_;
goto v___jp_3774_;
}
else
{
v___y_3775_ = v___x_3782_;
goto v___jp_3774_;
}
v___jp_3774_:
{
if (v___y_3775_ == 0)
{
lean_object* v_ks_3776_; lean_object* v_vs_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
v_ks_3776_ = lean_ctor_get(v_newNode_3773_, 0);
lean_inc_ref(v_ks_3776_);
v_vs_3777_ = lean_ctor_get(v_newNode_3773_, 1);
lean_inc_ref(v_vs_3777_);
lean_dec_ref(v_newNode_3773_);
v___x_3778_ = lean_unsigned_to_nat(0u);
v___x_3779_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___closed__0);
v___x_3780_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___redArg(v_x_3717_, v_ks_3776_, v_vs_3777_, v___x_3778_, v___x_3779_);
lean_dec_ref(v_vs_3777_);
lean_dec_ref(v_ks_3776_);
return v___x_3780_;
}
else
{
return v_newNode_3773_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___redArg(size_t v_depth_3788_, lean_object* v_keys_3789_, lean_object* v_vals_3790_, lean_object* v_i_3791_, lean_object* v_entries_3792_){
_start:
{
lean_object* v___x_3793_; uint8_t v___x_3794_; 
v___x_3793_ = lean_array_get_size(v_keys_3789_);
v___x_3794_ = lean_nat_dec_lt(v_i_3791_, v___x_3793_);
if (v___x_3794_ == 0)
{
lean_dec(v_i_3791_);
return v_entries_3792_;
}
else
{
lean_object* v_k_3795_; lean_object* v_v_3796_; uint64_t v___x_3797_; size_t v_h_3798_; size_t v___x_3799_; lean_object* v___x_3800_; size_t v___x_3801_; size_t v___x_3802_; size_t v___x_3803_; size_t v_h_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v_k_3795_ = lean_array_fget_borrowed(v_keys_3789_, v_i_3791_);
v_v_3796_ = lean_array_fget_borrowed(v_vals_3790_, v_i_3791_);
v___x_3797_ = l_Lean_instHashableMVarId_hash(v_k_3795_);
v_h_3798_ = lean_uint64_to_usize(v___x_3797_);
v___x_3799_ = ((size_t)5ULL);
v___x_3800_ = lean_unsigned_to_nat(1u);
v___x_3801_ = ((size_t)1ULL);
v___x_3802_ = lean_usize_sub(v_depth_3788_, v___x_3801_);
v___x_3803_ = lean_usize_mul(v___x_3799_, v___x_3802_);
v_h_3804_ = lean_usize_shift_right(v_h_3798_, v___x_3803_);
v___x_3805_ = lean_nat_add(v_i_3791_, v___x_3800_);
lean_dec(v_i_3791_);
lean_inc(v_v_3796_);
lean_inc(v_k_3795_);
v___x_3806_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg(v_entries_3792_, v_h_3804_, v_depth_3788_, v_k_3795_, v_v_3796_);
v_i_3791_ = v___x_3805_;
v_entries_3792_ = v___x_3806_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_3808_, lean_object* v_keys_3809_, lean_object* v_vals_3810_, lean_object* v_i_3811_, lean_object* v_entries_3812_){
_start:
{
size_t v_depth_boxed_3813_; lean_object* v_res_3814_; 
v_depth_boxed_3813_ = lean_unbox_usize(v_depth_3808_);
lean_dec(v_depth_3808_);
v_res_3814_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___redArg(v_depth_boxed_3813_, v_keys_3809_, v_vals_3810_, v_i_3811_, v_entries_3812_);
lean_dec_ref(v_vals_3810_);
lean_dec_ref(v_keys_3809_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_x_3815_, lean_object* v_x_3816_, lean_object* v_x_3817_, lean_object* v_x_3818_, lean_object* v_x_3819_){
_start:
{
size_t v_x_24356__boxed_3820_; size_t v_x_24357__boxed_3821_; lean_object* v_res_3822_; 
v_x_24356__boxed_3820_ = lean_unbox_usize(v_x_3816_);
lean_dec(v_x_3816_);
v_x_24357__boxed_3821_ = lean_unbox_usize(v_x_3817_);
lean_dec(v_x_3817_);
v_res_3822_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg(v_x_3815_, v_x_24356__boxed_3820_, v_x_24357__boxed_3821_, v_x_3818_, v_x_3819_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2___redArg(lean_object* v_x_3823_, lean_object* v_x_3824_, lean_object* v_x_3825_){
_start:
{
uint64_t v___x_3826_; size_t v___x_3827_; size_t v___x_3828_; lean_object* v___x_3829_; 
v___x_3826_ = l_Lean_instHashableMVarId_hash(v_x_3824_);
v___x_3827_ = lean_uint64_to_usize(v___x_3826_);
v___x_3828_ = ((size_t)1ULL);
v___x_3829_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg(v_x_3823_, v___x_3827_, v___x_3828_, v_x_3824_, v_x_3825_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(lean_object* v_mvarId_3830_, lean_object* v_val_3831_, lean_object* v___y_3832_){
_start:
{
lean_object* v___x_3834_; lean_object* v_mctx_3835_; lean_object* v_cache_3836_; lean_object* v_zetaDeltaFVarIds_3837_; lean_object* v_postponed_3838_; lean_object* v_diag_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3867_; 
v___x_3834_ = lean_st_ref_take(v___y_3832_);
v_mctx_3835_ = lean_ctor_get(v___x_3834_, 0);
v_cache_3836_ = lean_ctor_get(v___x_3834_, 1);
v_zetaDeltaFVarIds_3837_ = lean_ctor_get(v___x_3834_, 2);
v_postponed_3838_ = lean_ctor_get(v___x_3834_, 3);
v_diag_3839_ = lean_ctor_get(v___x_3834_, 4);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3841_ = v___x_3834_;
v_isShared_3842_ = v_isSharedCheck_3867_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_diag_3839_);
lean_inc(v_postponed_3838_);
lean_inc(v_zetaDeltaFVarIds_3837_);
lean_inc(v_cache_3836_);
lean_inc(v_mctx_3835_);
lean_dec(v___x_3834_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3867_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v_depth_3843_; lean_object* v_levelAssignDepth_3844_; lean_object* v_lmvarCounter_3845_; lean_object* v_mvarCounter_3846_; lean_object* v_lDecls_3847_; lean_object* v_decls_3848_; lean_object* v_userNames_3849_; lean_object* v_lAssignment_3850_; lean_object* v_eAssignment_3851_; lean_object* v_dAssignment_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3866_; 
v_depth_3843_ = lean_ctor_get(v_mctx_3835_, 0);
v_levelAssignDepth_3844_ = lean_ctor_get(v_mctx_3835_, 1);
v_lmvarCounter_3845_ = lean_ctor_get(v_mctx_3835_, 2);
v_mvarCounter_3846_ = lean_ctor_get(v_mctx_3835_, 3);
v_lDecls_3847_ = lean_ctor_get(v_mctx_3835_, 4);
v_decls_3848_ = lean_ctor_get(v_mctx_3835_, 5);
v_userNames_3849_ = lean_ctor_get(v_mctx_3835_, 6);
v_lAssignment_3850_ = lean_ctor_get(v_mctx_3835_, 7);
v_eAssignment_3851_ = lean_ctor_get(v_mctx_3835_, 8);
v_dAssignment_3852_ = lean_ctor_get(v_mctx_3835_, 9);
v_isSharedCheck_3866_ = !lean_is_exclusive(v_mctx_3835_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3854_ = v_mctx_3835_;
v_isShared_3855_ = v_isSharedCheck_3866_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_dAssignment_3852_);
lean_inc(v_eAssignment_3851_);
lean_inc(v_lAssignment_3850_);
lean_inc(v_userNames_3849_);
lean_inc(v_decls_3848_);
lean_inc(v_lDecls_3847_);
lean_inc(v_mvarCounter_3846_);
lean_inc(v_lmvarCounter_3845_);
lean_inc(v_levelAssignDepth_3844_);
lean_inc(v_depth_3843_);
lean_dec(v_mctx_3835_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3866_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3856_; lean_object* v___x_3858_; 
v___x_3856_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2___redArg(v_eAssignment_3851_, v_mvarId_3830_, v_val_3831_);
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 8, v___x_3856_);
v___x_3858_ = v___x_3854_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_depth_3843_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v_levelAssignDepth_3844_);
lean_ctor_set(v_reuseFailAlloc_3865_, 2, v_lmvarCounter_3845_);
lean_ctor_set(v_reuseFailAlloc_3865_, 3, v_mvarCounter_3846_);
lean_ctor_set(v_reuseFailAlloc_3865_, 4, v_lDecls_3847_);
lean_ctor_set(v_reuseFailAlloc_3865_, 5, v_decls_3848_);
lean_ctor_set(v_reuseFailAlloc_3865_, 6, v_userNames_3849_);
lean_ctor_set(v_reuseFailAlloc_3865_, 7, v_lAssignment_3850_);
lean_ctor_set(v_reuseFailAlloc_3865_, 8, v___x_3856_);
lean_ctor_set(v_reuseFailAlloc_3865_, 9, v_dAssignment_3852_);
v___x_3858_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
lean_object* v___x_3860_; 
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 0, v___x_3858_);
v___x_3860_ = v___x_3841_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3864_, 1, v_cache_3836_);
lean_ctor_set(v_reuseFailAlloc_3864_, 2, v_zetaDeltaFVarIds_3837_);
lean_ctor_set(v_reuseFailAlloc_3864_, 3, v_postponed_3838_);
lean_ctor_set(v_reuseFailAlloc_3864_, 4, v_diag_3839_);
v___x_3860_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3861_ = lean_st_ref_set(v___y_3832_, v___x_3860_);
v___x_3862_ = lean_box(0);
v___x_3863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3862_);
return v___x_3863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___boxed(lean_object* v_mvarId_3868_, lean_object* v_val_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_mvarId_3868_, v_val_3869_, v___y_3870_);
lean_dec(v___y_3870_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(uint8_t v___x_3873_, lean_object* v___f_3874_, lean_object* v_____r_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v___x_3886_; lean_object* v_rewriteSimpCache_3887_; lean_object* v_rewriteDSimpCache_3888_; lean_object* v_acCache_3889_; lean_object* v_typeAnalysis_3890_; lean_object* v_goal_3891_; lean_object* v_hypotheses_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3902_; 
v___x_3886_ = lean_st_ref_take(v___y_3878_);
v_rewriteSimpCache_3887_ = lean_ctor_get(v___x_3886_, 0);
v_rewriteDSimpCache_3888_ = lean_ctor_get(v___x_3886_, 1);
v_acCache_3889_ = lean_ctor_get(v___x_3886_, 2);
v_typeAnalysis_3890_ = lean_ctor_get(v___x_3886_, 3);
v_goal_3891_ = lean_ctor_get(v___x_3886_, 4);
v_hypotheses_3892_ = lean_ctor_get(v___x_3886_, 5);
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3894_ = v___x_3886_;
v_isShared_3895_ = v_isSharedCheck_3902_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_hypotheses_3892_);
lean_inc(v_goal_3891_);
lean_inc(v_typeAnalysis_3890_);
lean_inc(v_acCache_3889_);
lean_inc(v_rewriteDSimpCache_3888_);
lean_inc(v_rewriteSimpCache_3887_);
lean_dec(v___x_3886_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3902_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_rewriteSimpCache_3887_);
lean_ctor_set(v_reuseFailAlloc_3901_, 1, v_rewriteDSimpCache_3888_);
lean_ctor_set(v_reuseFailAlloc_3901_, 2, v_acCache_3889_);
lean_ctor_set(v_reuseFailAlloc_3901_, 3, v_typeAnalysis_3890_);
lean_ctor_set(v_reuseFailAlloc_3901_, 4, v_goal_3891_);
lean_ctor_set(v_reuseFailAlloc_3901_, 5, v_hypotheses_3892_);
v___x_3897_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
lean_ctor_set_uint8(v___x_3897_, sizeof(void*)*6, v___x_3873_);
v___x_3898_ = lean_st_ref_set(v___y_3878_, v___x_3897_);
v___x_3899_ = lean_box(0);
lean_inc(v___y_3884_);
lean_inc_ref(v___y_3883_);
lean_inc(v___y_3882_);
lean_inc_ref(v___y_3881_);
lean_inc(v___y_3880_);
lean_inc_ref(v___y_3879_);
lean_inc(v___y_3878_);
lean_inc_ref(v___y_3877_);
lean_inc(v___y_3876_);
v___x_3900_ = lean_apply_11(v___f_3874_, v___x_3899_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, lean_box(0));
return v___x_3900_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1___boxed(lean_object* v___x_3903_, lean_object* v___f_3904_, lean_object* v_____r_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
uint8_t v___x_24569__boxed_3916_; lean_object* v_res_3917_; 
v___x_24569__boxed_3916_ = lean_unbox(v___x_3903_);
v_res_3917_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(v___x_24569__boxed_3916_, v___f_3904_, v_____r_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
lean_dec(v___y_3912_);
lean_dec_ref(v___y_3911_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
lean_dec(v___y_3906_);
return v_res_3917_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0(lean_object* v_snd_3918_, lean_object* v_a_3919_, lean_object* v___x_3920_, lean_object* v_____r_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3932_ = lean_array_push(v_snd_3918_, v_a_3919_);
v___x_3933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3920_);
lean_ctor_set(v___x_3933_, 1, v___x_3932_);
v___x_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3933_);
v___x_3935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3934_);
return v___x_3935_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0___boxed(lean_object* v_snd_3936_, lean_object* v_a_3937_, lean_object* v___x_3938_, lean_object* v_____r_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_){
_start:
{
lean_object* v_res_3950_; 
v_res_3950_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0(v_snd_3936_, v_a_3937_, v___x_3938_, v_____r_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
lean_dec(v___y_3940_);
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg(lean_object* v_upperBound_3951_, lean_object* v___x_3952_, lean_object* v_methods_3953_, lean_object* v_config_3954_, lean_object* v_a_3955_, lean_object* v_b_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_){
_start:
{
lean_object* v___y_3968_; uint8_t v___x_3990_; 
v___x_3990_ = lean_nat_dec_lt(v_a_3955_, v_upperBound_3951_);
if (v___x_3990_ == 0)
{
lean_object* v___x_3991_; 
lean_dec(v_a_3955_);
lean_dec_ref(v_config_3954_);
lean_dec_ref(v_methods_3953_);
v___x_3991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3991_, 0, v_b_3956_);
return v___x_3991_;
}
else
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v_type_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3992_ = lean_st_ref_take(v___y_3957_);
v___x_3993_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
v___x_3994_ = lean_st_ref_set(v___y_3957_, v___x_3993_);
v___x_3995_ = lean_array_fget_borrowed(v___x_3952_, v_a_3955_);
v_type_3996_ = lean_ctor_get(v___x_3995_, 1);
v___x_3997_ = lean_unsigned_to_nat(0u);
v___x_3998_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
lean_ctor_set(v___x_3998_, 1, v___x_3992_);
lean_ctor_set(v___x_3998_, 2, v___x_3993_);
lean_ctor_set(v___x_3998_, 3, v___x_3993_);
lean_inc_ref(v_type_3996_);
v___x_3999_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3999_, 0, v_type_3996_);
lean_inc_ref(v_config_3954_);
lean_inc_ref(v_methods_3953_);
v___x_4000_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_3999_, v_methods_3953_, v_config_3954_, v___x_3998_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; lean_object* v_snd_4002_; lean_object* v_fst_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4085_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref_known(v___x_4000_, 1);
v_snd_4002_ = lean_ctor_get(v_a_4001_, 1);
v_fst_4003_ = lean_ctor_get(v_a_4001_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v_a_4001_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4005_ = v_a_4001_;
v_isShared_4006_ = v_isSharedCheck_4085_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_snd_4002_);
lean_inc(v_fst_4003_);
lean_dec(v_a_4001_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4085_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v_persistentCache_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; 
v_persistentCache_4007_ = lean_ctor_get(v_snd_4002_, 1);
lean_inc_ref(v_persistentCache_4007_);
lean_dec(v_snd_4002_);
v___x_4008_ = lean_st_ref_set(v___y_3957_, v_persistentCache_4007_);
lean_inc(v___x_3995_);
v___x_4009_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v___x_3995_, v_fst_4003_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; lean_object* v_snd_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4075_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
lean_inc(v_a_4010_);
lean_dec_ref_known(v___x_4009_, 1);
v_snd_4011_ = lean_ctor_get(v_b_3956_, 1);
v_isSharedCheck_4075_ = !lean_is_exclusive(v_b_3956_);
if (v_isSharedCheck_4075_ == 0)
{
lean_object* v_unused_4076_; 
v_unused_4076_ = lean_ctor_get(v_b_3956_, 0);
lean_dec(v_unused_4076_);
v___x_4013_ = v_b_3956_;
v_isShared_4014_ = v_isSharedCheck_4075_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_snd_4011_);
lean_dec(v_b_3956_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4075_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v_type_4015_; lean_object* v_value_4016_; uint8_t v___x_4017_; 
v_type_4015_ = lean_ctor_get(v_a_4010_, 1);
v_value_4016_ = lean_ctor_get(v_a_4010_, 2);
lean_inc_ref(v_type_4015_);
v___x_4017_ = l_Lean_Expr_isFalse(v_type_4015_);
if (v___x_4017_ == 0)
{
lean_object* v___x_4018_; lean_object* v___f_4019_; uint8_t v___x_4048_; 
lean_del_object(v___x_4013_);
v___x_4018_ = lean_box(0);
lean_inc(v_a_4010_);
lean_inc(v_snd_4011_);
v___f_4019_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0___boxed), 14, 3);
lean_closure_set(v___f_4019_, 0, v_snd_4011_);
lean_closure_set(v___f_4019_, 1, v_a_4010_);
lean_closure_set(v___f_4019_, 2, v___x_4018_);
v___x_4048_ = lean_expr_eqv(v_type_3996_, v_type_4015_);
if (v___x_4048_ == 0)
{
lean_inc_ref(v_type_4015_);
lean_dec(v_snd_4011_);
lean_dec(v_a_4010_);
goto v___jp_4023_;
}
else
{
if (v___x_4017_ == 0)
{
lean_object* v___x_4049_; lean_object* v___x_4050_; 
lean_dec_ref(v___f_4019_);
lean_del_object(v___x_4005_);
v___x_4049_ = lean_box(0);
v___x_4050_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0(v_snd_4011_, v_a_4010_, v___x_4018_, v___x_4049_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
v___y_3968_ = v___x_4050_;
goto v___jp_3967_;
}
else
{
lean_inc_ref(v_type_4015_);
lean_dec(v_snd_4011_);
lean_dec(v_a_4010_);
goto v___jp_4023_;
}
}
v___jp_4020_:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4021_ = lean_box(0);
v___x_4022_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(v___x_3990_, v___f_4019_, v___x_4021_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
v___y_3968_ = v___x_4022_;
goto v___jp_3967_;
}
v___jp_4023_:
{
lean_object* v_options_4024_; uint8_t v_hasTrace_4025_; 
v_options_4024_ = lean_ctor_get(v___y_3964_, 2);
v_hasTrace_4025_ = lean_ctor_get_uint8(v_options_4024_, sizeof(void*)*1);
if (v_hasTrace_4025_ == 0)
{
lean_dec_ref(v_type_4015_);
lean_del_object(v___x_4005_);
goto v___jp_4020_;
}
else
{
lean_object* v_inheritedTraceOptions_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; uint8_t v___x_4029_; 
v_inheritedTraceOptions_4026_ = lean_ctor_get(v___y_3964_, 13);
v___x_4027_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___x_4028_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___x_4029_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4026_, v_options_4024_, v___x_4028_);
if (v___x_4029_ == 0)
{
lean_dec_ref(v_type_4015_);
lean_del_object(v___x_4005_);
goto v___jp_4020_;
}
else
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4033_; 
lean_inc_ref(v_type_3996_);
v___x_4030_ = l_Lean_MessageData_ofExpr(v_type_3996_);
v___x_4031_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_4006_ == 0)
{
lean_ctor_set_tag(v___x_4005_, 7);
lean_ctor_set(v___x_4005_, 1, v___x_4031_);
lean_ctor_set(v___x_4005_, 0, v___x_4030_);
v___x_4033_ = v___x_4005_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v___x_4030_);
lean_ctor_set(v_reuseFailAlloc_4047_, 1, v___x_4031_);
v___x_4033_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4034_ = l_Lean_MessageData_ofExpr(v_type_4015_);
v___x_4035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4033_);
lean_ctor_set(v___x_4035_, 1, v___x_4034_);
v___x_4036_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v___x_4027_, v___x_4035_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4038_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
lean_inc(v_a_4037_);
lean_dec_ref_known(v___x_4036_, 1);
v___x_4038_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(v___x_3990_, v___f_4019_, v_a_4037_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
v___y_3968_ = v___x_4038_;
goto v___jp_3967_;
}
else
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
lean_dec_ref(v___f_4019_);
lean_dec(v_a_3955_);
lean_dec_ref(v_config_3954_);
lean_dec_ref(v_methods_3953_);
v_a_4039_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4041_ = v___x_4036_;
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v___x_4036_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4044_; 
if (v_isShared_4042_ == 0)
{
v___x_4044_ = v___x_4041_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_a_4039_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
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
lean_object* v___x_4051_; lean_object* v_goal_4052_; lean_object* v___x_4053_; 
lean_inc_ref(v_value_4016_);
lean_dec(v_a_4010_);
lean_del_object(v___x_4005_);
lean_dec(v_a_3955_);
lean_dec_ref(v_config_3954_);
lean_dec_ref(v_methods_3953_);
v___x_4051_ = lean_st_ref_get(v___y_3959_);
v_goal_4052_ = lean_ctor_get(v___x_4051_, 4);
lean_inc(v_goal_4052_);
lean_dec(v___x_4051_);
v___x_4053_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_goal_4052_, v_value_4016_, v___y_3963_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4065_; 
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4065_ == 0)
{
lean_object* v_unused_4066_; 
v_unused_4066_ = lean_ctor_get(v___x_4053_, 0);
lean_dec(v_unused_4066_);
v___x_4055_ = v___x_4053_;
v_isShared_4056_ = v_isSharedCheck_4065_;
goto v_resetjp_4054_;
}
else
{
lean_dec(v___x_4053_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4065_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4060_; 
v___x_4057_ = lean_box(v___x_4017_);
v___x_4058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4057_);
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 0, v___x_4058_);
v___x_4060_ = v___x_4013_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4058_);
lean_ctor_set(v_reuseFailAlloc_4064_, 1, v_snd_4011_);
v___x_4060_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
lean_object* v___x_4062_; 
if (v_isShared_4056_ == 0)
{
lean_ctor_set(v___x_4055_, 0, v___x_4060_);
v___x_4062_ = v___x_4055_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4060_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
}
else
{
lean_object* v_a_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4074_; 
lean_del_object(v___x_4013_);
lean_dec(v_snd_4011_);
v_a_4067_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4069_ = v___x_4053_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v___x_4053_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4067_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
}
}
}
}
}
}
else
{
lean_object* v_a_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4084_; 
lean_del_object(v___x_4005_);
lean_dec_ref(v_b_3956_);
lean_dec(v_a_3955_);
lean_dec_ref(v_config_3954_);
lean_dec_ref(v_methods_3953_);
v_a_4077_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4084_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4084_ == 0)
{
v___x_4079_ = v___x_4009_;
v_isShared_4080_ = v_isSharedCheck_4084_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_a_4077_);
lean_dec(v___x_4009_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4084_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4082_; 
if (v_isShared_4080_ == 0)
{
v___x_4082_ = v___x_4079_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_a_4077_);
v___x_4082_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
return v___x_4082_;
}
}
}
}
}
else
{
lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4093_; 
lean_dec_ref(v_b_3956_);
lean_dec(v_a_3955_);
lean_dec_ref(v_config_3954_);
lean_dec_ref(v_methods_3953_);
v_a_4086_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4088_ = v___x_4000_;
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v___x_4000_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4091_; 
if (v_isShared_4089_ == 0)
{
v___x_4091_ = v___x_4088_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4086_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
}
v___jp_3967_:
{
if (lean_obj_tag(v___y_3968_) == 0)
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3981_; 
v_a_3969_ = lean_ctor_get(v___y_3968_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___y_3968_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3971_ = v___y_3968_;
v_isShared_3972_ = v_isSharedCheck_3981_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___y_3968_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3981_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
if (lean_obj_tag(v_a_3969_) == 0)
{
lean_object* v_a_3973_; lean_object* v___x_3975_; 
lean_dec(v_a_3955_);
lean_dec_ref(v_config_3954_);
lean_dec_ref(v_methods_3953_);
v_a_3973_ = lean_ctor_get(v_a_3969_, 0);
lean_inc(v_a_3973_);
lean_dec_ref_known(v_a_3969_, 1);
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 0, v_a_3973_);
v___x_3975_ = v___x_3971_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_a_3973_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
else
{
lean_object* v_a_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
lean_del_object(v___x_3971_);
v_a_3977_ = lean_ctor_get(v_a_3969_, 0);
lean_inc(v_a_3977_);
lean_dec_ref_known(v_a_3969_, 1);
v___x_3978_ = lean_unsigned_to_nat(1u);
v___x_3979_ = lean_nat_add(v_a_3955_, v___x_3978_);
lean_dec(v_a_3955_);
v_a_3955_ = v___x_3979_;
v_b_3956_ = v_a_3977_;
goto _start;
}
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_dec(v_a_3955_);
lean_dec_ref(v_config_3954_);
lean_dec_ref(v_methods_3953_);
v_a_3982_ = lean_ctor_get(v___y_3968_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___y_3968_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___y_3968_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___y_3968_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___boxed(lean_object* v_upperBound_4094_, lean_object* v___x_4095_, lean_object* v_methods_4096_, lean_object* v_config_4097_, lean_object* v_a_4098_, lean_object* v_b_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg(v_upperBound_4094_, v___x_4095_, v_methods_4096_, v_config_4097_, v_a_4098_, v_b_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v___y_4100_);
lean_dec_ref(v___x_4095_);
lean_dec(v_upperBound_4094_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(lean_object* v_methods_4111_, lean_object* v_config_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_){
_start:
{
lean_object* v___x_4123_; lean_object* v_hypotheses_4124_; lean_object* v___x_4125_; lean_object* v_newHyps_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4123_ = lean_st_ref_get(v_a_4115_);
v_hypotheses_4124_ = lean_ctor_get(v___x_4123_, 5);
lean_inc_ref(v_hypotheses_4124_);
lean_dec(v___x_4123_);
v___x_4125_ = lean_array_get_size(v_hypotheses_4124_);
v_newHyps_4126_ = lean_mk_empty_array_with_capacity(v___x_4125_);
v___x_4127_ = lean_unsigned_to_nat(0u);
v___x_4128_ = lean_box(0);
v___x_4129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4128_);
lean_ctor_set(v___x_4129_, 1, v_newHyps_4126_);
v___x_4130_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg(v___x_4125_, v_hypotheses_4124_, v_methods_4111_, v_config_4112_, v___x_4127_, v___x_4129_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_);
lean_dec_ref(v_hypotheses_4124_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4162_; 
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4133_ = v___x_4130_;
v_isShared_4134_ = v_isSharedCheck_4162_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v___x_4130_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4162_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v_fst_4135_; 
v_fst_4135_ = lean_ctor_get(v_a_4131_, 0);
if (lean_obj_tag(v_fst_4135_) == 0)
{
lean_object* v_snd_4136_; lean_object* v___x_4137_; lean_object* v_rewriteSimpCache_4138_; lean_object* v_rewriteDSimpCache_4139_; lean_object* v_acCache_4140_; lean_object* v_typeAnalysis_4141_; lean_object* v_goal_4142_; uint8_t v_didChange_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4156_; 
v_snd_4136_ = lean_ctor_get(v_a_4131_, 1);
lean_inc(v_snd_4136_);
lean_dec(v_a_4131_);
v___x_4137_ = lean_st_ref_take(v_a_4115_);
v_rewriteSimpCache_4138_ = lean_ctor_get(v___x_4137_, 0);
v_rewriteDSimpCache_4139_ = lean_ctor_get(v___x_4137_, 1);
v_acCache_4140_ = lean_ctor_get(v___x_4137_, 2);
v_typeAnalysis_4141_ = lean_ctor_get(v___x_4137_, 3);
v_goal_4142_ = lean_ctor_get(v___x_4137_, 4);
v_didChange_4143_ = lean_ctor_get_uint8(v___x_4137_, sizeof(void*)*6);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4156_ == 0)
{
lean_object* v_unused_4157_; 
v_unused_4157_ = lean_ctor_get(v___x_4137_, 5);
lean_dec(v_unused_4157_);
v___x_4145_ = v___x_4137_;
v_isShared_4146_ = v_isSharedCheck_4156_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_goal_4142_);
lean_inc(v_typeAnalysis_4141_);
lean_inc(v_acCache_4140_);
lean_inc(v_rewriteDSimpCache_4139_);
lean_inc(v_rewriteSimpCache_4138_);
lean_dec(v___x_4137_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4156_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
lean_ctor_set(v___x_4145_, 5, v_snd_4136_);
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_rewriteSimpCache_4138_);
lean_ctor_set(v_reuseFailAlloc_4155_, 1, v_rewriteDSimpCache_4139_);
lean_ctor_set(v_reuseFailAlloc_4155_, 2, v_acCache_4140_);
lean_ctor_set(v_reuseFailAlloc_4155_, 3, v_typeAnalysis_4141_);
lean_ctor_set(v_reuseFailAlloc_4155_, 4, v_goal_4142_);
lean_ctor_set(v_reuseFailAlloc_4155_, 5, v_snd_4136_);
lean_ctor_set_uint8(v_reuseFailAlloc_4155_, sizeof(void*)*6, v_didChange_4143_);
v___x_4148_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
lean_object* v___x_4149_; uint8_t v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4153_; 
v___x_4149_ = lean_st_ref_set(v_a_4115_, v___x_4148_);
v___x_4150_ = 0;
v___x_4151_ = lean_box(v___x_4150_);
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 0, v___x_4151_);
v___x_4153_ = v___x_4133_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v___x_4151_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
else
{
lean_object* v_val_4158_; lean_object* v___x_4160_; 
lean_inc_ref(v_fst_4135_);
lean_dec(v_a_4131_);
v_val_4158_ = lean_ctor_get(v_fst_4135_, 0);
lean_inc(v_val_4158_);
lean_dec_ref_known(v_fst_4135_, 1);
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 0, v_val_4158_);
v___x_4160_ = v___x_4133_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_val_4158_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
else
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4170_; 
v_a_4163_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4170_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4165_ = v___x_4130_;
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v___x_4130_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4168_; 
if (v_isShared_4166_ == 0)
{
v___x_4168_ = v___x_4165_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v_a_4163_);
v___x_4168_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
return v___x_4168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go___boxed(lean_object* v_methods_4171_, lean_object* v_config_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_){
_start:
{
lean_object* v_res_4183_; 
v_res_4183_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_4171_, v_config_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
lean_dec(v_a_4181_);
lean_dec_ref(v_a_4180_);
lean_dec(v_a_4179_);
lean_dec_ref(v_a_4178_);
lean_dec(v_a_4177_);
lean_dec_ref(v_a_4176_);
lean_dec(v_a_4175_);
lean_dec_ref(v_a_4174_);
lean_dec(v_a_4173_);
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(lean_object* v_cls_4184_, lean_object* v_msg_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v___x_4196_; 
v___x_4196_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_4184_, v_msg_4185_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___boxed(lean_object* v_cls_4197_, lean_object* v_msg_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_){
_start:
{
lean_object* v_res_4209_; 
v_res_4209_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(v_cls_4197_, v_msg_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
return v_res_4209_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(lean_object* v_mvarId_4210_, lean_object* v_val_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
lean_object* v___x_4222_; 
v___x_4222_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_mvarId_4210_, v_val_4211_, v___y_4218_);
return v___x_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___boxed(lean_object* v_mvarId_4223_, lean_object* v_val_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
lean_object* v_res_4235_; 
v_res_4235_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(v_mvarId_4223_, v_val_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
lean_dec(v___y_4225_);
return v_res_4235_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2(lean_object* v_upperBound_4236_, lean_object* v___x_4237_, lean_object* v_methods_4238_, lean_object* v_config_4239_, lean_object* v_inst_4240_, lean_object* v_R_4241_, lean_object* v_a_4242_, lean_object* v_b_4243_, lean_object* v_c_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_){
_start:
{
lean_object* v___x_4255_; 
v___x_4255_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg(v_upperBound_4236_, v___x_4237_, v_methods_4238_, v_config_4239_, v_a_4242_, v_b_4243_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_4256_ = _args[0];
lean_object* v___x_4257_ = _args[1];
lean_object* v_methods_4258_ = _args[2];
lean_object* v_config_4259_ = _args[3];
lean_object* v_inst_4260_ = _args[4];
lean_object* v_R_4261_ = _args[5];
lean_object* v_a_4262_ = _args[6];
lean_object* v_b_4263_ = _args[7];
lean_object* v_c_4264_ = _args[8];
lean_object* v___y_4265_ = _args[9];
lean_object* v___y_4266_ = _args[10];
lean_object* v___y_4267_ = _args[11];
lean_object* v___y_4268_ = _args[12];
lean_object* v___y_4269_ = _args[13];
lean_object* v___y_4270_ = _args[14];
lean_object* v___y_4271_ = _args[15];
lean_object* v___y_4272_ = _args[16];
lean_object* v___y_4273_ = _args[17];
lean_object* v___y_4274_ = _args[18];
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2(v_upperBound_4256_, v___x_4257_, v_methods_4258_, v_config_4259_, v_inst_4260_, v_R_4261_, v_a_4262_, v_b_4263_, v_c_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_);
lean_dec(v___y_4273_);
lean_dec_ref(v___y_4272_);
lean_dec(v___y_4271_);
lean_dec_ref(v___y_4270_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec_ref(v___x_4257_);
lean_dec(v_upperBound_4256_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2(lean_object* v_00_u03b2_4276_, lean_object* v_x_4277_, lean_object* v_x_4278_, lean_object* v_x_4279_){
_start:
{
lean_object* v___x_4280_; 
v___x_4280_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2___redArg(v_x_4277_, v_x_4278_, v_x_4279_);
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4281_, lean_object* v_x_4282_, size_t v_x_4283_, size_t v_x_4284_, lean_object* v_x_4285_, lean_object* v_x_4286_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg(v_x_4282_, v_x_4283_, v_x_4284_, v_x_4285_, v_x_4286_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4288_, lean_object* v_x_4289_, lean_object* v_x_4290_, lean_object* v_x_4291_, lean_object* v_x_4292_, lean_object* v_x_4293_){
_start:
{
size_t v_x_25169__boxed_4294_; size_t v_x_25170__boxed_4295_; lean_object* v_res_4296_; 
v_x_25169__boxed_4294_ = lean_unbox_usize(v_x_4290_);
lean_dec(v_x_4290_);
v_x_25170__boxed_4295_ = lean_unbox_usize(v_x_4291_);
lean_dec(v_x_4291_);
v_res_4296_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3(v_00_u03b2_4288_, v_x_4289_, v_x_25169__boxed_4294_, v_x_25170__boxed_4295_, v_x_4292_, v_x_4293_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_4297_, lean_object* v_n_4298_, lean_object* v_k_4299_, lean_object* v_v_4300_){
_start:
{
lean_object* v___x_4301_; 
v___x_4301_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5___redArg(v_n_4298_, v_k_4299_, v_v_4300_);
return v___x_4301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_4302_, size_t v_depth_4303_, lean_object* v_keys_4304_, lean_object* v_vals_4305_, lean_object* v_heq_4306_, lean_object* v_i_4307_, lean_object* v_entries_4308_){
_start:
{
lean_object* v___x_4309_; 
v___x_4309_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___redArg(v_depth_4303_, v_keys_4304_, v_vals_4305_, v_i_4307_, v_entries_4308_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_4310_, lean_object* v_depth_4311_, lean_object* v_keys_4312_, lean_object* v_vals_4313_, lean_object* v_heq_4314_, lean_object* v_i_4315_, lean_object* v_entries_4316_){
_start:
{
size_t v_depth_boxed_4317_; lean_object* v_res_4318_; 
v_depth_boxed_4317_ = lean_unbox_usize(v_depth_4311_);
lean_dec(v_depth_4311_);
v_res_4318_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6(v_00_u03b2_4310_, v_depth_boxed_4317_, v_keys_4312_, v_vals_4313_, v_heq_4314_, v_i_4315_, v_entries_4316_);
lean_dec_ref(v_vals_4313_);
lean_dec_ref(v_keys_4312_);
return v_res_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_4319_, lean_object* v_x_4320_, lean_object* v_x_4321_, lean_object* v_x_4322_, lean_object* v_x_4323_){
_start:
{
lean_object* v___x_4324_; 
v___x_4324_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(v_x_4320_, v_x_4321_, v_x_4322_, v_x_4323_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(lean_object* v_methods_4325_, lean_object* v_config_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_){
_start:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
v___x_4336_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
v___x_4337_ = lean_st_mk_ref(v___x_4336_);
v___x_4338_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_4325_, v_config_4326_, v___x_4337_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_, v_a_4334_);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4347_; 
v_a_4339_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4341_ = v___x_4338_;
v_isShared_4342_ = v_isSharedCheck_4347_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4338_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4347_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4343_; lean_object* v___x_4345_; 
v___x_4343_ = lean_st_ref_get(v___x_4337_);
lean_dec(v___x_4337_);
lean_dec(v___x_4343_);
if (v_isShared_4342_ == 0)
{
v___x_4345_ = v___x_4341_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_a_4339_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
}
else
{
lean_dec(v___x_4337_);
return v___x_4338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps___boxed(lean_object* v_methods_4348_, lean_object* v_config_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(v_methods_4348_, v_config_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
lean_dec(v_a_4357_);
lean_dec_ref(v_a_4356_);
lean_dec(v_a_4355_);
lean_dec_ref(v_a_4354_);
lean_dec(v_a_4353_);
lean_dec_ref(v_a_4352_);
lean_dec(v_a_4351_);
lean_dec_ref(v_a_4350_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(lean_object* v_mvarId_4360_, lean_object* v_val_4361_, lean_object* v___y_4362_){
_start:
{
lean_object* v___x_4364_; lean_object* v_mctx_4365_; lean_object* v_cache_4366_; lean_object* v_zetaDeltaFVarIds_4367_; lean_object* v_postponed_4368_; lean_object* v_diag_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4397_; 
v___x_4364_ = lean_st_ref_take(v___y_4362_);
v_mctx_4365_ = lean_ctor_get(v___x_4364_, 0);
v_cache_4366_ = lean_ctor_get(v___x_4364_, 1);
v_zetaDeltaFVarIds_4367_ = lean_ctor_get(v___x_4364_, 2);
v_postponed_4368_ = lean_ctor_get(v___x_4364_, 3);
v_diag_4369_ = lean_ctor_get(v___x_4364_, 4);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4364_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4371_ = v___x_4364_;
v_isShared_4372_ = v_isSharedCheck_4397_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_diag_4369_);
lean_inc(v_postponed_4368_);
lean_inc(v_zetaDeltaFVarIds_4367_);
lean_inc(v_cache_4366_);
lean_inc(v_mctx_4365_);
lean_dec(v___x_4364_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4397_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v_depth_4373_; lean_object* v_levelAssignDepth_4374_; lean_object* v_lmvarCounter_4375_; lean_object* v_mvarCounter_4376_; lean_object* v_lDecls_4377_; lean_object* v_decls_4378_; lean_object* v_userNames_4379_; lean_object* v_lAssignment_4380_; lean_object* v_eAssignment_4381_; lean_object* v_dAssignment_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4396_; 
v_depth_4373_ = lean_ctor_get(v_mctx_4365_, 0);
v_levelAssignDepth_4374_ = lean_ctor_get(v_mctx_4365_, 1);
v_lmvarCounter_4375_ = lean_ctor_get(v_mctx_4365_, 2);
v_mvarCounter_4376_ = lean_ctor_get(v_mctx_4365_, 3);
v_lDecls_4377_ = lean_ctor_get(v_mctx_4365_, 4);
v_decls_4378_ = lean_ctor_get(v_mctx_4365_, 5);
v_userNames_4379_ = lean_ctor_get(v_mctx_4365_, 6);
v_lAssignment_4380_ = lean_ctor_get(v_mctx_4365_, 7);
v_eAssignment_4381_ = lean_ctor_get(v_mctx_4365_, 8);
v_dAssignment_4382_ = lean_ctor_get(v_mctx_4365_, 9);
v_isSharedCheck_4396_ = !lean_is_exclusive(v_mctx_4365_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4384_ = v_mctx_4365_;
v_isShared_4385_ = v_isSharedCheck_4396_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_dAssignment_4382_);
lean_inc(v_eAssignment_4381_);
lean_inc(v_lAssignment_4380_);
lean_inc(v_userNames_4379_);
lean_inc(v_decls_4378_);
lean_inc(v_lDecls_4377_);
lean_inc(v_mvarCounter_4376_);
lean_inc(v_lmvarCounter_4375_);
lean_inc(v_levelAssignDepth_4374_);
lean_inc(v_depth_4373_);
lean_dec(v_mctx_4365_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4396_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4386_; lean_object* v___x_4388_; 
v___x_4386_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2___redArg(v_eAssignment_4381_, v_mvarId_4360_, v_val_4361_);
if (v_isShared_4385_ == 0)
{
lean_ctor_set(v___x_4384_, 8, v___x_4386_);
v___x_4388_ = v___x_4384_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_depth_4373_);
lean_ctor_set(v_reuseFailAlloc_4395_, 1, v_levelAssignDepth_4374_);
lean_ctor_set(v_reuseFailAlloc_4395_, 2, v_lmvarCounter_4375_);
lean_ctor_set(v_reuseFailAlloc_4395_, 3, v_mvarCounter_4376_);
lean_ctor_set(v_reuseFailAlloc_4395_, 4, v_lDecls_4377_);
lean_ctor_set(v_reuseFailAlloc_4395_, 5, v_decls_4378_);
lean_ctor_set(v_reuseFailAlloc_4395_, 6, v_userNames_4379_);
lean_ctor_set(v_reuseFailAlloc_4395_, 7, v_lAssignment_4380_);
lean_ctor_set(v_reuseFailAlloc_4395_, 8, v___x_4386_);
lean_ctor_set(v_reuseFailAlloc_4395_, 9, v_dAssignment_4382_);
v___x_4388_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
lean_object* v___x_4390_; 
if (v_isShared_4372_ == 0)
{
lean_ctor_set(v___x_4371_, 0, v___x_4388_);
v___x_4390_ = v___x_4371_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v___x_4388_);
lean_ctor_set(v_reuseFailAlloc_4394_, 1, v_cache_4366_);
lean_ctor_set(v_reuseFailAlloc_4394_, 2, v_zetaDeltaFVarIds_4367_);
lean_ctor_set(v_reuseFailAlloc_4394_, 3, v_postponed_4368_);
lean_ctor_set(v_reuseFailAlloc_4394_, 4, v_diag_4369_);
v___x_4390_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
v___x_4391_ = lean_st_ref_set(v___y_4362_, v___x_4390_);
v___x_4392_ = lean_box(0);
v___x_4393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4393_, 0, v___x_4392_);
return v___x_4393_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg___boxed(lean_object* v_mvarId_4398_, lean_object* v_val_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_){
_start:
{
lean_object* v_res_4402_; 
v_res_4402_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_mvarId_4398_, v_val_4399_, v___y_4400_);
lean_dec(v___y_4400_);
return v_res_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(lean_object* v_cls_4403_, lean_object* v_msg_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_){
_start:
{
lean_object* v_ref_4410_; lean_object* v___x_4411_; lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4456_; 
v_ref_4410_ = lean_ctor_get(v___y_4407_, 5);
v___x_4411_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_);
v_a_4412_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4414_ = v___x_4411_;
v_isShared_4415_ = v_isSharedCheck_4456_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4411_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4456_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4416_; lean_object* v_traceState_4417_; lean_object* v_env_4418_; lean_object* v_nextMacroScope_4419_; lean_object* v_ngen_4420_; lean_object* v_auxDeclNGen_4421_; lean_object* v_cache_4422_; lean_object* v_messages_4423_; lean_object* v_infoState_4424_; lean_object* v_snapshotTasks_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4455_; 
v___x_4416_ = lean_st_ref_take(v___y_4408_);
v_traceState_4417_ = lean_ctor_get(v___x_4416_, 4);
v_env_4418_ = lean_ctor_get(v___x_4416_, 0);
v_nextMacroScope_4419_ = lean_ctor_get(v___x_4416_, 1);
v_ngen_4420_ = lean_ctor_get(v___x_4416_, 2);
v_auxDeclNGen_4421_ = lean_ctor_get(v___x_4416_, 3);
v_cache_4422_ = lean_ctor_get(v___x_4416_, 5);
v_messages_4423_ = lean_ctor_get(v___x_4416_, 6);
v_infoState_4424_ = lean_ctor_get(v___x_4416_, 7);
v_snapshotTasks_4425_ = lean_ctor_get(v___x_4416_, 8);
v_isSharedCheck_4455_ = !lean_is_exclusive(v___x_4416_);
if (v_isSharedCheck_4455_ == 0)
{
v___x_4427_ = v___x_4416_;
v_isShared_4428_ = v_isSharedCheck_4455_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_snapshotTasks_4425_);
lean_inc(v_infoState_4424_);
lean_inc(v_messages_4423_);
lean_inc(v_cache_4422_);
lean_inc(v_traceState_4417_);
lean_inc(v_auxDeclNGen_4421_);
lean_inc(v_ngen_4420_);
lean_inc(v_nextMacroScope_4419_);
lean_inc(v_env_4418_);
lean_dec(v___x_4416_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4455_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
uint64_t v_tid_4429_; lean_object* v_traces_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4454_; 
v_tid_4429_ = lean_ctor_get_uint64(v_traceState_4417_, sizeof(void*)*1);
v_traces_4430_ = lean_ctor_get(v_traceState_4417_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v_traceState_4417_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4432_ = v_traceState_4417_;
v_isShared_4433_ = v_isSharedCheck_4454_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_traces_4430_);
lean_dec(v_traceState_4417_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4454_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4434_; double v___x_4435_; uint8_t v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4444_; 
v___x_4434_ = lean_box(0);
v___x_4435_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_4436_ = 0;
v___x_4437_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_4438_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4438_, 0, v_cls_4403_);
lean_ctor_set(v___x_4438_, 1, v___x_4434_);
lean_ctor_set(v___x_4438_, 2, v___x_4437_);
lean_ctor_set_float(v___x_4438_, sizeof(void*)*3, v___x_4435_);
lean_ctor_set_float(v___x_4438_, sizeof(void*)*3 + 8, v___x_4435_);
lean_ctor_set_uint8(v___x_4438_, sizeof(void*)*3 + 16, v___x_4436_);
v___x_4439_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_4440_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4438_);
lean_ctor_set(v___x_4440_, 1, v_a_4412_);
lean_ctor_set(v___x_4440_, 2, v___x_4439_);
lean_inc(v_ref_4410_);
v___x_4441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4441_, 0, v_ref_4410_);
lean_ctor_set(v___x_4441_, 1, v___x_4440_);
v___x_4442_ = l_Lean_PersistentArray_push___redArg(v_traces_4430_, v___x_4441_);
if (v_isShared_4433_ == 0)
{
lean_ctor_set(v___x_4432_, 0, v___x_4442_);
v___x_4444_ = v___x_4432_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v___x_4442_);
lean_ctor_set_uint64(v_reuseFailAlloc_4453_, sizeof(void*)*1, v_tid_4429_);
v___x_4444_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
lean_object* v___x_4446_; 
if (v_isShared_4428_ == 0)
{
lean_ctor_set(v___x_4427_, 4, v___x_4444_);
v___x_4446_ = v___x_4427_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_env_4418_);
lean_ctor_set(v_reuseFailAlloc_4452_, 1, v_nextMacroScope_4419_);
lean_ctor_set(v_reuseFailAlloc_4452_, 2, v_ngen_4420_);
lean_ctor_set(v_reuseFailAlloc_4452_, 3, v_auxDeclNGen_4421_);
lean_ctor_set(v_reuseFailAlloc_4452_, 4, v___x_4444_);
lean_ctor_set(v_reuseFailAlloc_4452_, 5, v_cache_4422_);
lean_ctor_set(v_reuseFailAlloc_4452_, 6, v_messages_4423_);
lean_ctor_set(v_reuseFailAlloc_4452_, 7, v_infoState_4424_);
lean_ctor_set(v_reuseFailAlloc_4452_, 8, v_snapshotTasks_4425_);
v___x_4446_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4450_; 
v___x_4447_ = lean_st_ref_set(v___y_4408_, v___x_4446_);
v___x_4448_ = lean_box(0);
if (v_isShared_4415_ == 0)
{
lean_ctor_set(v___x_4414_, 0, v___x_4448_);
v___x_4450_ = v___x_4414_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v___x_4448_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_4457_, lean_object* v_msg_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
lean_object* v_res_4464_; 
v_res_4464_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_4457_, v_msg_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_dec(v___y_4460_);
lean_dec_ref(v___y_4459_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg(lean_object* v_upperBound_4465_, lean_object* v___x_4466_, lean_object* v_methods_4467_, lean_object* v_config_4468_, lean_object* v_a_4469_, lean_object* v_b_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_){
_start:
{
lean_object* v___y_4482_; uint8_t v___x_4504_; 
v___x_4504_ = lean_nat_dec_lt(v_a_4469_, v_upperBound_4465_);
if (v___x_4504_ == 0)
{
lean_object* v___x_4505_; 
lean_dec(v_a_4469_);
lean_dec_ref(v_config_4468_);
lean_dec_ref(v_methods_4467_);
v___x_4505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4505_, 0, v_b_4470_);
return v___x_4505_;
}
else
{
lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v_type_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; 
v___x_4506_ = lean_st_ref_take(v___y_4471_);
v___x_4507_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1);
v___x_4508_ = lean_st_ref_set(v___y_4471_, v___x_4507_);
v___x_4509_ = lean_array_fget_borrowed(v___x_4466_, v_a_4469_);
v_type_4510_ = lean_ctor_get(v___x_4509_, 1);
v___x_4511_ = lean_unsigned_to_nat(0u);
v___x_4512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4511_);
lean_ctor_set(v___x_4512_, 1, v___x_4506_);
lean_inc_ref(v_type_4510_);
v___x_4513_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_4513_, 0, v_type_4510_);
lean_inc_ref(v_config_4468_);
lean_inc_ref(v_methods_4467_);
v___x_4514_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_4513_, v_methods_4467_, v_config_4468_, v___x_4512_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
if (lean_obj_tag(v___x_4514_) == 0)
{
lean_object* v_a_4515_; lean_object* v_snd_4516_; lean_object* v_fst_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4606_; 
v_a_4515_ = lean_ctor_get(v___x_4514_, 0);
lean_inc(v_a_4515_);
lean_dec_ref_known(v___x_4514_, 1);
v_snd_4516_ = lean_ctor_get(v_a_4515_, 1);
v_fst_4517_ = lean_ctor_get(v_a_4515_, 0);
v_isSharedCheck_4606_ = !lean_is_exclusive(v_a_4515_);
if (v_isSharedCheck_4606_ == 0)
{
v___x_4519_ = v_a_4515_;
v_isShared_4520_ = v_isSharedCheck_4606_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_snd_4516_);
lean_inc(v_fst_4517_);
lean_dec(v_a_4515_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4606_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v_cache_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4604_; 
v_cache_4521_ = lean_ctor_get(v_snd_4516_, 1);
v_isSharedCheck_4604_ = !lean_is_exclusive(v_snd_4516_);
if (v_isSharedCheck_4604_ == 0)
{
lean_object* v_unused_4605_; 
v_unused_4605_ = lean_ctor_get(v_snd_4516_, 0);
lean_dec(v_unused_4605_);
v___x_4523_ = v_snd_4516_;
v_isShared_4524_ = v_isSharedCheck_4604_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_cache_4521_);
lean_dec(v_snd_4516_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4604_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; 
v___x_4525_ = lean_st_ref_set(v___y_4471_, v_cache_4521_);
lean_inc(v___x_4509_);
v___x_4526_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v___x_4509_, v_fst_4517_);
lean_dec(v_fst_4517_);
if (lean_obj_tag(v___x_4526_) == 0)
{
lean_object* v_a_4527_; lean_object* v_snd_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4594_; 
v_a_4527_ = lean_ctor_get(v___x_4526_, 0);
lean_inc(v_a_4527_);
lean_dec_ref_known(v___x_4526_, 1);
v_snd_4528_ = lean_ctor_get(v_b_4470_, 1);
v_isSharedCheck_4594_ = !lean_is_exclusive(v_b_4470_);
if (v_isSharedCheck_4594_ == 0)
{
lean_object* v_unused_4595_; 
v_unused_4595_ = lean_ctor_get(v_b_4470_, 0);
lean_dec(v_unused_4595_);
v___x_4530_ = v_b_4470_;
v_isShared_4531_ = v_isSharedCheck_4594_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_snd_4528_);
lean_dec(v_b_4470_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4594_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v_type_4532_; lean_object* v_value_4533_; uint8_t v___x_4534_; 
v_type_4532_ = lean_ctor_get(v_a_4527_, 1);
v_value_4533_ = lean_ctor_get(v_a_4527_, 2);
lean_inc_ref(v_type_4532_);
v___x_4534_ = l_Lean_Expr_isFalse(v_type_4532_);
if (v___x_4534_ == 0)
{
lean_object* v___x_4535_; lean_object* v___f_4536_; uint8_t v___x_4567_; 
lean_del_object(v___x_4530_);
v___x_4535_ = lean_box(0);
lean_inc(v_a_4527_);
lean_inc(v_snd_4528_);
v___f_4536_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0___boxed), 14, 3);
lean_closure_set(v___f_4536_, 0, v_snd_4528_);
lean_closure_set(v___f_4536_, 1, v_a_4527_);
lean_closure_set(v___f_4536_, 2, v___x_4535_);
v___x_4567_ = lean_expr_eqv(v_type_4510_, v_type_4532_);
if (v___x_4567_ == 0)
{
lean_inc_ref(v_type_4532_);
lean_dec(v_snd_4528_);
lean_dec(v_a_4527_);
goto v___jp_4540_;
}
else
{
if (v___x_4534_ == 0)
{
lean_object* v___x_4568_; lean_object* v___x_4569_; 
lean_dec_ref(v___f_4536_);
lean_del_object(v___x_4523_);
lean_del_object(v___x_4519_);
v___x_4568_ = lean_box(0);
v___x_4569_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0(v_snd_4528_, v_a_4527_, v___x_4535_, v___x_4568_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
v___y_4482_ = v___x_4569_;
goto v___jp_4481_;
}
else
{
lean_inc_ref(v_type_4532_);
lean_dec(v_snd_4528_);
lean_dec(v_a_4527_);
goto v___jp_4540_;
}
}
v___jp_4537_:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; 
v___x_4538_ = lean_box(0);
v___x_4539_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(v___x_4504_, v___f_4536_, v___x_4538_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
v___y_4482_ = v___x_4539_;
goto v___jp_4481_;
}
v___jp_4540_:
{
lean_object* v_options_4541_; uint8_t v_hasTrace_4542_; 
v_options_4541_ = lean_ctor_get(v___y_4478_, 2);
v_hasTrace_4542_ = lean_ctor_get_uint8(v_options_4541_, sizeof(void*)*1);
if (v_hasTrace_4542_ == 0)
{
lean_dec_ref(v_type_4532_);
lean_del_object(v___x_4523_);
lean_del_object(v___x_4519_);
goto v___jp_4537_;
}
else
{
lean_object* v_inheritedTraceOptions_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; uint8_t v___x_4546_; 
v_inheritedTraceOptions_4543_ = lean_ctor_get(v___y_4478_, 13);
v___x_4544_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___x_4545_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___x_4546_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4543_, v_options_4541_, v___x_4545_);
if (v___x_4546_ == 0)
{
lean_dec_ref(v_type_4532_);
lean_del_object(v___x_4523_);
lean_del_object(v___x_4519_);
goto v___jp_4537_;
}
else
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4550_; 
lean_inc_ref(v_type_4510_);
v___x_4547_ = l_Lean_MessageData_ofExpr(v_type_4510_);
v___x_4548_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_4524_ == 0)
{
lean_ctor_set_tag(v___x_4523_, 7);
lean_ctor_set(v___x_4523_, 1, v___x_4548_);
lean_ctor_set(v___x_4523_, 0, v___x_4547_);
v___x_4550_ = v___x_4523_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4566_; 
v_reuseFailAlloc_4566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4566_, 0, v___x_4547_);
lean_ctor_set(v_reuseFailAlloc_4566_, 1, v___x_4548_);
v___x_4550_ = v_reuseFailAlloc_4566_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
lean_object* v___x_4551_; lean_object* v___x_4553_; 
v___x_4551_ = l_Lean_MessageData_ofExpr(v_type_4532_);
if (v_isShared_4520_ == 0)
{
lean_ctor_set_tag(v___x_4519_, 7);
lean_ctor_set(v___x_4519_, 1, v___x_4551_);
lean_ctor_set(v___x_4519_, 0, v___x_4550_);
v___x_4553_ = v___x_4519_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v___x_4550_);
lean_ctor_set(v_reuseFailAlloc_4565_, 1, v___x_4551_);
v___x_4553_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
lean_object* v___x_4554_; 
v___x_4554_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v___x_4544_, v___x_4553_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
if (lean_obj_tag(v___x_4554_) == 0)
{
lean_object* v_a_4555_; lean_object* v___x_4556_; 
v_a_4555_ = lean_ctor_get(v___x_4554_, 0);
lean_inc(v_a_4555_);
lean_dec_ref_known(v___x_4554_, 1);
v___x_4556_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(v___x_4504_, v___f_4536_, v_a_4555_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
v___y_4482_ = v___x_4556_;
goto v___jp_4481_;
}
else
{
lean_object* v_a_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4564_; 
lean_dec_ref(v___f_4536_);
lean_dec(v_a_4469_);
lean_dec_ref(v_config_4468_);
lean_dec_ref(v_methods_4467_);
v_a_4557_ = lean_ctor_get(v___x_4554_, 0);
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4554_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4559_ = v___x_4554_;
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_a_4557_);
lean_dec(v___x_4554_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4562_; 
if (v_isShared_4560_ == 0)
{
v___x_4562_ = v___x_4559_;
goto v_reusejp_4561_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v_a_4557_);
v___x_4562_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4561_;
}
v_reusejp_4561_:
{
return v___x_4562_;
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
lean_object* v___x_4570_; lean_object* v_goal_4571_; lean_object* v___x_4572_; 
lean_inc_ref(v_value_4533_);
lean_dec(v_a_4527_);
lean_del_object(v___x_4523_);
lean_del_object(v___x_4519_);
lean_dec(v_a_4469_);
lean_dec_ref(v_config_4468_);
lean_dec_ref(v_methods_4467_);
v___x_4570_ = lean_st_ref_get(v___y_4473_);
v_goal_4571_ = lean_ctor_get(v___x_4570_, 4);
lean_inc(v_goal_4571_);
lean_dec(v___x_4570_);
v___x_4572_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_goal_4571_, v_value_4533_, v___y_4477_);
if (lean_obj_tag(v___x_4572_) == 0)
{
lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4584_; 
v_isSharedCheck_4584_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4584_ == 0)
{
lean_object* v_unused_4585_; 
v_unused_4585_ = lean_ctor_get(v___x_4572_, 0);
lean_dec(v_unused_4585_);
v___x_4574_ = v___x_4572_;
v_isShared_4575_ = v_isSharedCheck_4584_;
goto v_resetjp_4573_;
}
else
{
lean_dec(v___x_4572_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4584_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4579_; 
v___x_4576_ = lean_box(v___x_4534_);
v___x_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4577_, 0, v___x_4576_);
if (v_isShared_4531_ == 0)
{
lean_ctor_set(v___x_4530_, 0, v___x_4577_);
v___x_4579_ = v___x_4530_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v___x_4577_);
lean_ctor_set(v_reuseFailAlloc_4583_, 1, v_snd_4528_);
v___x_4579_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
lean_object* v___x_4581_; 
if (v_isShared_4575_ == 0)
{
lean_ctor_set(v___x_4574_, 0, v___x_4579_);
v___x_4581_ = v___x_4574_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v___x_4579_);
v___x_4581_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
return v___x_4581_;
}
}
}
}
else
{
lean_object* v_a_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4593_; 
lean_del_object(v___x_4530_);
lean_dec(v_snd_4528_);
v_a_4586_ = lean_ctor_get(v___x_4572_, 0);
v_isSharedCheck_4593_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4593_ == 0)
{
v___x_4588_ = v___x_4572_;
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_a_4586_);
lean_dec(v___x_4572_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v___x_4591_; 
if (v_isShared_4589_ == 0)
{
v___x_4591_ = v___x_4588_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v_a_4586_);
v___x_4591_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
return v___x_4591_;
}
}
}
}
}
}
else
{
lean_object* v_a_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4603_; 
lean_del_object(v___x_4523_);
lean_del_object(v___x_4519_);
lean_dec_ref(v_b_4470_);
lean_dec(v_a_4469_);
lean_dec_ref(v_config_4468_);
lean_dec_ref(v_methods_4467_);
v_a_4596_ = lean_ctor_get(v___x_4526_, 0);
v_isSharedCheck_4603_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4598_ = v___x_4526_;
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_a_4596_);
lean_dec(v___x_4526_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4601_; 
if (v_isShared_4599_ == 0)
{
v___x_4601_ = v___x_4598_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_a_4596_);
v___x_4601_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
return v___x_4601_;
}
}
}
}
}
}
else
{
lean_object* v_a_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4614_; 
lean_dec_ref(v_b_4470_);
lean_dec(v_a_4469_);
lean_dec_ref(v_config_4468_);
lean_dec_ref(v_methods_4467_);
v_a_4607_ = lean_ctor_get(v___x_4514_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v___x_4514_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4609_ = v___x_4514_;
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_a_4607_);
lean_dec(v___x_4514_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4612_; 
if (v_isShared_4610_ == 0)
{
v___x_4612_ = v___x_4609_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_a_4607_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
}
}
v___jp_4481_:
{
if (lean_obj_tag(v___y_4482_) == 0)
{
lean_object* v_a_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4495_; 
v_a_4483_ = lean_ctor_get(v___y_4482_, 0);
v_isSharedCheck_4495_ = !lean_is_exclusive(v___y_4482_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_4485_ = v___y_4482_;
v_isShared_4486_ = v_isSharedCheck_4495_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_a_4483_);
lean_dec(v___y_4482_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4495_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
if (lean_obj_tag(v_a_4483_) == 0)
{
lean_object* v_a_4487_; lean_object* v___x_4489_; 
lean_dec(v_a_4469_);
lean_dec_ref(v_config_4468_);
lean_dec_ref(v_methods_4467_);
v_a_4487_ = lean_ctor_get(v_a_4483_, 0);
lean_inc(v_a_4487_);
lean_dec_ref_known(v_a_4483_, 1);
if (v_isShared_4486_ == 0)
{
lean_ctor_set(v___x_4485_, 0, v_a_4487_);
v___x_4489_ = v___x_4485_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_a_4487_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
else
{
lean_object* v_a_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
lean_del_object(v___x_4485_);
v_a_4491_ = lean_ctor_get(v_a_4483_, 0);
lean_inc(v_a_4491_);
lean_dec_ref_known(v_a_4483_, 1);
v___x_4492_ = lean_unsigned_to_nat(1u);
v___x_4493_ = lean_nat_add(v_a_4469_, v___x_4492_);
lean_dec(v_a_4469_);
v_a_4469_ = v___x_4493_;
v_b_4470_ = v_a_4491_;
goto _start;
}
}
}
else
{
lean_object* v_a_4496_; lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4503_; 
lean_dec(v_a_4469_);
lean_dec_ref(v_config_4468_);
lean_dec_ref(v_methods_4467_);
v_a_4496_ = lean_ctor_get(v___y_4482_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___y_4482_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4498_ = v___y_4482_;
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
else
{
lean_inc(v_a_4496_);
lean_dec(v___y_4482_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v___x_4501_; 
if (v_isShared_4499_ == 0)
{
v___x_4501_ = v___x_4498_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_a_4496_);
v___x_4501_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
return v___x_4501_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg___boxed(lean_object* v_upperBound_4615_, lean_object* v___x_4616_, lean_object* v_methods_4617_, lean_object* v_config_4618_, lean_object* v_a_4619_, lean_object* v_b_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_){
_start:
{
lean_object* v_res_4631_; 
v_res_4631_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg(v_upperBound_4615_, v___x_4616_, v_methods_4617_, v_config_4618_, v_a_4619_, v_b_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_);
lean_dec(v___y_4629_);
lean_dec_ref(v___y_4628_);
lean_dec(v___y_4627_);
lean_dec_ref(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec_ref(v___y_4624_);
lean_dec(v___y_4623_);
lean_dec_ref(v___y_4622_);
lean_dec(v___y_4621_);
lean_dec_ref(v___x_4616_);
lean_dec(v_upperBound_4615_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(lean_object* v_methods_4632_, lean_object* v_config_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_){
_start:
{
lean_object* v___x_4644_; lean_object* v_hypotheses_4645_; lean_object* v___x_4646_; lean_object* v_newHyps_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4644_ = lean_st_ref_get(v_a_4636_);
v_hypotheses_4645_ = lean_ctor_get(v___x_4644_, 5);
lean_inc_ref(v_hypotheses_4645_);
lean_dec(v___x_4644_);
v___x_4646_ = lean_array_get_size(v_hypotheses_4645_);
v_newHyps_4647_ = lean_mk_empty_array_with_capacity(v___x_4646_);
v___x_4648_ = lean_unsigned_to_nat(0u);
v___x_4649_ = lean_box(0);
v___x_4650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4650_, 0, v___x_4649_);
lean_ctor_set(v___x_4650_, 1, v_newHyps_4647_);
v___x_4651_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg(v___x_4646_, v_hypotheses_4645_, v_methods_4632_, v_config_4633_, v___x_4648_, v___x_4650_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_);
lean_dec_ref(v_hypotheses_4645_);
if (lean_obj_tag(v___x_4651_) == 0)
{
lean_object* v_a_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4683_; 
v_a_4652_ = lean_ctor_get(v___x_4651_, 0);
v_isSharedCheck_4683_ = !lean_is_exclusive(v___x_4651_);
if (v_isSharedCheck_4683_ == 0)
{
v___x_4654_ = v___x_4651_;
v_isShared_4655_ = v_isSharedCheck_4683_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_a_4652_);
lean_dec(v___x_4651_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4683_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v_fst_4656_; 
v_fst_4656_ = lean_ctor_get(v_a_4652_, 0);
if (lean_obj_tag(v_fst_4656_) == 0)
{
lean_object* v_snd_4657_; lean_object* v___x_4658_; lean_object* v_rewriteSimpCache_4659_; lean_object* v_rewriteDSimpCache_4660_; lean_object* v_acCache_4661_; lean_object* v_typeAnalysis_4662_; lean_object* v_goal_4663_; uint8_t v_didChange_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4677_; 
v_snd_4657_ = lean_ctor_get(v_a_4652_, 1);
lean_inc(v_snd_4657_);
lean_dec(v_a_4652_);
v___x_4658_ = lean_st_ref_take(v_a_4636_);
v_rewriteSimpCache_4659_ = lean_ctor_get(v___x_4658_, 0);
v_rewriteDSimpCache_4660_ = lean_ctor_get(v___x_4658_, 1);
v_acCache_4661_ = lean_ctor_get(v___x_4658_, 2);
v_typeAnalysis_4662_ = lean_ctor_get(v___x_4658_, 3);
v_goal_4663_ = lean_ctor_get(v___x_4658_, 4);
v_didChange_4664_ = lean_ctor_get_uint8(v___x_4658_, sizeof(void*)*6);
v_isSharedCheck_4677_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4677_ == 0)
{
lean_object* v_unused_4678_; 
v_unused_4678_ = lean_ctor_get(v___x_4658_, 5);
lean_dec(v_unused_4678_);
v___x_4666_ = v___x_4658_;
v_isShared_4667_ = v_isSharedCheck_4677_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_goal_4663_);
lean_inc(v_typeAnalysis_4662_);
lean_inc(v_acCache_4661_);
lean_inc(v_rewriteDSimpCache_4660_);
lean_inc(v_rewriteSimpCache_4659_);
lean_dec(v___x_4658_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4677_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4669_; 
if (v_isShared_4667_ == 0)
{
lean_ctor_set(v___x_4666_, 5, v_snd_4657_);
v___x_4669_ = v___x_4666_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_rewriteSimpCache_4659_);
lean_ctor_set(v_reuseFailAlloc_4676_, 1, v_rewriteDSimpCache_4660_);
lean_ctor_set(v_reuseFailAlloc_4676_, 2, v_acCache_4661_);
lean_ctor_set(v_reuseFailAlloc_4676_, 3, v_typeAnalysis_4662_);
lean_ctor_set(v_reuseFailAlloc_4676_, 4, v_goal_4663_);
lean_ctor_set(v_reuseFailAlloc_4676_, 5, v_snd_4657_);
lean_ctor_set_uint8(v_reuseFailAlloc_4676_, sizeof(void*)*6, v_didChange_4664_);
v___x_4669_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
lean_object* v___x_4670_; uint8_t v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4674_; 
v___x_4670_ = lean_st_ref_set(v_a_4636_, v___x_4669_);
v___x_4671_ = 0;
v___x_4672_ = lean_box(v___x_4671_);
if (v_isShared_4655_ == 0)
{
lean_ctor_set(v___x_4654_, 0, v___x_4672_);
v___x_4674_ = v___x_4654_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v___x_4672_);
v___x_4674_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
return v___x_4674_;
}
}
}
}
else
{
lean_object* v_val_4679_; lean_object* v___x_4681_; 
lean_inc_ref(v_fst_4656_);
lean_dec(v_a_4652_);
v_val_4679_ = lean_ctor_get(v_fst_4656_, 0);
lean_inc(v_val_4679_);
lean_dec_ref_known(v_fst_4656_, 1);
if (v_isShared_4655_ == 0)
{
lean_ctor_set(v___x_4654_, 0, v_val_4679_);
v___x_4681_ = v___x_4654_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v_val_4679_);
v___x_4681_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
return v___x_4681_;
}
}
}
}
else
{
lean_object* v_a_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4691_; 
v_a_4684_ = lean_ctor_get(v___x_4651_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v___x_4651_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4686_ = v___x_4651_;
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_a_4684_);
lean_dec(v___x_4651_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
lean_object* v___x_4689_; 
if (v_isShared_4687_ == 0)
{
v___x_4689_ = v___x_4686_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_a_4684_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go___boxed(lean_object* v_methods_4692_, lean_object* v_config_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_){
_start:
{
lean_object* v_res_4704_; 
v_res_4704_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_4692_, v_config_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_);
lean_dec(v_a_4702_);
lean_dec_ref(v_a_4701_);
lean_dec(v_a_4700_);
lean_dec_ref(v_a_4699_);
lean_dec(v_a_4698_);
lean_dec_ref(v_a_4697_);
lean_dec(v_a_4696_);
lean_dec_ref(v_a_4695_);
lean_dec(v_a_4694_);
return v_res_4704_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(lean_object* v_cls_4705_, lean_object* v_msg_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_){
_start:
{
lean_object* v___x_4717_; 
v___x_4717_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_4705_, v_msg_4706_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
return v___x_4717_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___boxed(lean_object* v_cls_4718_, lean_object* v_msg_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_){
_start:
{
lean_object* v_res_4730_; 
v_res_4730_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(v_cls_4718_, v_msg_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
lean_dec(v___y_4728_);
lean_dec_ref(v___y_4727_);
lean_dec(v___y_4726_);
lean_dec_ref(v___y_4725_);
lean_dec(v___y_4724_);
lean_dec_ref(v___y_4723_);
lean_dec(v___y_4722_);
lean_dec_ref(v___y_4721_);
lean_dec(v___y_4720_);
return v_res_4730_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(lean_object* v_mvarId_4731_, lean_object* v_val_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_){
_start:
{
lean_object* v___x_4743_; 
v___x_4743_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_mvarId_4731_, v_val_4732_, v___y_4739_);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___boxed(lean_object* v_mvarId_4744_, lean_object* v_val_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_){
_start:
{
lean_object* v_res_4756_; 
v_res_4756_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(v_mvarId_4744_, v_val_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_);
lean_dec(v___y_4754_);
lean_dec_ref(v___y_4753_);
lean_dec(v___y_4752_);
lean_dec_ref(v___y_4751_);
lean_dec(v___y_4750_);
lean_dec_ref(v___y_4749_);
lean_dec(v___y_4748_);
lean_dec_ref(v___y_4747_);
lean_dec(v___y_4746_);
return v_res_4756_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2(lean_object* v_upperBound_4757_, lean_object* v___x_4758_, lean_object* v_methods_4759_, lean_object* v_config_4760_, lean_object* v_inst_4761_, lean_object* v_R_4762_, lean_object* v_a_4763_, lean_object* v_b_4764_, lean_object* v_c_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_){
_start:
{
lean_object* v___x_4776_; 
v___x_4776_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg(v_upperBound_4757_, v___x_4758_, v_methods_4759_, v_config_4760_, v_a_4763_, v_b_4764_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_4777_ = _args[0];
lean_object* v___x_4778_ = _args[1];
lean_object* v_methods_4779_ = _args[2];
lean_object* v_config_4780_ = _args[3];
lean_object* v_inst_4781_ = _args[4];
lean_object* v_R_4782_ = _args[5];
lean_object* v_a_4783_ = _args[6];
lean_object* v_b_4784_ = _args[7];
lean_object* v_c_4785_ = _args[8];
lean_object* v___y_4786_ = _args[9];
lean_object* v___y_4787_ = _args[10];
lean_object* v___y_4788_ = _args[11];
lean_object* v___y_4789_ = _args[12];
lean_object* v___y_4790_ = _args[13];
lean_object* v___y_4791_ = _args[14];
lean_object* v___y_4792_ = _args[15];
lean_object* v___y_4793_ = _args[16];
lean_object* v___y_4794_ = _args[17];
lean_object* v___y_4795_ = _args[18];
_start:
{
lean_object* v_res_4796_; 
v_res_4796_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2(v_upperBound_4777_, v___x_4778_, v_methods_4779_, v_config_4780_, v_inst_4781_, v_R_4782_, v_a_4783_, v_b_4784_, v_c_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_);
lean_dec(v___y_4794_);
lean_dec_ref(v___y_4793_);
lean_dec(v___y_4792_);
lean_dec_ref(v___y_4791_);
lean_dec(v___y_4790_);
lean_dec_ref(v___y_4789_);
lean_dec(v___y_4788_);
lean_dec_ref(v___y_4787_);
lean_dec(v___y_4786_);
lean_dec_ref(v___x_4778_);
lean_dec(v_upperBound_4777_);
return v_res_4796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(lean_object* v_methods_4797_, lean_object* v_config_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_){
_start:
{
lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; 
v___x_4808_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1);
v___x_4809_ = lean_st_mk_ref(v___x_4808_);
v___x_4810_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_4797_, v_config_4798_, v___x_4809_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_);
if (lean_obj_tag(v___x_4810_) == 0)
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4819_; 
v_a_4811_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4819_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4819_ == 0)
{
v___x_4813_ = v___x_4810_;
v_isShared_4814_ = v_isSharedCheck_4819_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4810_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4819_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4815_; lean_object* v___x_4817_; 
v___x_4815_ = lean_st_ref_get(v___x_4809_);
lean_dec(v___x_4809_);
lean_dec(v___x_4815_);
if (v_isShared_4814_ == 0)
{
v___x_4817_ = v___x_4813_;
goto v_reusejp_4816_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_a_4811_);
v___x_4817_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4816_;
}
v_reusejp_4816_:
{
return v___x_4817_;
}
}
}
else
{
lean_dec(v___x_4809_);
return v___x_4810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps___boxed(lean_object* v_methods_4820_, lean_object* v_config_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_){
_start:
{
lean_object* v_res_4831_; 
v_res_4831_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(v_methods_4820_, v_config_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_);
lean_dec(v_a_4829_);
lean_dec_ref(v_a_4828_);
lean_dec(v_a_4827_);
lean_dec_ref(v_a_4826_);
lean_dec(v_a_4825_);
lean_dec_ref(v_a_4824_);
lean_dec(v_a_4823_);
lean_dec_ref(v_a_4822_);
return v_res_4831_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4833_; lean_object* v___x_4834_; 
v___x_4833_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0));
v___x_4834_ = l_Lean_stringToMessageData(v___x_4833_);
return v___x_4834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(lean_object* v_name_4835_, lean_object* v_x_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_){
_start:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4846_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1);
v___x_4847_ = l_Lean_MessageData_ofName(v_name_4835_);
v___x_4848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4848_, 0, v___x_4846_);
lean_ctor_set(v___x_4848_, 1, v___x_4847_);
v___x_4849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4849_, 0, v___x_4848_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(lean_object* v_name_4850_, lean_object* v_x_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_){
_start:
{
lean_object* v_res_4861_; 
v_res_4861_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(v_name_4850_, v_x_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec(v___y_4855_);
lean_dec_ref(v___y_4854_);
lean_dec(v___y_4853_);
lean_dec_ref(v___y_4852_);
lean_dec_ref(v_x_4851_);
return v_res_4861_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0(void){
_start:
{
lean_object* v___x_4862_; 
v___x_4862_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_4862_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1(void){
_start:
{
lean_object* v___x_4863_; lean_object* v___x_4864_; 
v___x_4863_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0);
v___x_4864_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_4863_);
return v___x_4864_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2(void){
_start:
{
lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___x_4865_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1);
v___x_4866_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_4865_);
return v___x_4866_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3(void){
_start:
{
lean_object* v___x_4867_; lean_object* v___x_4868_; 
v___x_4867_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2);
v___x_4868_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_4867_);
return v___x_4868_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4(void){
_start:
{
lean_object* v___x_4869_; lean_object* v___x_4870_; 
v___x_4869_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3);
v___x_4870_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_4869_);
return v___x_4870_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5(void){
_start:
{
lean_object* v___x_4871_; lean_object* v___x_4872_; 
v___x_4871_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4);
v___x_4872_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_4871_);
return v___x_4872_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6(void){
_start:
{
lean_object* v___x_4873_; lean_object* v___x_4874_; 
v___x_4873_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5);
v___x_4874_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_4873_);
return v___x_4874_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7(void){
_start:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4875_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6);
v___x_4876_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_4875_);
return v___x_4876_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8(void){
_start:
{
lean_object* v___x_4877_; lean_object* v___x_4878_; 
v___x_4877_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7);
v___x_4878_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_4877_);
return v___x_4878_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10(void){
_start:
{
lean_object* v___x_4880_; double v___x_4881_; 
v___x_4880_ = lean_unsigned_to_nat(1000000000u);
v___x_4881_ = lean_float_of_nat(v___x_4880_);
return v___x_4881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(lean_object* v_pass_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_){
_start:
{
lean_object* v___x_4892_; lean_object* v_toApplicative_4893_; lean_object* v_toFunctor_4894_; lean_object* v_toSeq_4895_; lean_object* v_toSeqLeft_4896_; lean_object* v_toSeqRight_4897_; lean_object* v___f_4898_; lean_object* v___f_4899_; lean_object* v___f_4900_; lean_object* v___f_4901_; lean_object* v___x_4902_; lean_object* v___f_4903_; lean_object* v___f_4904_; lean_object* v___f_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v_toApplicative_4909_; lean_object* v___x_4911_; uint8_t v_isShared_4912_; uint8_t v_isSharedCheck_5050_; 
v___x_4892_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1);
v_toApplicative_4893_ = lean_ctor_get(v___x_4892_, 0);
v_toFunctor_4894_ = lean_ctor_get(v_toApplicative_4893_, 0);
v_toSeq_4895_ = lean_ctor_get(v_toApplicative_4893_, 2);
v_toSeqLeft_4896_ = lean_ctor_get(v_toApplicative_4893_, 3);
v_toSeqRight_4897_ = lean_ctor_get(v_toApplicative_4893_, 4);
v___f_4898_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2));
v___f_4899_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3));
lean_inc_ref_n(v_toFunctor_4894_, 2);
v___f_4900_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4900_, 0, v_toFunctor_4894_);
v___f_4901_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4901_, 0, v_toFunctor_4894_);
v___x_4902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4902_, 0, v___f_4900_);
lean_ctor_set(v___x_4902_, 1, v___f_4901_);
lean_inc(v_toSeqRight_4897_);
v___f_4903_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4903_, 0, v_toSeqRight_4897_);
lean_inc(v_toSeqLeft_4896_);
v___f_4904_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4904_, 0, v_toSeqLeft_4896_);
lean_inc(v_toSeq_4895_);
v___f_4905_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4905_, 0, v_toSeq_4895_);
v___x_4906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4906_, 0, v___x_4902_);
lean_ctor_set(v___x_4906_, 1, v___f_4898_);
lean_ctor_set(v___x_4906_, 2, v___f_4905_);
lean_ctor_set(v___x_4906_, 3, v___f_4904_);
lean_ctor_set(v___x_4906_, 4, v___f_4903_);
v___x_4907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4907_, 0, v___x_4906_);
lean_ctor_set(v___x_4907_, 1, v___f_4899_);
v___x_4908_ = l_StateRefT_x27_instMonad___redArg(v___x_4907_);
v_toApplicative_4909_ = lean_ctor_get(v___x_4908_, 0);
v_isSharedCheck_5050_ = !lean_is_exclusive(v___x_4908_);
if (v_isSharedCheck_5050_ == 0)
{
lean_object* v_unused_5051_; 
v_unused_5051_ = lean_ctor_get(v___x_4908_, 1);
lean_dec(v_unused_5051_);
v___x_4911_ = v___x_4908_;
v_isShared_4912_ = v_isSharedCheck_5050_;
goto v_resetjp_4910_;
}
else
{
lean_inc(v_toApplicative_4909_);
lean_dec(v___x_4908_);
v___x_4911_ = lean_box(0);
v_isShared_4912_ = v_isSharedCheck_5050_;
goto v_resetjp_4910_;
}
v_resetjp_4910_:
{
lean_object* v_toFunctor_4913_; lean_object* v_toSeq_4914_; lean_object* v_toSeqLeft_4915_; lean_object* v_toSeqRight_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_5048_; 
v_toFunctor_4913_ = lean_ctor_get(v_toApplicative_4909_, 0);
v_toSeq_4914_ = lean_ctor_get(v_toApplicative_4909_, 2);
v_toSeqLeft_4915_ = lean_ctor_get(v_toApplicative_4909_, 3);
v_toSeqRight_4916_ = lean_ctor_get(v_toApplicative_4909_, 4);
v_isSharedCheck_5048_ = !lean_is_exclusive(v_toApplicative_4909_);
if (v_isSharedCheck_5048_ == 0)
{
lean_object* v_unused_5049_; 
v_unused_5049_ = lean_ctor_get(v_toApplicative_4909_, 1);
lean_dec(v_unused_5049_);
v___x_4918_ = v_toApplicative_4909_;
v_isShared_4919_ = v_isSharedCheck_5048_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_toSeqRight_4916_);
lean_inc(v_toSeqLeft_4915_);
lean_inc(v_toSeq_4914_);
lean_inc(v_toFunctor_4913_);
lean_dec(v_toApplicative_4909_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_5048_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
lean_object* v___f_4920_; lean_object* v___f_4921_; lean_object* v___f_4922_; lean_object* v___f_4923_; lean_object* v___x_4924_; lean_object* v___f_4925_; lean_object* v___f_4926_; lean_object* v___f_4927_; lean_object* v___x_4929_; 
v___f_4920_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4));
v___f_4921_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5));
lean_inc_ref(v_toFunctor_4913_);
v___f_4922_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4922_, 0, v_toFunctor_4913_);
v___f_4923_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4923_, 0, v_toFunctor_4913_);
v___x_4924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4924_, 0, v___f_4922_);
lean_ctor_set(v___x_4924_, 1, v___f_4923_);
v___f_4925_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4925_, 0, v_toSeqRight_4916_);
v___f_4926_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4926_, 0, v_toSeqLeft_4915_);
v___f_4927_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4927_, 0, v_toSeq_4914_);
if (v_isShared_4919_ == 0)
{
lean_ctor_set(v___x_4918_, 4, v___f_4925_);
lean_ctor_set(v___x_4918_, 3, v___f_4926_);
lean_ctor_set(v___x_4918_, 2, v___f_4927_);
lean_ctor_set(v___x_4918_, 1, v___f_4920_);
lean_ctor_set(v___x_4918_, 0, v___x_4924_);
v___x_4929_ = v___x_4918_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v___x_4924_);
lean_ctor_set(v_reuseFailAlloc_5047_, 1, v___f_4920_);
lean_ctor_set(v_reuseFailAlloc_5047_, 2, v___f_4927_);
lean_ctor_set(v_reuseFailAlloc_5047_, 3, v___f_4926_);
lean_ctor_set(v_reuseFailAlloc_5047_, 4, v___f_4925_);
v___x_4929_ = v_reuseFailAlloc_5047_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
lean_object* v___x_4931_; 
if (v_isShared_4912_ == 0)
{
lean_ctor_set(v___x_4911_, 1, v___f_4921_);
lean_ctor_set(v___x_4911_, 0, v___x_4929_);
v___x_4931_ = v___x_4911_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v___x_4929_);
lean_ctor_set(v_reuseFailAlloc_5046_, 1, v___f_4921_);
v___x_4931_ = v_reuseFailAlloc_5046_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v_toMonadRef_4938_; lean_object* v___x_4939_; lean_object* v_options_4940_; uint8_t v_hasTrace_4941_; 
v___x_4932_ = l_StateRefT_x27_instMonad___redArg(v___x_4931_);
v___x_4933_ = l_ReaderT_instMonad___redArg(v___x_4932_);
v___x_4934_ = l_StateRefT_x27_instMonad___redArg(v___x_4933_);
v___x_4935_ = l_ReaderT_instMonad___redArg(v___x_4934_);
v___x_4936_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13);
v___x_4937_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v_toMonadRef_4938_ = lean_ctor_get(v___x_4937_, 0);
v___x_4939_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8);
v_options_4940_ = lean_ctor_get(v_a_4889_, 2);
v_hasTrace_4941_ = lean_ctor_get_uint8(v_options_4940_, sizeof(void*)*1);
if (v_hasTrace_4941_ == 0)
{
lean_object* v_run_x27_4942_; lean_object* v___x_4943_; 
lean_dec_ref(v___x_4935_);
v_run_x27_4942_ = lean_ctor_get(v_pass_4882_, 1);
lean_inc_ref(v_run_x27_4942_);
lean_dec_ref(v_pass_4882_);
lean_inc(v_a_4890_);
lean_inc_ref(v_a_4889_);
lean_inc(v_a_4888_);
lean_inc_ref(v_a_4887_);
lean_inc(v_a_4886_);
lean_inc_ref(v_a_4885_);
lean_inc(v_a_4884_);
lean_inc_ref(v_a_4883_);
v___x_4943_ = lean_apply_9(v_run_x27_4942_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, lean_box(0));
return v___x_4943_;
}
else
{
lean_object* v_name_4944_; lean_object* v_run_x27_4945_; lean_object* v___x_4947_; uint8_t v_isShared_4948_; uint8_t v_isSharedCheck_5045_; 
v_name_4944_ = lean_ctor_get(v_pass_4882_, 0);
v_run_x27_4945_ = lean_ctor_get(v_pass_4882_, 1);
v_isSharedCheck_5045_ = !lean_is_exclusive(v_pass_4882_);
if (v_isSharedCheck_5045_ == 0)
{
v___x_4947_ = v_pass_4882_;
v_isShared_4948_ = v_isSharedCheck_5045_;
goto v_resetjp_4946_;
}
else
{
lean_inc(v_run_x27_4945_);
lean_inc(v_name_4944_);
lean_dec(v_pass_4882_);
v___x_4947_ = lean_box(0);
v_isShared_4948_ = v_isSharedCheck_5045_;
goto v_resetjp_4946_;
}
v_resetjp_4946_:
{
lean_object* v_inheritedTraceOptions_4949_; lean_object* v___f_4950_; lean_object* v___f_4951_; lean_object* v___f_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; uint8_t v___x_4956_; lean_object* v___y_4958_; lean_object* v___y_4959_; lean_object* v_a_4960_; lean_object* v___y_4976_; lean_object* v___y_4977_; lean_object* v_a_4978_; 
v_inheritedTraceOptions_4949_ = lean_ctor_get(v_a_4889_, 13);
v___f_4950_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 11, 1);
lean_closure_set(v___f_4950_, 0, v_name_4944_);
v___f_4951_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32);
v___f_4952_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9));
v___x_4953_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___x_4954_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_4955_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___x_4956_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4949_, v_options_4940_, v___x_4955_);
if (v___x_4956_ == 0)
{
lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; uint8_t v___x_5043_; 
v___x_5040_ = l_Lean_KVMap_instValueBool;
v___x_5041_ = l_Lean_trace_profiler;
v___x_5042_ = l_Lean_Option_get___redArg(v___x_5040_, v_options_4940_, v___x_5041_);
v___x_5043_ = lean_unbox(v___x_5042_);
lean_dec(v___x_5042_);
if (v___x_5043_ == 0)
{
lean_object* v___x_5044_; 
lean_dec_ref(v___f_4950_);
lean_del_object(v___x_4947_);
lean_dec_ref(v___x_4935_);
lean_inc(v_a_4890_);
lean_inc_ref(v_a_4889_);
lean_inc(v_a_4888_);
lean_inc_ref(v_a_4887_);
lean_inc(v_a_4886_);
lean_inc_ref(v_a_4885_);
lean_inc(v_a_4884_);
lean_inc_ref(v_a_4883_);
v___x_5044_ = lean_apply_9(v_run_x27_4945_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, lean_box(0));
return v___x_5044_;
}
else
{
goto v___jp_4988_;
}
}
else
{
goto v___jp_4988_;
}
v___jp_4957_:
{
lean_object* v___x_4961_; double v___x_4962_; double v___x_4963_; double v___x_4964_; double v___x_4965_; double v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4970_; 
v___x_4961_ = lean_io_mono_nanos_now();
v___x_4962_ = lean_float_of_nat(v___y_4959_);
v___x_4963_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10);
v___x_4964_ = lean_float_div(v___x_4962_, v___x_4963_);
v___x_4965_ = lean_float_of_nat(v___x_4961_);
v___x_4966_ = lean_float_div(v___x_4965_, v___x_4963_);
v___x_4967_ = lean_box_float(v___x_4964_);
v___x_4968_ = lean_box_float(v___x_4966_);
if (v_isShared_4948_ == 0)
{
lean_ctor_set(v___x_4947_, 1, v___x_4968_);
lean_ctor_set(v___x_4947_, 0, v___x_4967_);
v___x_4970_ = v___x_4947_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v___x_4967_);
lean_ctor_set(v_reuseFailAlloc_4974_, 1, v___x_4968_);
v___x_4970_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
lean_object* v___x_4971_; lean_object* v___x_16945__overap_4972_; lean_object* v___x_4973_; 
v___x_4971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4971_, 0, v_a_4960_);
lean_ctor_set(v___x_4971_, 1, v___x_4970_);
lean_inc_ref(v_toMonadRef_4938_);
v___x_16945__overap_4972_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_4935_, v___x_4936_, v_toMonadRef_4938_, v___f_4951_, lean_box(0), v___x_4939_, v___f_4952_, v___x_4953_, v_hasTrace_4941_, v___x_4954_, v_options_4940_, v___x_4956_, v___y_4958_, v___f_4950_, v___x_4971_);
lean_inc(v_a_4890_);
lean_inc_ref(v_a_4889_);
lean_inc(v_a_4888_);
lean_inc_ref(v_a_4887_);
lean_inc(v_a_4886_);
lean_inc_ref(v_a_4885_);
lean_inc(v_a_4884_);
lean_inc_ref(v_a_4883_);
v___x_4973_ = lean_apply_9(v___x_16945__overap_4972_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, lean_box(0));
return v___x_4973_;
}
}
v___jp_4975_:
{
lean_object* v___x_4979_; double v___x_4980_; double v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_16966__overap_4986_; lean_object* v___x_4987_; 
v___x_4979_ = lean_io_get_num_heartbeats();
v___x_4980_ = lean_float_of_nat(v___y_4977_);
v___x_4981_ = lean_float_of_nat(v___x_4979_);
v___x_4982_ = lean_box_float(v___x_4980_);
v___x_4983_ = lean_box_float(v___x_4981_);
v___x_4984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4984_, 0, v___x_4982_);
lean_ctor_set(v___x_4984_, 1, v___x_4983_);
v___x_4985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4985_, 0, v_a_4978_);
lean_ctor_set(v___x_4985_, 1, v___x_4984_);
lean_inc_ref(v_toMonadRef_4938_);
v___x_16966__overap_4986_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_4935_, v___x_4936_, v_toMonadRef_4938_, v___f_4951_, lean_box(0), v___x_4939_, v___f_4952_, v___x_4953_, v_hasTrace_4941_, v___x_4954_, v_options_4940_, v___x_4956_, v___y_4976_, v___f_4950_, v___x_4985_);
lean_inc(v_a_4890_);
lean_inc_ref(v_a_4889_);
lean_inc(v_a_4888_);
lean_inc_ref(v_a_4887_);
lean_inc(v_a_4886_);
lean_inc_ref(v_a_4885_);
lean_inc(v_a_4884_);
lean_inc_ref(v_a_4883_);
v___x_4987_ = lean_apply_9(v___x_16966__overap_4986_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, lean_box(0));
return v___x_4987_;
}
v___jp_4988_:
{
lean_object* v___x_16922__overap_4989_; lean_object* v___x_4990_; 
lean_inc_ref(v___x_4935_);
v___x_16922__overap_4989_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_4935_, v___x_4936_);
lean_inc(v_a_4890_);
lean_inc_ref(v_a_4889_);
lean_inc(v_a_4888_);
lean_inc_ref(v_a_4887_);
lean_inc(v_a_4886_);
lean_inc_ref(v_a_4885_);
lean_inc(v_a_4884_);
lean_inc_ref(v_a_4883_);
v___x_4990_ = lean_apply_9(v___x_16922__overap_4989_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, lean_box(0));
if (lean_obj_tag(v___x_4990_) == 0)
{
lean_object* v_a_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; uint8_t v___x_4995_; 
v_a_4991_ = lean_ctor_get(v___x_4990_, 0);
lean_inc(v_a_4991_);
lean_dec_ref_known(v___x_4990_, 1);
v___x_4992_ = l_Lean_KVMap_instValueBool;
v___x_4993_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4994_ = l_Lean_Option_get___redArg(v___x_4992_, v_options_4940_, v___x_4993_);
v___x_4995_ = lean_unbox(v___x_4994_);
lean_dec(v___x_4994_);
if (v___x_4995_ == 0)
{
lean_object* v___x_4996_; lean_object* v___x_4997_; 
v___x_4996_ = lean_io_mono_nanos_now();
lean_inc(v_a_4890_);
lean_inc_ref(v_a_4889_);
lean_inc(v_a_4888_);
lean_inc_ref(v_a_4887_);
lean_inc(v_a_4886_);
lean_inc_ref(v_a_4885_);
lean_inc(v_a_4884_);
lean_inc_ref(v_a_4883_);
v___x_4997_ = lean_apply_9(v_run_x27_4945_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, lean_box(0));
if (lean_obj_tag(v___x_4997_) == 0)
{
lean_object* v_a_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5005_; 
v_a_4998_ = lean_ctor_get(v___x_4997_, 0);
v_isSharedCheck_5005_ = !lean_is_exclusive(v___x_4997_);
if (v_isSharedCheck_5005_ == 0)
{
v___x_5000_ = v___x_4997_;
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_a_4998_);
lean_dec(v___x_4997_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
v_resetjp_4999_:
{
lean_object* v___x_5003_; 
if (v_isShared_5001_ == 0)
{
lean_ctor_set_tag(v___x_5000_, 1);
v___x_5003_ = v___x_5000_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v_a_4998_);
v___x_5003_ = v_reuseFailAlloc_5004_;
goto v_reusejp_5002_;
}
v_reusejp_5002_:
{
v___y_4958_ = v_a_4991_;
v___y_4959_ = v___x_4996_;
v_a_4960_ = v___x_5003_;
goto v___jp_4957_;
}
}
}
else
{
lean_object* v_a_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5013_; 
v_a_5006_ = lean_ctor_get(v___x_4997_, 0);
v_isSharedCheck_5013_ = !lean_is_exclusive(v___x_4997_);
if (v_isSharedCheck_5013_ == 0)
{
v___x_5008_ = v___x_4997_;
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_a_5006_);
lean_dec(v___x_4997_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v___x_5011_; 
if (v_isShared_5009_ == 0)
{
lean_ctor_set_tag(v___x_5008_, 0);
v___x_5011_ = v___x_5008_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_a_5006_);
v___x_5011_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
v___y_4958_ = v_a_4991_;
v___y_4959_ = v___x_4996_;
v_a_4960_ = v___x_5011_;
goto v___jp_4957_;
}
}
}
}
else
{
lean_object* v___x_5014_; lean_object* v___x_5015_; 
lean_del_object(v___x_4947_);
v___x_5014_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4890_);
lean_inc_ref(v_a_4889_);
lean_inc(v_a_4888_);
lean_inc_ref(v_a_4887_);
lean_inc(v_a_4886_);
lean_inc_ref(v_a_4885_);
lean_inc(v_a_4884_);
lean_inc_ref(v_a_4883_);
v___x_5015_ = lean_apply_9(v_run_x27_4945_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, lean_box(0));
if (lean_obj_tag(v___x_5015_) == 0)
{
lean_object* v_a_5016_; lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5023_; 
v_a_5016_ = lean_ctor_get(v___x_5015_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v___x_5015_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_5018_ = v___x_5015_;
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
else
{
lean_inc(v_a_5016_);
lean_dec(v___x_5015_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
lean_object* v___x_5021_; 
if (v_isShared_5019_ == 0)
{
lean_ctor_set_tag(v___x_5018_, 1);
v___x_5021_ = v___x_5018_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_a_5016_);
v___x_5021_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
v___y_4976_ = v_a_4991_;
v___y_4977_ = v___x_5014_;
v_a_4978_ = v___x_5021_;
goto v___jp_4975_;
}
}
}
else
{
lean_object* v_a_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5031_; 
v_a_5024_ = lean_ctor_get(v___x_5015_, 0);
v_isSharedCheck_5031_ = !lean_is_exclusive(v___x_5015_);
if (v_isSharedCheck_5031_ == 0)
{
v___x_5026_ = v___x_5015_;
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_a_5024_);
lean_dec(v___x_5015_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v___x_5029_; 
if (v_isShared_5027_ == 0)
{
lean_ctor_set_tag(v___x_5026_, 0);
v___x_5029_ = v___x_5026_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v_a_5024_);
v___x_5029_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
v___y_4976_ = v_a_4991_;
v___y_4977_ = v___x_5014_;
v_a_4978_ = v___x_5029_;
goto v___jp_4975_;
}
}
}
}
}
else
{
lean_object* v_a_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5039_; 
lean_dec_ref(v___f_4950_);
lean_del_object(v___x_4947_);
lean_dec_ref(v_run_x27_4945_);
lean_dec_ref(v___x_4935_);
v_a_5032_ = lean_ctor_get(v___x_4990_, 0);
v_isSharedCheck_5039_ = !lean_is_exclusive(v___x_4990_);
if (v_isSharedCheck_5039_ == 0)
{
v___x_5034_ = v___x_4990_;
v_isShared_5035_ = v_isSharedCheck_5039_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_a_5032_);
lean_dec(v___x_4990_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5039_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
lean_object* v___x_5037_; 
if (v_isShared_5035_ == 0)
{
v___x_5037_ = v___x_5034_;
goto v_reusejp_5036_;
}
else
{
lean_object* v_reuseFailAlloc_5038_; 
v_reuseFailAlloc_5038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5038_, 0, v_a_5032_);
v___x_5037_ = v_reuseFailAlloc_5038_;
goto v_reusejp_5036_;
}
v_reusejp_5036_:
{
return v___x_5037_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___boxed(lean_object* v_pass_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_){
_start:
{
lean_object* v_res_5062_; 
v_res_5062_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(v_pass_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_);
lean_dec(v_a_5060_);
lean_dec_ref(v_a_5059_);
lean_dec(v_a_5058_);
lean_dec_ref(v_a_5057_);
lean_dec(v_a_5056_);
lean_dec_ref(v_a_5055_);
lean_dec(v_a_5054_);
lean_dec_ref(v_a_5053_);
return v_res_5062_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v___x_5063_ = lean_unsigned_to_nat(32u);
v___x_5064_ = lean_mk_empty_array_with_capacity(v___x_5063_);
v___x_5065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5065_, 0, v___x_5064_);
return v___x_5065_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; 
v___x_5066_ = ((size_t)5ULL);
v___x_5067_ = lean_unsigned_to_nat(0u);
v___x_5068_ = lean_unsigned_to_nat(32u);
v___x_5069_ = lean_mk_empty_array_with_capacity(v___x_5068_);
v___x_5070_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0);
v___x_5071_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5071_, 0, v___x_5070_);
lean_ctor_set(v___x_5071_, 1, v___x_5069_);
lean_ctor_set(v___x_5071_, 2, v___x_5067_);
lean_ctor_set(v___x_5071_, 3, v___x_5067_);
lean_ctor_set_usize(v___x_5071_, 4, v___x_5066_);
return v___x_5071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(lean_object* v___y_5072_){
_start:
{
lean_object* v___x_5074_; lean_object* v_traceState_5075_; lean_object* v_traces_5076_; lean_object* v___x_5077_; lean_object* v_traceState_5078_; lean_object* v_env_5079_; lean_object* v_nextMacroScope_5080_; lean_object* v_ngen_5081_; lean_object* v_auxDeclNGen_5082_; lean_object* v_cache_5083_; lean_object* v_messages_5084_; lean_object* v_infoState_5085_; lean_object* v_snapshotTasks_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5105_; 
v___x_5074_ = lean_st_ref_get(v___y_5072_);
v_traceState_5075_ = lean_ctor_get(v___x_5074_, 4);
lean_inc_ref(v_traceState_5075_);
lean_dec(v___x_5074_);
v_traces_5076_ = lean_ctor_get(v_traceState_5075_, 0);
lean_inc_ref(v_traces_5076_);
lean_dec_ref(v_traceState_5075_);
v___x_5077_ = lean_st_ref_take(v___y_5072_);
v_traceState_5078_ = lean_ctor_get(v___x_5077_, 4);
v_env_5079_ = lean_ctor_get(v___x_5077_, 0);
v_nextMacroScope_5080_ = lean_ctor_get(v___x_5077_, 1);
v_ngen_5081_ = lean_ctor_get(v___x_5077_, 2);
v_auxDeclNGen_5082_ = lean_ctor_get(v___x_5077_, 3);
v_cache_5083_ = lean_ctor_get(v___x_5077_, 5);
v_messages_5084_ = lean_ctor_get(v___x_5077_, 6);
v_infoState_5085_ = lean_ctor_get(v___x_5077_, 7);
v_snapshotTasks_5086_ = lean_ctor_get(v___x_5077_, 8);
v_isSharedCheck_5105_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_5088_ = v___x_5077_;
v_isShared_5089_ = v_isSharedCheck_5105_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_snapshotTasks_5086_);
lean_inc(v_infoState_5085_);
lean_inc(v_messages_5084_);
lean_inc(v_cache_5083_);
lean_inc(v_traceState_5078_);
lean_inc(v_auxDeclNGen_5082_);
lean_inc(v_ngen_5081_);
lean_inc(v_nextMacroScope_5080_);
lean_inc(v_env_5079_);
lean_dec(v___x_5077_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5105_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
uint64_t v_tid_5090_; lean_object* v___x_5092_; uint8_t v_isShared_5093_; uint8_t v_isSharedCheck_5103_; 
v_tid_5090_ = lean_ctor_get_uint64(v_traceState_5078_, sizeof(void*)*1);
v_isSharedCheck_5103_ = !lean_is_exclusive(v_traceState_5078_);
if (v_isSharedCheck_5103_ == 0)
{
lean_object* v_unused_5104_; 
v_unused_5104_ = lean_ctor_get(v_traceState_5078_, 0);
lean_dec(v_unused_5104_);
v___x_5092_ = v_traceState_5078_;
v_isShared_5093_ = v_isSharedCheck_5103_;
goto v_resetjp_5091_;
}
else
{
lean_dec(v_traceState_5078_);
v___x_5092_ = lean_box(0);
v_isShared_5093_ = v_isSharedCheck_5103_;
goto v_resetjp_5091_;
}
v_resetjp_5091_:
{
lean_object* v___x_5094_; lean_object* v___x_5096_; 
v___x_5094_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1);
if (v_isShared_5093_ == 0)
{
lean_ctor_set(v___x_5092_, 0, v___x_5094_);
v___x_5096_ = v___x_5092_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v___x_5094_);
lean_ctor_set_uint64(v_reuseFailAlloc_5102_, sizeof(void*)*1, v_tid_5090_);
v___x_5096_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
lean_object* v___x_5098_; 
if (v_isShared_5089_ == 0)
{
lean_ctor_set(v___x_5088_, 4, v___x_5096_);
v___x_5098_ = v___x_5088_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v_env_5079_);
lean_ctor_set(v_reuseFailAlloc_5101_, 1, v_nextMacroScope_5080_);
lean_ctor_set(v_reuseFailAlloc_5101_, 2, v_ngen_5081_);
lean_ctor_set(v_reuseFailAlloc_5101_, 3, v_auxDeclNGen_5082_);
lean_ctor_set(v_reuseFailAlloc_5101_, 4, v___x_5096_);
lean_ctor_set(v_reuseFailAlloc_5101_, 5, v_cache_5083_);
lean_ctor_set(v_reuseFailAlloc_5101_, 6, v_messages_5084_);
lean_ctor_set(v_reuseFailAlloc_5101_, 7, v_infoState_5085_);
lean_ctor_set(v_reuseFailAlloc_5101_, 8, v_snapshotTasks_5086_);
v___x_5098_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
lean_object* v___x_5099_; lean_object* v___x_5100_; 
v___x_5099_ = lean_st_ref_set(v___y_5072_, v___x_5098_);
v___x_5100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5100_, 0, v_traces_5076_);
return v___x_5100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___boxed(lean_object* v___y_5106_, lean_object* v___y_5107_){
_start:
{
lean_object* v_res_5108_; 
v_res_5108_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_5106_);
lean_dec(v___y_5106_);
return v_res_5108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_){
_start:
{
lean_object* v___x_5118_; 
v___x_5118_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_5116_);
return v___x_5118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___boxed(lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_){
_start:
{
lean_object* v_res_5128_; 
v_res_5128_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_);
lean_dec(v___y_5126_);
lean_dec_ref(v___y_5125_);
lean_dec(v___y_5124_);
lean_dec_ref(v___y_5123_);
lean_dec(v___y_5122_);
lean_dec_ref(v___y_5121_);
lean_dec(v___y_5120_);
lean_dec_ref(v___y_5119_);
return v_res_5128_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(lean_object* v_opts_5129_, lean_object* v_opt_5130_){
_start:
{
lean_object* v_name_5131_; lean_object* v_defValue_5132_; lean_object* v_map_5133_; lean_object* v___x_5134_; 
v_name_5131_ = lean_ctor_get(v_opt_5130_, 0);
v_defValue_5132_ = lean_ctor_get(v_opt_5130_, 1);
v_map_5133_ = lean_ctor_get(v_opts_5129_, 0);
v___x_5134_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5133_, v_name_5131_);
if (lean_obj_tag(v___x_5134_) == 0)
{
uint8_t v___x_5135_; 
v___x_5135_ = lean_unbox(v_defValue_5132_);
return v___x_5135_;
}
else
{
lean_object* v_val_5136_; 
v_val_5136_ = lean_ctor_get(v___x_5134_, 0);
lean_inc(v_val_5136_);
lean_dec_ref_known(v___x_5134_, 1);
if (lean_obj_tag(v_val_5136_) == 1)
{
uint8_t v_v_5137_; 
v_v_5137_ = lean_ctor_get_uint8(v_val_5136_, 0);
lean_dec_ref_known(v_val_5136_, 0);
return v_v_5137_;
}
else
{
uint8_t v___x_5138_; 
lean_dec(v_val_5136_);
v___x_5138_ = lean_unbox(v_defValue_5132_);
return v___x_5138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2___boxed(lean_object* v_opts_5139_, lean_object* v_opt_5140_){
_start:
{
uint8_t v_res_5141_; lean_object* v_r_5142_; 
v_res_5141_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_5139_, v_opt_5140_);
lean_dec_ref(v_opt_5140_);
lean_dec_ref(v_opts_5139_);
v_r_5142_ = lean_box(v_res_5141_);
return v_r_5142_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(lean_object* v_cls_5143_, lean_object* v_msg_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_){
_start:
{
lean_object* v_ref_5150_; lean_object* v___x_5151_; lean_object* v_a_5152_; lean_object* v___x_5154_; uint8_t v_isShared_5155_; uint8_t v_isSharedCheck_5196_; 
v_ref_5150_ = lean_ctor_get(v___y_5147_, 5);
v___x_5151_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_5144_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
v_a_5152_ = lean_ctor_get(v___x_5151_, 0);
v_isSharedCheck_5196_ = !lean_is_exclusive(v___x_5151_);
if (v_isSharedCheck_5196_ == 0)
{
v___x_5154_ = v___x_5151_;
v_isShared_5155_ = v_isSharedCheck_5196_;
goto v_resetjp_5153_;
}
else
{
lean_inc(v_a_5152_);
lean_dec(v___x_5151_);
v___x_5154_ = lean_box(0);
v_isShared_5155_ = v_isSharedCheck_5196_;
goto v_resetjp_5153_;
}
v_resetjp_5153_:
{
lean_object* v___x_5156_; lean_object* v_traceState_5157_; lean_object* v_env_5158_; lean_object* v_nextMacroScope_5159_; lean_object* v_ngen_5160_; lean_object* v_auxDeclNGen_5161_; lean_object* v_cache_5162_; lean_object* v_messages_5163_; lean_object* v_infoState_5164_; lean_object* v_snapshotTasks_5165_; lean_object* v___x_5167_; uint8_t v_isShared_5168_; uint8_t v_isSharedCheck_5195_; 
v___x_5156_ = lean_st_ref_take(v___y_5148_);
v_traceState_5157_ = lean_ctor_get(v___x_5156_, 4);
v_env_5158_ = lean_ctor_get(v___x_5156_, 0);
v_nextMacroScope_5159_ = lean_ctor_get(v___x_5156_, 1);
v_ngen_5160_ = lean_ctor_get(v___x_5156_, 2);
v_auxDeclNGen_5161_ = lean_ctor_get(v___x_5156_, 3);
v_cache_5162_ = lean_ctor_get(v___x_5156_, 5);
v_messages_5163_ = lean_ctor_get(v___x_5156_, 6);
v_infoState_5164_ = lean_ctor_get(v___x_5156_, 7);
v_snapshotTasks_5165_ = lean_ctor_get(v___x_5156_, 8);
v_isSharedCheck_5195_ = !lean_is_exclusive(v___x_5156_);
if (v_isSharedCheck_5195_ == 0)
{
v___x_5167_ = v___x_5156_;
v_isShared_5168_ = v_isSharedCheck_5195_;
goto v_resetjp_5166_;
}
else
{
lean_inc(v_snapshotTasks_5165_);
lean_inc(v_infoState_5164_);
lean_inc(v_messages_5163_);
lean_inc(v_cache_5162_);
lean_inc(v_traceState_5157_);
lean_inc(v_auxDeclNGen_5161_);
lean_inc(v_ngen_5160_);
lean_inc(v_nextMacroScope_5159_);
lean_inc(v_env_5158_);
lean_dec(v___x_5156_);
v___x_5167_ = lean_box(0);
v_isShared_5168_ = v_isSharedCheck_5195_;
goto v_resetjp_5166_;
}
v_resetjp_5166_:
{
uint64_t v_tid_5169_; lean_object* v_traces_5170_; lean_object* v___x_5172_; uint8_t v_isShared_5173_; uint8_t v_isSharedCheck_5194_; 
v_tid_5169_ = lean_ctor_get_uint64(v_traceState_5157_, sizeof(void*)*1);
v_traces_5170_ = lean_ctor_get(v_traceState_5157_, 0);
v_isSharedCheck_5194_ = !lean_is_exclusive(v_traceState_5157_);
if (v_isSharedCheck_5194_ == 0)
{
v___x_5172_ = v_traceState_5157_;
v_isShared_5173_ = v_isSharedCheck_5194_;
goto v_resetjp_5171_;
}
else
{
lean_inc(v_traces_5170_);
lean_dec(v_traceState_5157_);
v___x_5172_ = lean_box(0);
v_isShared_5173_ = v_isSharedCheck_5194_;
goto v_resetjp_5171_;
}
v_resetjp_5171_:
{
lean_object* v___x_5174_; double v___x_5175_; uint8_t v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5184_; 
v___x_5174_ = lean_box(0);
v___x_5175_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_5176_ = 0;
v___x_5177_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5178_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5178_, 0, v_cls_5143_);
lean_ctor_set(v___x_5178_, 1, v___x_5174_);
lean_ctor_set(v___x_5178_, 2, v___x_5177_);
lean_ctor_set_float(v___x_5178_, sizeof(void*)*3, v___x_5175_);
lean_ctor_set_float(v___x_5178_, sizeof(void*)*3 + 8, v___x_5175_);
lean_ctor_set_uint8(v___x_5178_, sizeof(void*)*3 + 16, v___x_5176_);
v___x_5179_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_5180_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5180_, 0, v___x_5178_);
lean_ctor_set(v___x_5180_, 1, v_a_5152_);
lean_ctor_set(v___x_5180_, 2, v___x_5179_);
lean_inc(v_ref_5150_);
v___x_5181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5181_, 0, v_ref_5150_);
lean_ctor_set(v___x_5181_, 1, v___x_5180_);
v___x_5182_ = l_Lean_PersistentArray_push___redArg(v_traces_5170_, v___x_5181_);
if (v_isShared_5173_ == 0)
{
lean_ctor_set(v___x_5172_, 0, v___x_5182_);
v___x_5184_ = v___x_5172_;
goto v_reusejp_5183_;
}
else
{
lean_object* v_reuseFailAlloc_5193_; 
v_reuseFailAlloc_5193_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5193_, 0, v___x_5182_);
lean_ctor_set_uint64(v_reuseFailAlloc_5193_, sizeof(void*)*1, v_tid_5169_);
v___x_5184_ = v_reuseFailAlloc_5193_;
goto v_reusejp_5183_;
}
v_reusejp_5183_:
{
lean_object* v___x_5186_; 
if (v_isShared_5168_ == 0)
{
lean_ctor_set(v___x_5167_, 4, v___x_5184_);
v___x_5186_ = v___x_5167_;
goto v_reusejp_5185_;
}
else
{
lean_object* v_reuseFailAlloc_5192_; 
v_reuseFailAlloc_5192_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5192_, 0, v_env_5158_);
lean_ctor_set(v_reuseFailAlloc_5192_, 1, v_nextMacroScope_5159_);
lean_ctor_set(v_reuseFailAlloc_5192_, 2, v_ngen_5160_);
lean_ctor_set(v_reuseFailAlloc_5192_, 3, v_auxDeclNGen_5161_);
lean_ctor_set(v_reuseFailAlloc_5192_, 4, v___x_5184_);
lean_ctor_set(v_reuseFailAlloc_5192_, 5, v_cache_5162_);
lean_ctor_set(v_reuseFailAlloc_5192_, 6, v_messages_5163_);
lean_ctor_set(v_reuseFailAlloc_5192_, 7, v_infoState_5164_);
lean_ctor_set(v_reuseFailAlloc_5192_, 8, v_snapshotTasks_5165_);
v___x_5186_ = v_reuseFailAlloc_5192_;
goto v_reusejp_5185_;
}
v_reusejp_5185_:
{
lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5190_; 
v___x_5187_ = lean_st_ref_set(v___y_5148_, v___x_5186_);
v___x_5188_ = lean_box(0);
if (v_isShared_5155_ == 0)
{
lean_ctor_set(v___x_5154_, 0, v___x_5188_);
v___x_5190_ = v___x_5154_;
goto v_reusejp_5189_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v___x_5188_);
v___x_5190_ = v_reuseFailAlloc_5191_;
goto v_reusejp_5189_;
}
v_reusejp_5189_:
{
return v___x_5190_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg___boxed(lean_object* v_cls_5197_, lean_object* v_msg_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_){
_start:
{
lean_object* v_res_5204_; 
v_res_5204_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_5197_, v_msg_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_);
lean_dec(v___y_5202_);
lean_dec_ref(v___y_5201_);
lean_dec(v___y_5200_);
lean_dec_ref(v___y_5199_);
return v_res_5204_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(lean_object* v_e_5205_){
_start:
{
if (lean_obj_tag(v_e_5205_) == 0)
{
uint8_t v___x_5206_; 
v___x_5206_ = 2;
return v___x_5206_;
}
else
{
lean_object* v_a_5207_; uint8_t v___x_5208_; 
v_a_5207_ = lean_ctor_get(v_e_5205_, 0);
v___x_5208_ = lean_unbox(v_a_5207_);
if (v___x_5208_ == 0)
{
uint8_t v___x_5209_; 
v___x_5209_ = 1;
return v___x_5209_;
}
else
{
uint8_t v___x_5210_; 
v___x_5210_ = 0;
return v___x_5210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5___boxed(lean_object* v_e_5211_){
_start:
{
uint8_t v_res_5212_; lean_object* v_r_5213_; 
v_res_5212_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_e_5211_);
lean_dec_ref(v_e_5211_);
v_r_5213_ = lean_box(v_res_5212_);
return v_r_5213_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(lean_object* v_x_5214_){
_start:
{
if (lean_obj_tag(v_x_5214_) == 0)
{
lean_object* v_a_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5223_; 
v_a_5216_ = lean_ctor_get(v_x_5214_, 0);
v_isSharedCheck_5223_ = !lean_is_exclusive(v_x_5214_);
if (v_isSharedCheck_5223_ == 0)
{
v___x_5218_ = v_x_5214_;
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_a_5216_);
lean_dec(v_x_5214_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
lean_object* v___x_5221_; 
if (v_isShared_5219_ == 0)
{
lean_ctor_set_tag(v___x_5218_, 1);
v___x_5221_ = v___x_5218_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5222_; 
v_reuseFailAlloc_5222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5222_, 0, v_a_5216_);
v___x_5221_ = v_reuseFailAlloc_5222_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
return v___x_5221_;
}
}
}
else
{
lean_object* v_a_5224_; lean_object* v___x_5226_; uint8_t v_isShared_5227_; uint8_t v_isSharedCheck_5231_; 
v_a_5224_ = lean_ctor_get(v_x_5214_, 0);
v_isSharedCheck_5231_ = !lean_is_exclusive(v_x_5214_);
if (v_isSharedCheck_5231_ == 0)
{
v___x_5226_ = v_x_5214_;
v_isShared_5227_ = v_isSharedCheck_5231_;
goto v_resetjp_5225_;
}
else
{
lean_inc(v_a_5224_);
lean_dec(v_x_5214_);
v___x_5226_ = lean_box(0);
v_isShared_5227_ = v_isSharedCheck_5231_;
goto v_resetjp_5225_;
}
v_resetjp_5225_:
{
lean_object* v___x_5229_; 
if (v_isShared_5227_ == 0)
{
lean_ctor_set_tag(v___x_5226_, 0);
v___x_5229_ = v___x_5226_;
goto v_reusejp_5228_;
}
else
{
lean_object* v_reuseFailAlloc_5230_; 
v_reuseFailAlloc_5230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5230_, 0, v_a_5224_);
v___x_5229_ = v_reuseFailAlloc_5230_;
goto v_reusejp_5228_;
}
v_reusejp_5228_:
{
return v___x_5229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg___boxed(lean_object* v_x_5232_, lean_object* v___y_5233_){
_start:
{
lean_object* v_res_5234_; 
v_res_5234_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_5232_);
return v_res_5234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(lean_object* v_opts_5235_, lean_object* v_opt_5236_){
_start:
{
lean_object* v_name_5237_; lean_object* v_defValue_5238_; lean_object* v_map_5239_; lean_object* v___x_5240_; 
v_name_5237_ = lean_ctor_get(v_opt_5236_, 0);
v_defValue_5238_ = lean_ctor_get(v_opt_5236_, 1);
v_map_5239_ = lean_ctor_get(v_opts_5235_, 0);
v___x_5240_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5239_, v_name_5237_);
if (lean_obj_tag(v___x_5240_) == 0)
{
lean_inc(v_defValue_5238_);
return v_defValue_5238_;
}
else
{
lean_object* v_val_5241_; 
v_val_5241_ = lean_ctor_get(v___x_5240_, 0);
lean_inc(v_val_5241_);
lean_dec_ref_known(v___x_5240_, 1);
if (lean_obj_tag(v_val_5241_) == 3)
{
lean_object* v_v_5242_; 
v_v_5242_ = lean_ctor_get(v_val_5241_, 0);
lean_inc(v_v_5242_);
lean_dec_ref_known(v_val_5241_, 1);
return v_v_5242_;
}
else
{
lean_dec(v_val_5241_);
lean_inc(v_defValue_5238_);
return v_defValue_5238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6___boxed(lean_object* v_opts_5243_, lean_object* v_opt_5244_){
_start:
{
lean_object* v_res_5245_; 
v_res_5245_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_5243_, v_opt_5244_);
lean_dec_ref(v_opt_5244_);
lean_dec_ref(v_opts_5243_);
return v_res_5245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(size_t v_sz_5246_, size_t v_i_5247_, lean_object* v_bs_5248_){
_start:
{
uint8_t v___x_5249_; 
v___x_5249_ = lean_usize_dec_lt(v_i_5247_, v_sz_5246_);
if (v___x_5249_ == 0)
{
return v_bs_5248_;
}
else
{
lean_object* v_v_5250_; lean_object* v_msg_5251_; lean_object* v___x_5252_; lean_object* v_bs_x27_5253_; size_t v___x_5254_; size_t v___x_5255_; lean_object* v___x_5256_; 
v_v_5250_ = lean_array_uget_borrowed(v_bs_5248_, v_i_5247_);
v_msg_5251_ = lean_ctor_get(v_v_5250_, 1);
lean_inc_ref(v_msg_5251_);
v___x_5252_ = lean_unsigned_to_nat(0u);
v_bs_x27_5253_ = lean_array_uset(v_bs_5248_, v_i_5247_, v___x_5252_);
v___x_5254_ = ((size_t)1ULL);
v___x_5255_ = lean_usize_add(v_i_5247_, v___x_5254_);
v___x_5256_ = lean_array_uset(v_bs_x27_5253_, v_i_5247_, v_msg_5251_);
v_i_5247_ = v___x_5255_;
v_bs_5248_ = v___x_5256_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_5258_, lean_object* v_i_5259_, lean_object* v_bs_5260_){
_start:
{
size_t v_sz_boxed_5261_; size_t v_i_boxed_5262_; lean_object* v_res_5263_; 
v_sz_boxed_5261_ = lean_unbox_usize(v_sz_5258_);
lean_dec(v_sz_5258_);
v_i_boxed_5262_ = lean_unbox_usize(v_i_5259_);
lean_dec(v_i_5259_);
v_res_5263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_boxed_5261_, v_i_boxed_5262_, v_bs_5260_);
return v_res_5263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(lean_object* v_oldTraces_5264_, lean_object* v_data_5265_, lean_object* v_ref_5266_, lean_object* v_msg_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_){
_start:
{
lean_object* v_fileName_5273_; lean_object* v_fileMap_5274_; lean_object* v_options_5275_; lean_object* v_currRecDepth_5276_; lean_object* v_maxRecDepth_5277_; lean_object* v_ref_5278_; lean_object* v_currNamespace_5279_; lean_object* v_openDecls_5280_; lean_object* v_initHeartbeats_5281_; lean_object* v_maxHeartbeats_5282_; lean_object* v_quotContext_5283_; lean_object* v_currMacroScope_5284_; uint8_t v_diag_5285_; lean_object* v_cancelTk_x3f_5286_; uint8_t v_suppressElabErrors_5287_; lean_object* v_inheritedTraceOptions_5288_; lean_object* v___x_5289_; lean_object* v_traceState_5290_; lean_object* v_traces_5291_; lean_object* v_ref_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; size_t v_sz_5295_; size_t v___x_5296_; lean_object* v___x_5297_; lean_object* v_msg_5298_; lean_object* v___x_5299_; lean_object* v_a_5300_; lean_object* v___x_5302_; uint8_t v_isShared_5303_; uint8_t v_isSharedCheck_5337_; 
v_fileName_5273_ = lean_ctor_get(v___y_5270_, 0);
v_fileMap_5274_ = lean_ctor_get(v___y_5270_, 1);
v_options_5275_ = lean_ctor_get(v___y_5270_, 2);
v_currRecDepth_5276_ = lean_ctor_get(v___y_5270_, 3);
v_maxRecDepth_5277_ = lean_ctor_get(v___y_5270_, 4);
v_ref_5278_ = lean_ctor_get(v___y_5270_, 5);
v_currNamespace_5279_ = lean_ctor_get(v___y_5270_, 6);
v_openDecls_5280_ = lean_ctor_get(v___y_5270_, 7);
v_initHeartbeats_5281_ = lean_ctor_get(v___y_5270_, 8);
v_maxHeartbeats_5282_ = lean_ctor_get(v___y_5270_, 9);
v_quotContext_5283_ = lean_ctor_get(v___y_5270_, 10);
v_currMacroScope_5284_ = lean_ctor_get(v___y_5270_, 11);
v_diag_5285_ = lean_ctor_get_uint8(v___y_5270_, sizeof(void*)*14);
v_cancelTk_x3f_5286_ = lean_ctor_get(v___y_5270_, 12);
v_suppressElabErrors_5287_ = lean_ctor_get_uint8(v___y_5270_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5288_ = lean_ctor_get(v___y_5270_, 13);
v___x_5289_ = lean_st_ref_get(v___y_5271_);
v_traceState_5290_ = lean_ctor_get(v___x_5289_, 4);
lean_inc_ref(v_traceState_5290_);
lean_dec(v___x_5289_);
v_traces_5291_ = lean_ctor_get(v_traceState_5290_, 0);
lean_inc_ref(v_traces_5291_);
lean_dec_ref(v_traceState_5290_);
v_ref_5292_ = l_Lean_replaceRef(v_ref_5266_, v_ref_5278_);
lean_inc_ref(v_inheritedTraceOptions_5288_);
lean_inc(v_cancelTk_x3f_5286_);
lean_inc(v_currMacroScope_5284_);
lean_inc(v_quotContext_5283_);
lean_inc(v_maxHeartbeats_5282_);
lean_inc(v_initHeartbeats_5281_);
lean_inc(v_openDecls_5280_);
lean_inc(v_currNamespace_5279_);
lean_inc(v_maxRecDepth_5277_);
lean_inc(v_currRecDepth_5276_);
lean_inc_ref(v_options_5275_);
lean_inc_ref(v_fileMap_5274_);
lean_inc_ref(v_fileName_5273_);
v___x_5293_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5293_, 0, v_fileName_5273_);
lean_ctor_set(v___x_5293_, 1, v_fileMap_5274_);
lean_ctor_set(v___x_5293_, 2, v_options_5275_);
lean_ctor_set(v___x_5293_, 3, v_currRecDepth_5276_);
lean_ctor_set(v___x_5293_, 4, v_maxRecDepth_5277_);
lean_ctor_set(v___x_5293_, 5, v_ref_5292_);
lean_ctor_set(v___x_5293_, 6, v_currNamespace_5279_);
lean_ctor_set(v___x_5293_, 7, v_openDecls_5280_);
lean_ctor_set(v___x_5293_, 8, v_initHeartbeats_5281_);
lean_ctor_set(v___x_5293_, 9, v_maxHeartbeats_5282_);
lean_ctor_set(v___x_5293_, 10, v_quotContext_5283_);
lean_ctor_set(v___x_5293_, 11, v_currMacroScope_5284_);
lean_ctor_set(v___x_5293_, 12, v_cancelTk_x3f_5286_);
lean_ctor_set(v___x_5293_, 13, v_inheritedTraceOptions_5288_);
lean_ctor_set_uint8(v___x_5293_, sizeof(void*)*14, v_diag_5285_);
lean_ctor_set_uint8(v___x_5293_, sizeof(void*)*14 + 1, v_suppressElabErrors_5287_);
v___x_5294_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5291_);
lean_dec_ref(v_traces_5291_);
v_sz_5295_ = lean_array_size(v___x_5294_);
v___x_5296_ = ((size_t)0ULL);
v___x_5297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_5295_, v___x_5296_, v___x_5294_);
v_msg_5298_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5298_, 0, v_data_5265_);
lean_ctor_set(v_msg_5298_, 1, v_msg_5267_);
lean_ctor_set(v_msg_5298_, 2, v___x_5297_);
v___x_5299_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_5298_, v___y_5268_, v___y_5269_, v___x_5293_, v___y_5271_);
lean_dec_ref_known(v___x_5293_, 14);
v_a_5300_ = lean_ctor_get(v___x_5299_, 0);
v_isSharedCheck_5337_ = !lean_is_exclusive(v___x_5299_);
if (v_isSharedCheck_5337_ == 0)
{
v___x_5302_ = v___x_5299_;
v_isShared_5303_ = v_isSharedCheck_5337_;
goto v_resetjp_5301_;
}
else
{
lean_inc(v_a_5300_);
lean_dec(v___x_5299_);
v___x_5302_ = lean_box(0);
v_isShared_5303_ = v_isSharedCheck_5337_;
goto v_resetjp_5301_;
}
v_resetjp_5301_:
{
lean_object* v___x_5304_; lean_object* v_traceState_5305_; lean_object* v_env_5306_; lean_object* v_nextMacroScope_5307_; lean_object* v_ngen_5308_; lean_object* v_auxDeclNGen_5309_; lean_object* v_cache_5310_; lean_object* v_messages_5311_; lean_object* v_infoState_5312_; lean_object* v_snapshotTasks_5313_; lean_object* v___x_5315_; uint8_t v_isShared_5316_; uint8_t v_isSharedCheck_5336_; 
v___x_5304_ = lean_st_ref_take(v___y_5271_);
v_traceState_5305_ = lean_ctor_get(v___x_5304_, 4);
v_env_5306_ = lean_ctor_get(v___x_5304_, 0);
v_nextMacroScope_5307_ = lean_ctor_get(v___x_5304_, 1);
v_ngen_5308_ = lean_ctor_get(v___x_5304_, 2);
v_auxDeclNGen_5309_ = lean_ctor_get(v___x_5304_, 3);
v_cache_5310_ = lean_ctor_get(v___x_5304_, 5);
v_messages_5311_ = lean_ctor_get(v___x_5304_, 6);
v_infoState_5312_ = lean_ctor_get(v___x_5304_, 7);
v_snapshotTasks_5313_ = lean_ctor_get(v___x_5304_, 8);
v_isSharedCheck_5336_ = !lean_is_exclusive(v___x_5304_);
if (v_isSharedCheck_5336_ == 0)
{
v___x_5315_ = v___x_5304_;
v_isShared_5316_ = v_isSharedCheck_5336_;
goto v_resetjp_5314_;
}
else
{
lean_inc(v_snapshotTasks_5313_);
lean_inc(v_infoState_5312_);
lean_inc(v_messages_5311_);
lean_inc(v_cache_5310_);
lean_inc(v_traceState_5305_);
lean_inc(v_auxDeclNGen_5309_);
lean_inc(v_ngen_5308_);
lean_inc(v_nextMacroScope_5307_);
lean_inc(v_env_5306_);
lean_dec(v___x_5304_);
v___x_5315_ = lean_box(0);
v_isShared_5316_ = v_isSharedCheck_5336_;
goto v_resetjp_5314_;
}
v_resetjp_5314_:
{
uint64_t v_tid_5317_; lean_object* v___x_5319_; uint8_t v_isShared_5320_; uint8_t v_isSharedCheck_5334_; 
v_tid_5317_ = lean_ctor_get_uint64(v_traceState_5305_, sizeof(void*)*1);
v_isSharedCheck_5334_ = !lean_is_exclusive(v_traceState_5305_);
if (v_isSharedCheck_5334_ == 0)
{
lean_object* v_unused_5335_; 
v_unused_5335_ = lean_ctor_get(v_traceState_5305_, 0);
lean_dec(v_unused_5335_);
v___x_5319_ = v_traceState_5305_;
v_isShared_5320_ = v_isSharedCheck_5334_;
goto v_resetjp_5318_;
}
else
{
lean_dec(v_traceState_5305_);
v___x_5319_ = lean_box(0);
v_isShared_5320_ = v_isSharedCheck_5334_;
goto v_resetjp_5318_;
}
v_resetjp_5318_:
{
lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5324_; 
v___x_5321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5321_, 0, v_ref_5266_);
lean_ctor_set(v___x_5321_, 1, v_a_5300_);
v___x_5322_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5264_, v___x_5321_);
if (v_isShared_5320_ == 0)
{
lean_ctor_set(v___x_5319_, 0, v___x_5322_);
v___x_5324_ = v___x_5319_;
goto v_reusejp_5323_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v___x_5322_);
lean_ctor_set_uint64(v_reuseFailAlloc_5333_, sizeof(void*)*1, v_tid_5317_);
v___x_5324_ = v_reuseFailAlloc_5333_;
goto v_reusejp_5323_;
}
v_reusejp_5323_:
{
lean_object* v___x_5326_; 
if (v_isShared_5316_ == 0)
{
lean_ctor_set(v___x_5315_, 4, v___x_5324_);
v___x_5326_ = v___x_5315_;
goto v_reusejp_5325_;
}
else
{
lean_object* v_reuseFailAlloc_5332_; 
v_reuseFailAlloc_5332_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5332_, 0, v_env_5306_);
lean_ctor_set(v_reuseFailAlloc_5332_, 1, v_nextMacroScope_5307_);
lean_ctor_set(v_reuseFailAlloc_5332_, 2, v_ngen_5308_);
lean_ctor_set(v_reuseFailAlloc_5332_, 3, v_auxDeclNGen_5309_);
lean_ctor_set(v_reuseFailAlloc_5332_, 4, v___x_5324_);
lean_ctor_set(v_reuseFailAlloc_5332_, 5, v_cache_5310_);
lean_ctor_set(v_reuseFailAlloc_5332_, 6, v_messages_5311_);
lean_ctor_set(v_reuseFailAlloc_5332_, 7, v_infoState_5312_);
lean_ctor_set(v_reuseFailAlloc_5332_, 8, v_snapshotTasks_5313_);
v___x_5326_ = v_reuseFailAlloc_5332_;
goto v_reusejp_5325_;
}
v_reusejp_5325_:
{
lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5330_; 
v___x_5327_ = lean_st_ref_set(v___y_5271_, v___x_5326_);
v___x_5328_ = lean_box(0);
if (v_isShared_5303_ == 0)
{
lean_ctor_set(v___x_5302_, 0, v___x_5328_);
v___x_5330_ = v___x_5302_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v___x_5328_);
v___x_5330_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
return v___x_5330_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_5338_, lean_object* v_data_5339_, lean_object* v_ref_5340_, lean_object* v_msg_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_){
_start:
{
lean_object* v_res_5347_; 
v_res_5347_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_5338_, v_data_5339_, v_ref_5340_, v_msg_5341_, v___y_5342_, v___y_5343_, v___y_5344_, v___y_5345_);
lean_dec(v___y_5345_);
lean_dec_ref(v___y_5344_);
lean_dec(v___y_5343_);
lean_dec_ref(v___y_5342_);
return v_res_5347_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5349_; lean_object* v___x_5350_; 
v___x_5349_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0));
v___x_5350_ = l_Lean_stringToMessageData(v___x_5349_);
return v___x_5350_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2(void){
_start:
{
lean_object* v___x_5351_; double v___x_5352_; 
v___x_5351_ = lean_unsigned_to_nat(1000u);
v___x_5352_ = lean_float_of_nat(v___x_5351_);
return v___x_5352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(lean_object* v_cls_5353_, uint8_t v_collapsed_5354_, lean_object* v_tag_5355_, lean_object* v_opts_5356_, uint8_t v_clsEnabled_5357_, lean_object* v_oldTraces_5358_, lean_object* v_msg_5359_, lean_object* v_resStartStop_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_){
_start:
{
lean_object* v_fst_5370_; lean_object* v_snd_5371_; lean_object* v___y_5373_; lean_object* v___y_5374_; lean_object* v_data_5375_; lean_object* v_fst_5386_; lean_object* v_snd_5387_; lean_object* v___x_5388_; uint8_t v___x_5389_; lean_object* v___y_5391_; lean_object* v_a_5392_; uint8_t v___y_5407_; double v___y_5438_; 
v_fst_5370_ = lean_ctor_get(v_resStartStop_5360_, 0);
lean_inc(v_fst_5370_);
v_snd_5371_ = lean_ctor_get(v_resStartStop_5360_, 1);
lean_inc(v_snd_5371_);
lean_dec_ref(v_resStartStop_5360_);
v_fst_5386_ = lean_ctor_get(v_snd_5371_, 0);
lean_inc(v_fst_5386_);
v_snd_5387_ = lean_ctor_get(v_snd_5371_, 1);
lean_inc(v_snd_5387_);
lean_dec(v_snd_5371_);
v___x_5388_ = l_Lean_trace_profiler;
v___x_5389_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_5356_, v___x_5388_);
if (v___x_5389_ == 0)
{
v___y_5407_ = v___x_5389_;
goto v___jp_5406_;
}
else
{
lean_object* v___x_5443_; uint8_t v___x_5444_; 
v___x_5443_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5444_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_5356_, v___x_5443_);
if (v___x_5444_ == 0)
{
lean_object* v___x_5445_; lean_object* v___x_5446_; double v___x_5447_; double v___x_5448_; double v___x_5449_; 
v___x_5445_ = l_Lean_trace_profiler_threshold;
v___x_5446_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_5356_, v___x_5445_);
v___x_5447_ = lean_float_of_nat(v___x_5446_);
v___x_5448_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2);
v___x_5449_ = lean_float_div(v___x_5447_, v___x_5448_);
v___y_5438_ = v___x_5449_;
goto v___jp_5437_;
}
else
{
lean_object* v___x_5450_; lean_object* v___x_5451_; double v___x_5452_; 
v___x_5450_ = l_Lean_trace_profiler_threshold;
v___x_5451_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_5356_, v___x_5450_);
v___x_5452_ = lean_float_of_nat(v___x_5451_);
v___y_5438_ = v___x_5452_;
goto v___jp_5437_;
}
}
v___jp_5372_:
{
lean_object* v___x_5376_; 
lean_inc(v___y_5374_);
v___x_5376_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_5358_, v_data_5375_, v___y_5374_, v___y_5373_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_);
if (lean_obj_tag(v___x_5376_) == 0)
{
lean_object* v___x_5377_; 
lean_dec_ref_known(v___x_5376_, 1);
v___x_5377_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_5370_);
return v___x_5377_;
}
else
{
lean_object* v_a_5378_; lean_object* v___x_5380_; uint8_t v_isShared_5381_; uint8_t v_isSharedCheck_5385_; 
lean_dec(v_fst_5370_);
v_a_5378_ = lean_ctor_get(v___x_5376_, 0);
v_isSharedCheck_5385_ = !lean_is_exclusive(v___x_5376_);
if (v_isSharedCheck_5385_ == 0)
{
v___x_5380_ = v___x_5376_;
v_isShared_5381_ = v_isSharedCheck_5385_;
goto v_resetjp_5379_;
}
else
{
lean_inc(v_a_5378_);
lean_dec(v___x_5376_);
v___x_5380_ = lean_box(0);
v_isShared_5381_ = v_isSharedCheck_5385_;
goto v_resetjp_5379_;
}
v_resetjp_5379_:
{
lean_object* v___x_5383_; 
if (v_isShared_5381_ == 0)
{
v___x_5383_ = v___x_5380_;
goto v_reusejp_5382_;
}
else
{
lean_object* v_reuseFailAlloc_5384_; 
v_reuseFailAlloc_5384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5384_, 0, v_a_5378_);
v___x_5383_ = v_reuseFailAlloc_5384_;
goto v_reusejp_5382_;
}
v_reusejp_5382_:
{
return v___x_5383_;
}
}
}
}
v___jp_5390_:
{
uint8_t v_result_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; double v___x_5396_; lean_object* v_data_5397_; 
v_result_5393_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_fst_5370_);
v___x_5394_ = lean_box(v_result_5393_);
v___x_5395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5395_, 0, v___x_5394_);
v___x_5396_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_5355_);
lean_inc_ref(v___x_5395_);
lean_inc(v_cls_5353_);
v_data_5397_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5397_, 0, v_cls_5353_);
lean_ctor_set(v_data_5397_, 1, v___x_5395_);
lean_ctor_set(v_data_5397_, 2, v_tag_5355_);
lean_ctor_set_float(v_data_5397_, sizeof(void*)*3, v___x_5396_);
lean_ctor_set_float(v_data_5397_, sizeof(void*)*3 + 8, v___x_5396_);
lean_ctor_set_uint8(v_data_5397_, sizeof(void*)*3 + 16, v_collapsed_5354_);
if (v___x_5389_ == 0)
{
lean_dec_ref_known(v___x_5395_, 1);
lean_dec(v_snd_5387_);
lean_dec(v_fst_5386_);
lean_dec_ref(v_tag_5355_);
lean_dec(v_cls_5353_);
v___y_5373_ = v_a_5392_;
v___y_5374_ = v___y_5391_;
v_data_5375_ = v_data_5397_;
goto v___jp_5372_;
}
else
{
lean_object* v_data_5398_; double v___x_5399_; double v___x_5400_; 
lean_dec_ref_known(v_data_5397_, 3);
v_data_5398_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5398_, 0, v_cls_5353_);
lean_ctor_set(v_data_5398_, 1, v___x_5395_);
lean_ctor_set(v_data_5398_, 2, v_tag_5355_);
v___x_5399_ = lean_unbox_float(v_fst_5386_);
lean_dec(v_fst_5386_);
lean_ctor_set_float(v_data_5398_, sizeof(void*)*3, v___x_5399_);
v___x_5400_ = lean_unbox_float(v_snd_5387_);
lean_dec(v_snd_5387_);
lean_ctor_set_float(v_data_5398_, sizeof(void*)*3 + 8, v___x_5400_);
lean_ctor_set_uint8(v_data_5398_, sizeof(void*)*3 + 16, v_collapsed_5354_);
v___y_5373_ = v_a_5392_;
v___y_5374_ = v___y_5391_;
v_data_5375_ = v_data_5398_;
goto v___jp_5372_;
}
}
v___jp_5401_:
{
lean_object* v_ref_5402_; lean_object* v___x_5403_; 
v_ref_5402_ = lean_ctor_get(v___y_5367_, 5);
lean_inc(v___y_5368_);
lean_inc_ref(v___y_5367_);
lean_inc(v___y_5366_);
lean_inc_ref(v___y_5365_);
lean_inc(v___y_5364_);
lean_inc_ref(v___y_5363_);
lean_inc(v___y_5362_);
lean_inc_ref(v___y_5361_);
lean_inc(v_fst_5370_);
v___x_5403_ = lean_apply_10(v_msg_5359_, v_fst_5370_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_, lean_box(0));
if (lean_obj_tag(v___x_5403_) == 0)
{
lean_object* v_a_5404_; 
v_a_5404_ = lean_ctor_get(v___x_5403_, 0);
lean_inc(v_a_5404_);
lean_dec_ref_known(v___x_5403_, 1);
v___y_5391_ = v_ref_5402_;
v_a_5392_ = v_a_5404_;
goto v___jp_5390_;
}
else
{
lean_object* v___x_5405_; 
lean_dec_ref_known(v___x_5403_, 1);
v___x_5405_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1);
v___y_5391_ = v_ref_5402_;
v_a_5392_ = v___x_5405_;
goto v___jp_5390_;
}
}
v___jp_5406_:
{
if (v_clsEnabled_5357_ == 0)
{
if (v___y_5407_ == 0)
{
lean_object* v___x_5408_; lean_object* v_traceState_5409_; lean_object* v_env_5410_; lean_object* v_nextMacroScope_5411_; lean_object* v_ngen_5412_; lean_object* v_auxDeclNGen_5413_; lean_object* v_cache_5414_; lean_object* v_messages_5415_; lean_object* v_infoState_5416_; lean_object* v_snapshotTasks_5417_; lean_object* v___x_5419_; uint8_t v_isShared_5420_; uint8_t v_isSharedCheck_5436_; 
lean_dec(v_snd_5387_);
lean_dec(v_fst_5386_);
lean_dec_ref(v_msg_5359_);
lean_dec_ref(v_tag_5355_);
lean_dec(v_cls_5353_);
v___x_5408_ = lean_st_ref_take(v___y_5368_);
v_traceState_5409_ = lean_ctor_get(v___x_5408_, 4);
v_env_5410_ = lean_ctor_get(v___x_5408_, 0);
v_nextMacroScope_5411_ = lean_ctor_get(v___x_5408_, 1);
v_ngen_5412_ = lean_ctor_get(v___x_5408_, 2);
v_auxDeclNGen_5413_ = lean_ctor_get(v___x_5408_, 3);
v_cache_5414_ = lean_ctor_get(v___x_5408_, 5);
v_messages_5415_ = lean_ctor_get(v___x_5408_, 6);
v_infoState_5416_ = lean_ctor_get(v___x_5408_, 7);
v_snapshotTasks_5417_ = lean_ctor_get(v___x_5408_, 8);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5408_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5419_ = v___x_5408_;
v_isShared_5420_ = v_isSharedCheck_5436_;
goto v_resetjp_5418_;
}
else
{
lean_inc(v_snapshotTasks_5417_);
lean_inc(v_infoState_5416_);
lean_inc(v_messages_5415_);
lean_inc(v_cache_5414_);
lean_inc(v_traceState_5409_);
lean_inc(v_auxDeclNGen_5413_);
lean_inc(v_ngen_5412_);
lean_inc(v_nextMacroScope_5411_);
lean_inc(v_env_5410_);
lean_dec(v___x_5408_);
v___x_5419_ = lean_box(0);
v_isShared_5420_ = v_isSharedCheck_5436_;
goto v_resetjp_5418_;
}
v_resetjp_5418_:
{
uint64_t v_tid_5421_; lean_object* v_traces_5422_; lean_object* v___x_5424_; uint8_t v_isShared_5425_; uint8_t v_isSharedCheck_5435_; 
v_tid_5421_ = lean_ctor_get_uint64(v_traceState_5409_, sizeof(void*)*1);
v_traces_5422_ = lean_ctor_get(v_traceState_5409_, 0);
v_isSharedCheck_5435_ = !lean_is_exclusive(v_traceState_5409_);
if (v_isSharedCheck_5435_ == 0)
{
v___x_5424_ = v_traceState_5409_;
v_isShared_5425_ = v_isSharedCheck_5435_;
goto v_resetjp_5423_;
}
else
{
lean_inc(v_traces_5422_);
lean_dec(v_traceState_5409_);
v___x_5424_ = lean_box(0);
v_isShared_5425_ = v_isSharedCheck_5435_;
goto v_resetjp_5423_;
}
v_resetjp_5423_:
{
lean_object* v___x_5426_; lean_object* v___x_5428_; 
v___x_5426_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5358_, v_traces_5422_);
lean_dec_ref(v_traces_5422_);
if (v_isShared_5425_ == 0)
{
lean_ctor_set(v___x_5424_, 0, v___x_5426_);
v___x_5428_ = v___x_5424_;
goto v_reusejp_5427_;
}
else
{
lean_object* v_reuseFailAlloc_5434_; 
v_reuseFailAlloc_5434_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5434_, 0, v___x_5426_);
lean_ctor_set_uint64(v_reuseFailAlloc_5434_, sizeof(void*)*1, v_tid_5421_);
v___x_5428_ = v_reuseFailAlloc_5434_;
goto v_reusejp_5427_;
}
v_reusejp_5427_:
{
lean_object* v___x_5430_; 
if (v_isShared_5420_ == 0)
{
lean_ctor_set(v___x_5419_, 4, v___x_5428_);
v___x_5430_ = v___x_5419_;
goto v_reusejp_5429_;
}
else
{
lean_object* v_reuseFailAlloc_5433_; 
v_reuseFailAlloc_5433_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5433_, 0, v_env_5410_);
lean_ctor_set(v_reuseFailAlloc_5433_, 1, v_nextMacroScope_5411_);
lean_ctor_set(v_reuseFailAlloc_5433_, 2, v_ngen_5412_);
lean_ctor_set(v_reuseFailAlloc_5433_, 3, v_auxDeclNGen_5413_);
lean_ctor_set(v_reuseFailAlloc_5433_, 4, v___x_5428_);
lean_ctor_set(v_reuseFailAlloc_5433_, 5, v_cache_5414_);
lean_ctor_set(v_reuseFailAlloc_5433_, 6, v_messages_5415_);
lean_ctor_set(v_reuseFailAlloc_5433_, 7, v_infoState_5416_);
lean_ctor_set(v_reuseFailAlloc_5433_, 8, v_snapshotTasks_5417_);
v___x_5430_ = v_reuseFailAlloc_5433_;
goto v_reusejp_5429_;
}
v_reusejp_5429_:
{
lean_object* v___x_5431_; lean_object* v___x_5432_; 
v___x_5431_ = lean_st_ref_set(v___y_5368_, v___x_5430_);
v___x_5432_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_5370_);
return v___x_5432_;
}
}
}
}
}
else
{
goto v___jp_5401_;
}
}
else
{
goto v___jp_5401_;
}
}
v___jp_5437_:
{
double v___x_5439_; double v___x_5440_; double v___x_5441_; uint8_t v___x_5442_; 
v___x_5439_ = lean_unbox_float(v_snd_5387_);
v___x_5440_ = lean_unbox_float(v_fst_5386_);
v___x_5441_ = lean_float_sub(v___x_5439_, v___x_5440_);
v___x_5442_ = lean_float_decLt(v___y_5438_, v___x_5441_);
v___y_5407_ = v___x_5442_;
goto v___jp_5406_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___boxed(lean_object** _args){
lean_object* v_cls_5453_ = _args[0];
lean_object* v_collapsed_5454_ = _args[1];
lean_object* v_tag_5455_ = _args[2];
lean_object* v_opts_5456_ = _args[3];
lean_object* v_clsEnabled_5457_ = _args[4];
lean_object* v_oldTraces_5458_ = _args[5];
lean_object* v_msg_5459_ = _args[6];
lean_object* v_resStartStop_5460_ = _args[7];
lean_object* v___y_5461_ = _args[8];
lean_object* v___y_5462_ = _args[9];
lean_object* v___y_5463_ = _args[10];
lean_object* v___y_5464_ = _args[11];
lean_object* v___y_5465_ = _args[12];
lean_object* v___y_5466_ = _args[13];
lean_object* v___y_5467_ = _args[14];
lean_object* v___y_5468_ = _args[15];
lean_object* v___y_5469_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_5470_; uint8_t v_clsEnabled_boxed_5471_; lean_object* v_res_5472_; 
v_collapsed_boxed_5470_ = lean_unbox(v_collapsed_5454_);
v_clsEnabled_boxed_5471_ = lean_unbox(v_clsEnabled_5457_);
v_res_5472_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v_cls_5453_, v_collapsed_boxed_5470_, v_tag_5455_, v_opts_5456_, v_clsEnabled_boxed_5471_, v_oldTraces_5458_, v_msg_5459_, v_resStartStop_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_);
lean_dec(v___y_5468_);
lean_dec_ref(v___y_5467_);
lean_dec(v___y_5466_);
lean_dec_ref(v___y_5465_);
lean_dec(v___y_5464_);
lean_dec_ref(v___y_5463_);
lean_dec(v___y_5462_);
lean_dec_ref(v___y_5461_);
lean_dec_ref(v_opts_5456_);
return v_res_5472_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_5477_; lean_object* v___x_5478_; 
v___x_5477_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1));
v___x_5478_ = l_Lean_stringToMessageData(v___x_5477_);
return v___x_5478_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(lean_object* v_as_x27_5479_, lean_object* v_b_5480_, lean_object* v___y_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_){
_start:
{
if (lean_obj_tag(v_as_x27_5479_) == 0)
{
lean_object* v___x_5490_; 
v___x_5490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5490_, 0, v_b_5480_);
return v___x_5490_;
}
else
{
lean_object* v_head_5491_; lean_object* v_options_5492_; lean_object* v_tail_5493_; lean_object* v_name_5494_; lean_object* v_run_x27_5495_; lean_object* v_inheritedTraceOptions_5496_; uint8_t v_hasTrace_5497_; lean_object* v___x_5498_; uint8_t v___y_5500_; lean_object* v___x_5505_; lean_object* v___y_5507_; 
lean_dec_ref(v_b_5480_);
v_head_5491_ = lean_ctor_get(v_as_x27_5479_, 0);
v_options_5492_ = lean_ctor_get(v___y_5487_, 2);
v_tail_5493_ = lean_ctor_get(v_as_x27_5479_, 1);
v_name_5494_ = lean_ctor_get(v_head_5491_, 0);
v_run_x27_5495_ = lean_ctor_get(v_head_5491_, 1);
v_inheritedTraceOptions_5496_ = lean_ctor_get(v___y_5487_, 13);
v_hasTrace_5497_ = lean_ctor_get_uint8(v_options_5492_, sizeof(void*)*1);
v___x_5498_ = lean_box(0);
v___x_5505_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
if (v_hasTrace_5497_ == 0)
{
lean_object* v___x_5535_; 
lean_inc_ref(v_run_x27_5495_);
lean_inc(v___y_5488_);
lean_inc_ref(v___y_5487_);
lean_inc(v___y_5486_);
lean_inc_ref(v___y_5485_);
lean_inc(v___y_5484_);
lean_inc_ref(v___y_5483_);
lean_inc(v___y_5482_);
lean_inc_ref(v___y_5481_);
v___x_5535_ = lean_apply_9(v_run_x27_5495_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, lean_box(0));
v___y_5507_ = v___x_5535_;
goto v___jp_5506_;
}
else
{
lean_object* v___f_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v___x_5539_; uint8_t v___x_5540_; lean_object* v___y_5542_; lean_object* v___y_5543_; lean_object* v_a_5544_; lean_object* v___y_5557_; lean_object* v___y_5558_; lean_object* v_a_5559_; 
lean_inc(v_name_5494_);
v___f_5536_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 11, 1);
lean_closure_set(v___f_5536_, 0, v_name_5494_);
v___x_5537_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___x_5538_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5539_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___x_5540_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5496_, v_options_5492_, v___x_5539_);
if (v___x_5540_ == 0)
{
lean_object* v___x_5609_; uint8_t v___x_5610_; 
v___x_5609_ = l_Lean_trace_profiler;
v___x_5610_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_5492_, v___x_5609_);
if (v___x_5610_ == 0)
{
lean_object* v___x_5611_; 
lean_dec_ref(v___f_5536_);
lean_inc_ref(v_run_x27_5495_);
lean_inc(v___y_5488_);
lean_inc_ref(v___y_5487_);
lean_inc(v___y_5486_);
lean_inc_ref(v___y_5485_);
lean_inc(v___y_5484_);
lean_inc_ref(v___y_5483_);
lean_inc(v___y_5482_);
lean_inc_ref(v___y_5481_);
v___x_5611_ = lean_apply_9(v_run_x27_5495_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, lean_box(0));
v___y_5507_ = v___x_5611_;
goto v___jp_5506_;
}
else
{
goto v___jp_5568_;
}
}
else
{
goto v___jp_5568_;
}
v___jp_5541_:
{
lean_object* v___x_5545_; double v___x_5546_; double v___x_5547_; double v___x_5548_; double v___x_5549_; double v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; 
v___x_5545_ = lean_io_mono_nanos_now();
v___x_5546_ = lean_float_of_nat(v___y_5542_);
v___x_5547_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10);
v___x_5548_ = lean_float_div(v___x_5546_, v___x_5547_);
v___x_5549_ = lean_float_of_nat(v___x_5545_);
v___x_5550_ = lean_float_div(v___x_5549_, v___x_5547_);
v___x_5551_ = lean_box_float(v___x_5548_);
v___x_5552_ = lean_box_float(v___x_5550_);
v___x_5553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5553_, 0, v___x_5551_);
lean_ctor_set(v___x_5553_, 1, v___x_5552_);
v___x_5554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5554_, 0, v_a_5544_);
lean_ctor_set(v___x_5554_, 1, v___x_5553_);
v___x_5555_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_5537_, v_hasTrace_5497_, v___x_5538_, v_options_5492_, v___x_5540_, v___y_5543_, v___f_5536_, v___x_5554_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_);
v___y_5507_ = v___x_5555_;
goto v___jp_5506_;
}
v___jp_5556_:
{
lean_object* v___x_5560_; double v___x_5561_; double v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; 
v___x_5560_ = lean_io_get_num_heartbeats();
v___x_5561_ = lean_float_of_nat(v___y_5557_);
v___x_5562_ = lean_float_of_nat(v___x_5560_);
v___x_5563_ = lean_box_float(v___x_5561_);
v___x_5564_ = lean_box_float(v___x_5562_);
v___x_5565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5565_, 0, v___x_5563_);
lean_ctor_set(v___x_5565_, 1, v___x_5564_);
v___x_5566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5566_, 0, v_a_5559_);
lean_ctor_set(v___x_5566_, 1, v___x_5565_);
v___x_5567_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_5537_, v_hasTrace_5497_, v___x_5538_, v_options_5492_, v___x_5540_, v___y_5558_, v___f_5536_, v___x_5566_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_);
v___y_5507_ = v___x_5567_;
goto v___jp_5506_;
}
v___jp_5568_:
{
lean_object* v___x_5569_; lean_object* v_a_5570_; lean_object* v___x_5571_; uint8_t v___x_5572_; 
v___x_5569_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_5488_);
v_a_5570_ = lean_ctor_get(v___x_5569_, 0);
lean_inc(v_a_5570_);
lean_dec_ref(v___x_5569_);
v___x_5571_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5572_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_5492_, v___x_5571_);
if (v___x_5572_ == 0)
{
lean_object* v___x_5573_; lean_object* v___x_5574_; 
v___x_5573_ = lean_io_mono_nanos_now();
lean_inc_ref(v_run_x27_5495_);
lean_inc(v___y_5488_);
lean_inc_ref(v___y_5487_);
lean_inc(v___y_5486_);
lean_inc_ref(v___y_5485_);
lean_inc(v___y_5484_);
lean_inc_ref(v___y_5483_);
lean_inc(v___y_5482_);
lean_inc_ref(v___y_5481_);
v___x_5574_ = lean_apply_9(v_run_x27_5495_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, lean_box(0));
if (lean_obj_tag(v___x_5574_) == 0)
{
lean_object* v_a_5575_; lean_object* v___x_5577_; uint8_t v_isShared_5578_; uint8_t v_isSharedCheck_5582_; 
v_a_5575_ = lean_ctor_get(v___x_5574_, 0);
v_isSharedCheck_5582_ = !lean_is_exclusive(v___x_5574_);
if (v_isSharedCheck_5582_ == 0)
{
v___x_5577_ = v___x_5574_;
v_isShared_5578_ = v_isSharedCheck_5582_;
goto v_resetjp_5576_;
}
else
{
lean_inc(v_a_5575_);
lean_dec(v___x_5574_);
v___x_5577_ = lean_box(0);
v_isShared_5578_ = v_isSharedCheck_5582_;
goto v_resetjp_5576_;
}
v_resetjp_5576_:
{
lean_object* v___x_5580_; 
if (v_isShared_5578_ == 0)
{
lean_ctor_set_tag(v___x_5577_, 1);
v___x_5580_ = v___x_5577_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v_a_5575_);
v___x_5580_ = v_reuseFailAlloc_5581_;
goto v_reusejp_5579_;
}
v_reusejp_5579_:
{
v___y_5542_ = v___x_5573_;
v___y_5543_ = v_a_5570_;
v_a_5544_ = v___x_5580_;
goto v___jp_5541_;
}
}
}
else
{
lean_object* v_a_5583_; lean_object* v___x_5585_; uint8_t v_isShared_5586_; uint8_t v_isSharedCheck_5590_; 
v_a_5583_ = lean_ctor_get(v___x_5574_, 0);
v_isSharedCheck_5590_ = !lean_is_exclusive(v___x_5574_);
if (v_isSharedCheck_5590_ == 0)
{
v___x_5585_ = v___x_5574_;
v_isShared_5586_ = v_isSharedCheck_5590_;
goto v_resetjp_5584_;
}
else
{
lean_inc(v_a_5583_);
lean_dec(v___x_5574_);
v___x_5585_ = lean_box(0);
v_isShared_5586_ = v_isSharedCheck_5590_;
goto v_resetjp_5584_;
}
v_resetjp_5584_:
{
lean_object* v___x_5588_; 
if (v_isShared_5586_ == 0)
{
lean_ctor_set_tag(v___x_5585_, 0);
v___x_5588_ = v___x_5585_;
goto v_reusejp_5587_;
}
else
{
lean_object* v_reuseFailAlloc_5589_; 
v_reuseFailAlloc_5589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5589_, 0, v_a_5583_);
v___x_5588_ = v_reuseFailAlloc_5589_;
goto v_reusejp_5587_;
}
v_reusejp_5587_:
{
v___y_5542_ = v___x_5573_;
v___y_5543_ = v_a_5570_;
v_a_5544_ = v___x_5588_;
goto v___jp_5541_;
}
}
}
}
else
{
lean_object* v___x_5591_; lean_object* v___x_5592_; 
v___x_5591_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_run_x27_5495_);
lean_inc(v___y_5488_);
lean_inc_ref(v___y_5487_);
lean_inc(v___y_5486_);
lean_inc_ref(v___y_5485_);
lean_inc(v___y_5484_);
lean_inc_ref(v___y_5483_);
lean_inc(v___y_5482_);
lean_inc_ref(v___y_5481_);
v___x_5592_ = lean_apply_9(v_run_x27_5495_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, lean_box(0));
if (lean_obj_tag(v___x_5592_) == 0)
{
lean_object* v_a_5593_; lean_object* v___x_5595_; uint8_t v_isShared_5596_; uint8_t v_isSharedCheck_5600_; 
v_a_5593_ = lean_ctor_get(v___x_5592_, 0);
v_isSharedCheck_5600_ = !lean_is_exclusive(v___x_5592_);
if (v_isSharedCheck_5600_ == 0)
{
v___x_5595_ = v___x_5592_;
v_isShared_5596_ = v_isSharedCheck_5600_;
goto v_resetjp_5594_;
}
else
{
lean_inc(v_a_5593_);
lean_dec(v___x_5592_);
v___x_5595_ = lean_box(0);
v_isShared_5596_ = v_isSharedCheck_5600_;
goto v_resetjp_5594_;
}
v_resetjp_5594_:
{
lean_object* v___x_5598_; 
if (v_isShared_5596_ == 0)
{
lean_ctor_set_tag(v___x_5595_, 1);
v___x_5598_ = v___x_5595_;
goto v_reusejp_5597_;
}
else
{
lean_object* v_reuseFailAlloc_5599_; 
v_reuseFailAlloc_5599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5599_, 0, v_a_5593_);
v___x_5598_ = v_reuseFailAlloc_5599_;
goto v_reusejp_5597_;
}
v_reusejp_5597_:
{
v___y_5557_ = v___x_5591_;
v___y_5558_ = v_a_5570_;
v_a_5559_ = v___x_5598_;
goto v___jp_5556_;
}
}
}
else
{
lean_object* v_a_5601_; lean_object* v___x_5603_; uint8_t v_isShared_5604_; uint8_t v_isSharedCheck_5608_; 
v_a_5601_ = lean_ctor_get(v___x_5592_, 0);
v_isSharedCheck_5608_ = !lean_is_exclusive(v___x_5592_);
if (v_isSharedCheck_5608_ == 0)
{
v___x_5603_ = v___x_5592_;
v_isShared_5604_ = v_isSharedCheck_5608_;
goto v_resetjp_5602_;
}
else
{
lean_inc(v_a_5601_);
lean_dec(v___x_5592_);
v___x_5603_ = lean_box(0);
v_isShared_5604_ = v_isSharedCheck_5608_;
goto v_resetjp_5602_;
}
v_resetjp_5602_:
{
lean_object* v___x_5606_; 
if (v_isShared_5604_ == 0)
{
lean_ctor_set_tag(v___x_5603_, 0);
v___x_5606_ = v___x_5603_;
goto v_reusejp_5605_;
}
else
{
lean_object* v_reuseFailAlloc_5607_; 
v_reuseFailAlloc_5607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5607_, 0, v_a_5601_);
v___x_5606_ = v_reuseFailAlloc_5607_;
goto v_reusejp_5605_;
}
v_reusejp_5605_:
{
v___y_5557_ = v___x_5591_;
v___y_5558_ = v_a_5570_;
v_a_5559_ = v___x_5606_;
goto v___jp_5556_;
}
}
}
}
}
}
v___jp_5499_:
{
lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; 
v___x_5501_ = lean_box(v___y_5500_);
v___x_5502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5502_, 0, v___x_5501_);
v___x_5503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5503_, 0, v___x_5502_);
lean_ctor_set(v___x_5503_, 1, v___x_5498_);
v___x_5504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5504_, 0, v___x_5503_);
return v___x_5504_;
}
v___jp_5506_:
{
if (lean_obj_tag(v___y_5507_) == 0)
{
lean_object* v_a_5508_; uint8_t v___x_5509_; 
v_a_5508_ = lean_ctor_get(v___y_5507_, 0);
lean_inc(v_a_5508_);
lean_dec_ref_known(v___y_5507_, 1);
v___x_5509_ = lean_unbox(v_a_5508_);
if (v___x_5509_ == 0)
{
lean_dec(v_a_5508_);
v_as_x27_5479_ = v_tail_5493_;
v_b_5480_ = v___x_5505_;
goto _start;
}
else
{
if (v_hasTrace_5497_ == 0)
{
uint8_t v___x_5511_; 
v___x_5511_ = lean_unbox(v_a_5508_);
lean_dec(v_a_5508_);
v___y_5500_ = v___x_5511_;
goto v___jp_5499_;
}
else
{
lean_object* v___x_5512_; lean_object* v___x_5513_; uint8_t v___x_5514_; 
v___x_5512_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___x_5513_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___x_5514_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5496_, v_options_5492_, v___x_5513_);
if (v___x_5514_ == 0)
{
uint8_t v___x_5515_; 
v___x_5515_ = lean_unbox(v_a_5508_);
lean_dec(v_a_5508_);
v___y_5500_ = v___x_5515_;
goto v___jp_5499_;
}
else
{
lean_object* v___x_5516_; lean_object* v___x_5517_; 
v___x_5516_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2);
v___x_5517_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_5512_, v___x_5516_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_);
if (lean_obj_tag(v___x_5517_) == 0)
{
uint8_t v___x_5518_; 
lean_dec_ref_known(v___x_5517_, 1);
v___x_5518_ = lean_unbox(v_a_5508_);
lean_dec(v_a_5508_);
v___y_5500_ = v___x_5518_;
goto v___jp_5499_;
}
else
{
lean_object* v_a_5519_; lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5526_; 
lean_dec(v_a_5508_);
v_a_5519_ = lean_ctor_get(v___x_5517_, 0);
v_isSharedCheck_5526_ = !lean_is_exclusive(v___x_5517_);
if (v_isSharedCheck_5526_ == 0)
{
v___x_5521_ = v___x_5517_;
v_isShared_5522_ = v_isSharedCheck_5526_;
goto v_resetjp_5520_;
}
else
{
lean_inc(v_a_5519_);
lean_dec(v___x_5517_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5526_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
lean_object* v___x_5524_; 
if (v_isShared_5522_ == 0)
{
v___x_5524_ = v___x_5521_;
goto v_reusejp_5523_;
}
else
{
lean_object* v_reuseFailAlloc_5525_; 
v_reuseFailAlloc_5525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5525_, 0, v_a_5519_);
v___x_5524_ = v_reuseFailAlloc_5525_;
goto v_reusejp_5523_;
}
v_reusejp_5523_:
{
return v___x_5524_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5527_; lean_object* v___x_5529_; uint8_t v_isShared_5530_; uint8_t v_isSharedCheck_5534_; 
v_a_5527_ = lean_ctor_get(v___y_5507_, 0);
v_isSharedCheck_5534_ = !lean_is_exclusive(v___y_5507_);
if (v_isSharedCheck_5534_ == 0)
{
v___x_5529_ = v___y_5507_;
v_isShared_5530_ = v_isSharedCheck_5534_;
goto v_resetjp_5528_;
}
else
{
lean_inc(v_a_5527_);
lean_dec(v___y_5507_);
v___x_5529_ = lean_box(0);
v_isShared_5530_ = v_isSharedCheck_5534_;
goto v_resetjp_5528_;
}
v_resetjp_5528_:
{
lean_object* v___x_5532_; 
if (v_isShared_5530_ == 0)
{
v___x_5532_ = v___x_5529_;
goto v_reusejp_5531_;
}
else
{
lean_object* v_reuseFailAlloc_5533_; 
v_reuseFailAlloc_5533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5533_, 0, v_a_5527_);
v___x_5532_ = v_reuseFailAlloc_5533_;
goto v_reusejp_5531_;
}
v_reusejp_5531_:
{
return v___x_5532_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___boxed(lean_object* v_as_x27_5612_, lean_object* v_b_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_){
_start:
{
lean_object* v_res_5623_; 
v_res_5623_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_5612_, v_b_5613_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
lean_dec(v___y_5621_);
lean_dec_ref(v___y_5620_);
lean_dec(v___y_5619_);
lean_dec_ref(v___y_5618_);
lean_dec(v___y_5617_);
lean_dec_ref(v___y_5616_);
lean_dec(v___y_5615_);
lean_dec_ref(v___y_5614_);
lean_dec(v_as_x27_5612_);
return v_res_5623_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2(void){
_start:
{
lean_object* v___x_5626_; lean_object* v___x_5627_; 
v___x_5626_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1));
v___x_5627_ = l_Lean_stringToMessageData(v___x_5626_);
return v___x_5627_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4(void){
_start:
{
lean_object* v___x_5629_; lean_object* v___x_5630_; 
v___x_5629_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3));
v___x_5630_ = l_Lean_stringToMessageData(v___x_5629_);
return v___x_5630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(lean_object* v_passes_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_, lean_object* v_a_5638_, lean_object* v_a_5639_){
_start:
{
lean_object* v___x_5641_; lean_object* v___x_5642_; 
v___x_5641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0));
v___x_5642_ = l_Lean_Core_checkSystem(v___x_5641_, v_a_5638_, v_a_5639_);
if (lean_obj_tag(v___x_5642_) == 0)
{
lean_object* v___x_5643_; lean_object* v_rewriteSimpCache_5644_; lean_object* v_rewriteDSimpCache_5645_; lean_object* v_acCache_5646_; lean_object* v_typeAnalysis_5647_; lean_object* v_goal_5648_; lean_object* v_hypotheses_5649_; lean_object* v___x_5651_; uint8_t v_isShared_5652_; uint8_t v_isSharedCheck_5732_; 
lean_dec_ref_known(v___x_5642_, 1);
v___x_5643_ = lean_st_ref_take(v_a_5633_);
v_rewriteSimpCache_5644_ = lean_ctor_get(v___x_5643_, 0);
v_rewriteDSimpCache_5645_ = lean_ctor_get(v___x_5643_, 1);
v_acCache_5646_ = lean_ctor_get(v___x_5643_, 2);
v_typeAnalysis_5647_ = lean_ctor_get(v___x_5643_, 3);
v_goal_5648_ = lean_ctor_get(v___x_5643_, 4);
v_hypotheses_5649_ = lean_ctor_get(v___x_5643_, 5);
v_isSharedCheck_5732_ = !lean_is_exclusive(v___x_5643_);
if (v_isSharedCheck_5732_ == 0)
{
v___x_5651_ = v___x_5643_;
v_isShared_5652_ = v_isSharedCheck_5732_;
goto v_resetjp_5650_;
}
else
{
lean_inc(v_hypotheses_5649_);
lean_inc(v_goal_5648_);
lean_inc(v_typeAnalysis_5647_);
lean_inc(v_acCache_5646_);
lean_inc(v_rewriteDSimpCache_5645_);
lean_inc(v_rewriteSimpCache_5644_);
lean_dec(v___x_5643_);
v___x_5651_ = lean_box(0);
v_isShared_5652_ = v_isSharedCheck_5732_;
goto v_resetjp_5650_;
}
v_resetjp_5650_:
{
uint8_t v___x_5653_; lean_object* v___x_5655_; 
v___x_5653_ = 0;
if (v_isShared_5652_ == 0)
{
v___x_5655_ = v___x_5651_;
goto v_reusejp_5654_;
}
else
{
lean_object* v_reuseFailAlloc_5731_; 
v_reuseFailAlloc_5731_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_5731_, 0, v_rewriteSimpCache_5644_);
lean_ctor_set(v_reuseFailAlloc_5731_, 1, v_rewriteDSimpCache_5645_);
lean_ctor_set(v_reuseFailAlloc_5731_, 2, v_acCache_5646_);
lean_ctor_set(v_reuseFailAlloc_5731_, 3, v_typeAnalysis_5647_);
lean_ctor_set(v_reuseFailAlloc_5731_, 4, v_goal_5648_);
lean_ctor_set(v_reuseFailAlloc_5731_, 5, v_hypotheses_5649_);
v___x_5655_ = v_reuseFailAlloc_5731_;
goto v_reusejp_5654_;
}
v_reusejp_5654_:
{
lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; 
lean_ctor_set_uint8(v___x_5655_, sizeof(void*)*6, v___x_5653_);
v___x_5656_ = lean_st_ref_set(v_a_5633_, v___x_5655_);
v___x_5657_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
v___x_5658_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_passes_5631_, v___x_5657_, v_a_5632_, v_a_5633_, v_a_5634_, v_a_5635_, v_a_5636_, v_a_5637_, v_a_5638_, v_a_5639_);
if (lean_obj_tag(v___x_5658_) == 0)
{
lean_object* v_a_5659_; lean_object* v___x_5661_; uint8_t v_isShared_5662_; uint8_t v_isSharedCheck_5722_; 
v_a_5659_ = lean_ctor_get(v___x_5658_, 0);
v_isSharedCheck_5722_ = !lean_is_exclusive(v___x_5658_);
if (v_isSharedCheck_5722_ == 0)
{
v___x_5661_ = v___x_5658_;
v_isShared_5662_ = v_isSharedCheck_5722_;
goto v_resetjp_5660_;
}
else
{
lean_inc(v_a_5659_);
lean_dec(v___x_5658_);
v___x_5661_ = lean_box(0);
v_isShared_5662_ = v_isSharedCheck_5722_;
goto v_resetjp_5660_;
}
v_resetjp_5660_:
{
lean_object* v_fst_5663_; 
v_fst_5663_ = lean_ctor_get(v_a_5659_, 0);
lean_inc(v_fst_5663_);
lean_dec(v_a_5659_);
if (lean_obj_tag(v_fst_5663_) == 0)
{
lean_object* v___x_5664_; uint8_t v_didChange_5665_; 
v___x_5664_ = lean_st_ref_get(v_a_5633_);
v_didChange_5665_ = lean_ctor_get_uint8(v___x_5664_, sizeof(void*)*6);
lean_dec(v___x_5664_);
if (v_didChange_5665_ == 0)
{
lean_object* v_options_5666_; uint8_t v_hasTrace_5667_; 
v_options_5666_ = lean_ctor_get(v_a_5638_, 2);
v_hasTrace_5667_ = lean_ctor_get_uint8(v_options_5666_, sizeof(void*)*1);
if (v_hasTrace_5667_ == 0)
{
lean_object* v___x_5668_; lean_object* v___x_5670_; 
v___x_5668_ = lean_box(v_didChange_5665_);
if (v_isShared_5662_ == 0)
{
lean_ctor_set(v___x_5661_, 0, v___x_5668_);
v___x_5670_ = v___x_5661_;
goto v_reusejp_5669_;
}
else
{
lean_object* v_reuseFailAlloc_5671_; 
v_reuseFailAlloc_5671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5671_, 0, v___x_5668_);
v___x_5670_ = v_reuseFailAlloc_5671_;
goto v_reusejp_5669_;
}
v_reusejp_5669_:
{
return v___x_5670_;
}
}
else
{
lean_object* v_inheritedTraceOptions_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; uint8_t v___x_5675_; 
v_inheritedTraceOptions_5672_ = lean_ctor_get(v_a_5638_, 13);
v___x_5673_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___x_5674_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___x_5675_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5672_, v_options_5666_, v___x_5674_);
if (v___x_5675_ == 0)
{
lean_object* v___x_5676_; lean_object* v___x_5678_; 
v___x_5676_ = lean_box(v_didChange_5665_);
if (v_isShared_5662_ == 0)
{
lean_ctor_set(v___x_5661_, 0, v___x_5676_);
v___x_5678_ = v___x_5661_;
goto v_reusejp_5677_;
}
else
{
lean_object* v_reuseFailAlloc_5679_; 
v_reuseFailAlloc_5679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5679_, 0, v___x_5676_);
v___x_5678_ = v_reuseFailAlloc_5679_;
goto v_reusejp_5677_;
}
v_reusejp_5677_:
{
return v___x_5678_;
}
}
else
{
lean_object* v___x_5680_; lean_object* v___x_5681_; 
lean_del_object(v___x_5661_);
v___x_5680_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2);
v___x_5681_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_5673_, v___x_5680_, v_a_5636_, v_a_5637_, v_a_5638_, v_a_5639_);
if (lean_obj_tag(v___x_5681_) == 0)
{
lean_object* v___x_5683_; uint8_t v_isShared_5684_; uint8_t v_isSharedCheck_5689_; 
v_isSharedCheck_5689_ = !lean_is_exclusive(v___x_5681_);
if (v_isSharedCheck_5689_ == 0)
{
lean_object* v_unused_5690_; 
v_unused_5690_ = lean_ctor_get(v___x_5681_, 0);
lean_dec(v_unused_5690_);
v___x_5683_ = v___x_5681_;
v_isShared_5684_ = v_isSharedCheck_5689_;
goto v_resetjp_5682_;
}
else
{
lean_dec(v___x_5681_);
v___x_5683_ = lean_box(0);
v_isShared_5684_ = v_isSharedCheck_5689_;
goto v_resetjp_5682_;
}
v_resetjp_5682_:
{
lean_object* v___x_5685_; lean_object* v___x_5687_; 
v___x_5685_ = lean_box(v_didChange_5665_);
if (v_isShared_5684_ == 0)
{
lean_ctor_set(v___x_5683_, 0, v___x_5685_);
v___x_5687_ = v___x_5683_;
goto v_reusejp_5686_;
}
else
{
lean_object* v_reuseFailAlloc_5688_; 
v_reuseFailAlloc_5688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5688_, 0, v___x_5685_);
v___x_5687_ = v_reuseFailAlloc_5688_;
goto v_reusejp_5686_;
}
v_reusejp_5686_:
{
return v___x_5687_;
}
}
}
else
{
lean_object* v_a_5691_; lean_object* v___x_5693_; uint8_t v_isShared_5694_; uint8_t v_isSharedCheck_5698_; 
v_a_5691_ = lean_ctor_get(v___x_5681_, 0);
v_isSharedCheck_5698_ = !lean_is_exclusive(v___x_5681_);
if (v_isSharedCheck_5698_ == 0)
{
v___x_5693_ = v___x_5681_;
v_isShared_5694_ = v_isSharedCheck_5698_;
goto v_resetjp_5692_;
}
else
{
lean_inc(v_a_5691_);
lean_dec(v___x_5681_);
v___x_5693_ = lean_box(0);
v_isShared_5694_ = v_isSharedCheck_5698_;
goto v_resetjp_5692_;
}
v_resetjp_5692_:
{
lean_object* v___x_5696_; 
if (v_isShared_5694_ == 0)
{
v___x_5696_ = v___x_5693_;
goto v_reusejp_5695_;
}
else
{
lean_object* v_reuseFailAlloc_5697_; 
v_reuseFailAlloc_5697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5697_, 0, v_a_5691_);
v___x_5696_ = v_reuseFailAlloc_5697_;
goto v_reusejp_5695_;
}
v_reusejp_5695_:
{
return v___x_5696_;
}
}
}
}
}
}
else
{
lean_object* v_options_5699_; uint8_t v_hasTrace_5700_; 
lean_del_object(v___x_5661_);
v_options_5699_ = lean_ctor_get(v_a_5638_, 2);
v_hasTrace_5700_ = lean_ctor_get_uint8(v_options_5699_, sizeof(void*)*1);
if (v_hasTrace_5700_ == 0)
{
goto _start;
}
else
{
lean_object* v_inheritedTraceOptions_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; uint8_t v___x_5705_; 
v_inheritedTraceOptions_5702_ = lean_ctor_get(v_a_5638_, 13);
v___x_5703_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___x_5704_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___x_5705_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5702_, v_options_5699_, v___x_5704_);
if (v___x_5705_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_5707_; lean_object* v___x_5708_; 
v___x_5707_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4);
v___x_5708_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_5703_, v___x_5707_, v_a_5636_, v_a_5637_, v_a_5638_, v_a_5639_);
if (lean_obj_tag(v___x_5708_) == 0)
{
lean_dec_ref_known(v___x_5708_, 1);
goto _start;
}
else
{
lean_object* v_a_5710_; lean_object* v___x_5712_; uint8_t v_isShared_5713_; uint8_t v_isSharedCheck_5717_; 
v_a_5710_ = lean_ctor_get(v___x_5708_, 0);
v_isSharedCheck_5717_ = !lean_is_exclusive(v___x_5708_);
if (v_isSharedCheck_5717_ == 0)
{
v___x_5712_ = v___x_5708_;
v_isShared_5713_ = v_isSharedCheck_5717_;
goto v_resetjp_5711_;
}
else
{
lean_inc(v_a_5710_);
lean_dec(v___x_5708_);
v___x_5712_ = lean_box(0);
v_isShared_5713_ = v_isSharedCheck_5717_;
goto v_resetjp_5711_;
}
v_resetjp_5711_:
{
lean_object* v___x_5715_; 
if (v_isShared_5713_ == 0)
{
v___x_5715_ = v___x_5712_;
goto v_reusejp_5714_;
}
else
{
lean_object* v_reuseFailAlloc_5716_; 
v_reuseFailAlloc_5716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5716_, 0, v_a_5710_);
v___x_5715_ = v_reuseFailAlloc_5716_;
goto v_reusejp_5714_;
}
v_reusejp_5714_:
{
return v___x_5715_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_5718_; lean_object* v___x_5720_; 
v_val_5718_ = lean_ctor_get(v_fst_5663_, 0);
lean_inc(v_val_5718_);
lean_dec_ref_known(v_fst_5663_, 1);
if (v_isShared_5662_ == 0)
{
lean_ctor_set(v___x_5661_, 0, v_val_5718_);
v___x_5720_ = v___x_5661_;
goto v_reusejp_5719_;
}
else
{
lean_object* v_reuseFailAlloc_5721_; 
v_reuseFailAlloc_5721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5721_, 0, v_val_5718_);
v___x_5720_ = v_reuseFailAlloc_5721_;
goto v_reusejp_5719_;
}
v_reusejp_5719_:
{
return v___x_5720_;
}
}
}
}
else
{
lean_object* v_a_5723_; lean_object* v___x_5725_; uint8_t v_isShared_5726_; uint8_t v_isSharedCheck_5730_; 
v_a_5723_ = lean_ctor_get(v___x_5658_, 0);
v_isSharedCheck_5730_ = !lean_is_exclusive(v___x_5658_);
if (v_isSharedCheck_5730_ == 0)
{
v___x_5725_ = v___x_5658_;
v_isShared_5726_ = v_isSharedCheck_5730_;
goto v_resetjp_5724_;
}
else
{
lean_inc(v_a_5723_);
lean_dec(v___x_5658_);
v___x_5725_ = lean_box(0);
v_isShared_5726_ = v_isSharedCheck_5730_;
goto v_resetjp_5724_;
}
v_resetjp_5724_:
{
lean_object* v___x_5728_; 
if (v_isShared_5726_ == 0)
{
v___x_5728_ = v___x_5725_;
goto v_reusejp_5727_;
}
else
{
lean_object* v_reuseFailAlloc_5729_; 
v_reuseFailAlloc_5729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5729_, 0, v_a_5723_);
v___x_5728_ = v_reuseFailAlloc_5729_;
goto v_reusejp_5727_;
}
v_reusejp_5727_:
{
return v___x_5728_;
}
}
}
}
}
}
else
{
lean_object* v_a_5733_; lean_object* v___x_5735_; uint8_t v_isShared_5736_; uint8_t v_isSharedCheck_5740_; 
v_a_5733_ = lean_ctor_get(v___x_5642_, 0);
v_isSharedCheck_5740_ = !lean_is_exclusive(v___x_5642_);
if (v_isSharedCheck_5740_ == 0)
{
v___x_5735_ = v___x_5642_;
v_isShared_5736_ = v_isSharedCheck_5740_;
goto v_resetjp_5734_;
}
else
{
lean_inc(v_a_5733_);
lean_dec(v___x_5642_);
v___x_5735_ = lean_box(0);
v_isShared_5736_ = v_isSharedCheck_5740_;
goto v_resetjp_5734_;
}
v_resetjp_5734_:
{
lean_object* v___x_5738_; 
if (v_isShared_5736_ == 0)
{
v___x_5738_ = v___x_5735_;
goto v_reusejp_5737_;
}
else
{
lean_object* v_reuseFailAlloc_5739_; 
v_reuseFailAlloc_5739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5739_, 0, v_a_5733_);
v___x_5738_ = v_reuseFailAlloc_5739_;
goto v_reusejp_5737_;
}
v_reusejp_5737_:
{
return v___x_5738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___boxed(lean_object* v_passes_5741_, lean_object* v_a_5742_, lean_object* v_a_5743_, lean_object* v_a_5744_, lean_object* v_a_5745_, lean_object* v_a_5746_, lean_object* v_a_5747_, lean_object* v_a_5748_, lean_object* v_a_5749_, lean_object* v_a_5750_){
_start:
{
lean_object* v_res_5751_; 
v_res_5751_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_5741_, v_a_5742_, v_a_5743_, v_a_5744_, v_a_5745_, v_a_5746_, v_a_5747_, v_a_5748_, v_a_5749_);
lean_dec(v_a_5749_);
lean_dec_ref(v_a_5748_);
lean_dec(v_a_5747_);
lean_dec_ref(v_a_5746_);
lean_dec(v_a_5745_);
lean_dec_ref(v_a_5744_);
lean_dec(v_a_5743_);
lean_dec_ref(v_a_5742_);
lean_dec(v_passes_5741_);
return v_res_5751_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(lean_object* v_cls_5752_, lean_object* v_msg_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_){
_start:
{
lean_object* v___x_5763_; 
v___x_5763_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_5752_, v_msg_5753_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_);
return v___x_5763_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___boxed(lean_object* v_cls_5764_, lean_object* v_msg_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_, lean_object* v___y_5773_, lean_object* v___y_5774_){
_start:
{
lean_object* v_res_5775_; 
v_res_5775_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(v_cls_5764_, v_msg_5765_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_, v___y_5773_);
lean_dec(v___y_5773_);
lean_dec_ref(v___y_5772_);
lean_dec(v___y_5771_);
lean_dec_ref(v___y_5770_);
lean_dec(v___y_5769_);
lean_dec_ref(v___y_5768_);
lean_dec(v___y_5767_);
lean_dec_ref(v___y_5766_);
return v_res_5775_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(lean_object* v_00_u03b1_5776_, lean_object* v_x_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_){
_start:
{
lean_object* v___x_5787_; 
v___x_5787_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_5777_);
return v___x_5787_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___boxed(lean_object* v_00_u03b1_5788_, lean_object* v_x_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_, lean_object* v___y_5798_){
_start:
{
lean_object* v_res_5799_; 
v_res_5799_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(v_00_u03b1_5788_, v_x_5789_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_, v___y_5794_, v___y_5795_, v___y_5796_, v___y_5797_);
lean_dec(v___y_5797_);
lean_dec_ref(v___y_5796_);
lean_dec(v___y_5795_);
lean_dec_ref(v___y_5794_);
lean_dec(v___y_5793_);
lean_dec_ref(v___y_5792_);
lean_dec(v___y_5791_);
lean_dec_ref(v___y_5790_);
return v_res_5799_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(lean_object* v_as_5800_, lean_object* v_as_x27_5801_, lean_object* v_b_5802_, lean_object* v_a_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_){
_start:
{
lean_object* v___x_5813_; 
v___x_5813_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_5801_, v_b_5802_, v___y_5804_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_);
return v___x_5813_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___boxed(lean_object* v_as_5814_, lean_object* v_as_x27_5815_, lean_object* v_b_5816_, lean_object* v_a_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_){
_start:
{
lean_object* v_res_5827_; 
v_res_5827_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(v_as_5814_, v_as_x27_5815_, v_b_5816_, v_a_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_);
lean_dec(v___y_5825_);
lean_dec_ref(v___y_5824_);
lean_dec(v___y_5823_);
lean_dec_ref(v___y_5822_);
lean_dec(v___y_5821_);
lean_dec_ref(v___y_5820_);
lean_dec(v___y_5819_);
lean_dec_ref(v___y_5818_);
lean_dec(v_as_x27_5815_);
lean_dec(v_as_5814_);
return v_res_5827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(lean_object* v_oldTraces_5828_, lean_object* v_data_5829_, lean_object* v_ref_5830_, lean_object* v_msg_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_){
_start:
{
lean_object* v___x_5841_; 
v___x_5841_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_5828_, v_data_5829_, v_ref_5830_, v_msg_5831_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
return v___x_5841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___boxed(lean_object* v_oldTraces_5842_, lean_object* v_data_5843_, lean_object* v_ref_5844_, lean_object* v_msg_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_, lean_object* v___y_5848_, lean_object* v___y_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_, lean_object* v___y_5853_, lean_object* v___y_5854_){
_start:
{
lean_object* v_res_5855_; 
v_res_5855_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(v_oldTraces_5842_, v_data_5843_, v_ref_5844_, v_msg_5845_, v___y_5846_, v___y_5847_, v___y_5848_, v___y_5849_, v___y_5850_, v___y_5851_, v___y_5852_, v___y_5853_);
lean_dec(v___y_5853_);
lean_dec_ref(v___y_5852_);
lean_dec(v___y_5851_);
lean_dec_ref(v___y_5850_);
lean_dec(v___y_5849_);
lean_dec_ref(v___y_5848_);
lean_dec(v___y_5847_);
lean_dec_ref(v___y_5846_);
return v_res_5855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object* v_passes_5856_, lean_object* v_a_5857_, lean_object* v_a_5858_, lean_object* v_a_5859_, lean_object* v_a_5860_, lean_object* v_a_5861_, lean_object* v_a_5862_, lean_object* v_a_5863_, lean_object* v_a_5864_){
_start:
{
lean_object* v___x_5866_; 
v___x_5866_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_5856_, v_a_5857_, v_a_5858_, v_a_5859_, v_a_5860_, v_a_5861_, v_a_5862_, v_a_5863_, v_a_5864_);
if (lean_obj_tag(v___x_5866_) == 0)
{
lean_object* v_a_5867_; lean_object* v___x_5868_; lean_object* v___x_5870_; uint8_t v_isShared_5871_; uint8_t v_isSharedCheck_5875_; 
v_a_5867_ = lean_ctor_get(v___x_5866_, 0);
lean_inc(v_a_5867_);
lean_dec_ref_known(v___x_5866_, 1);
v___x_5868_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg(v_a_5858_);
v_isSharedCheck_5875_ = !lean_is_exclusive(v___x_5868_);
if (v_isSharedCheck_5875_ == 0)
{
lean_object* v_unused_5876_; 
v_unused_5876_ = lean_ctor_get(v___x_5868_, 0);
lean_dec(v_unused_5876_);
v___x_5870_ = v___x_5868_;
v_isShared_5871_ = v_isSharedCheck_5875_;
goto v_resetjp_5869_;
}
else
{
lean_dec(v___x_5868_);
v___x_5870_ = lean_box(0);
v_isShared_5871_ = v_isSharedCheck_5875_;
goto v_resetjp_5869_;
}
v_resetjp_5869_:
{
lean_object* v___x_5873_; 
if (v_isShared_5871_ == 0)
{
lean_ctor_set(v___x_5870_, 0, v_a_5867_);
v___x_5873_ = v___x_5870_;
goto v_reusejp_5872_;
}
else
{
lean_object* v_reuseFailAlloc_5874_; 
v_reuseFailAlloc_5874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5874_, 0, v_a_5867_);
v___x_5873_ = v_reuseFailAlloc_5874_;
goto v_reusejp_5872_;
}
v_reusejp_5872_:
{
return v___x_5873_;
}
}
}
else
{
return v___x_5866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___boxed(lean_object* v_passes_5877_, lean_object* v_a_5878_, lean_object* v_a_5879_, lean_object* v_a_5880_, lean_object* v_a_5881_, lean_object* v_a_5882_, lean_object* v_a_5883_, lean_object* v_a_5884_, lean_object* v_a_5885_, lean_object* v_a_5886_){
_start:
{
lean_object* v_res_5887_; 
v_res_5887_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_passes_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_);
lean_dec(v_a_5885_);
lean_dec_ref(v_a_5884_);
lean_dec(v_a_5883_);
lean_dec_ref(v_a_5882_);
lean_dec(v_a_5881_);
lean_dec_ref(v_a_5880_);
lean_dec(v_a_5879_);
lean_dec_ref(v_a_5878_);
lean_dec(v_passes_5877_);
return v_res_5887_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Result(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default = _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default);
l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp = _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Attr(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_Result(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
