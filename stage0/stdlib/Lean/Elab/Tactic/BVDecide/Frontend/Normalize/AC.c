// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.Normalize.AC
// Imports: public import Lean.Meta.Tactic.AC.Main public import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_instReprExpr_repr(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_AC_rewriteUnnormalizedRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_merge___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
extern lean_object* l_Lean_Meta_Simp_neutralConfig;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_io_mono_nanos_now();
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_checkEmoji;
lean_object* l_Lean_Meta_Simp_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_applySimpResultToLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instMul"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 82, 7, 193, 128, 145, 145, 228)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Op.mul"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_neutralElement(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_instToMessageData___lam__0(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_instToMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_instToMessageData___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_instToMessageData___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_instToMessageData___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_instToMessageData = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_instToMessageData___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "internal error (this is a bug!): index "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = " out of range, the current state only has "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " variables:\n\n"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0___boxed(lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Found binary operation '"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__8;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "', expected '"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__12;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "'.Treating as atom."};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__13_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "canonicalizeWithSharing"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Operations mismatch:\n      the left-hand-side has operation "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\n        "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "\n      but the right-hand-side has operation "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8;
static const lean_array_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Canonicalizing with respect to operation: '"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "'."};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Failed to recognize operation: "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__3___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3_value)} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Canonicalizing: "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__2_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__3_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_ac_nf "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " found `BEq.beq`."};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__10;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__11;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " found `Eq`."};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__13;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__2___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__3___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__9;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__10;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__0(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__0___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__0___boxed__const__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__0___boxed__const__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__0___boxed, .m_arity = 9, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__0___boxed__const__1_value)} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__0_value;
static const lean_array_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__2___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bv_ac_nf"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(186, 2, 240, 42, 244, 93, 182, 215)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__3_value;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType(lean_object* v_w_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__2);
v___x_9_ = l_Lean_Expr_app___override(v___x_8_, v_w_7_);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = lean_box(0);
v___x_15_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__1));
v___x_16_ = l_Lean_Expr_const___override(v___x_15_, v___x_14_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul(lean_object* v_w_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__2);
v___x_19_ = l_Lean_Expr_app___override(v___x_18_, v_w_17_);
return v___x_19_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__3(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_26_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__2));
v___x_27_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__1));
v___x_28_ = l_Lean_mkConst(v___x_27_, v___x_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul(lean_object* v_w_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_30_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__3);
lean_inc_ref(v_w_29_);
v___x_31_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType(v_w_29_);
v___x_32_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul(v_w_29_);
v___x_33_ = l_Lean_mkAppB(v___x_30_, v___x_31_, v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__2(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_box(0);
v___x_39_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__1));
v___x_40_ = l_Lean_mkConst(v___x_39_, v___x_38_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit(lean_object* v_w_41_, lean_object* v_n_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__2);
v___x_44_ = l_Lean_mkNatLit(v_n_42_);
v___x_45_ = l_Lean_mkAppB(v___x_43_, v_w_41_, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp_beq(lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
uint8_t v___x_48_; 
v___x_48_ = lean_expr_eqv(v_x_46_, v_x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp_beq___boxed(lean_object* v_x_49_, lean_object* v_x_50_){
_start:
{
uint8_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp_beq(v_x_49_, v_x_50_);
lean_dec_ref(v_x_50_);
lean_dec_ref(v_x_49_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__3(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(2u);
v___x_62_ = lean_nat_to_int(v___x_61_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__4(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_unsigned_to_nat(1u);
v___x_64_ = lean_nat_to_int(v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr(lean_object* v_x_65_, lean_object* v_prec_66_){
_start:
{
lean_object* v___y_68_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(1024u);
v___x_78_ = lean_nat_dec_le(v___x_77_, v_prec_66_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
v___x_79_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__3);
v___y_68_ = v___x_79_;
goto v___jp_67_;
}
else
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__4);
v___y_68_ = v___x_80_;
goto v___jp_67_;
}
v___jp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_69_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__2));
v___x_70_ = lean_unsigned_to_nat(1024u);
v___x_71_ = l_Lean_instReprExpr_repr(v_x_65_, v___x_70_);
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_69_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
lean_inc(v___y_68_);
v___x_73_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_73_, 0, v___y_68_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = 0;
v___x_75_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_75_, 0, v___x_73_);
lean_ctor_set_uint8(v___x_75_, sizeof(void*)*1, v___x_74_);
v___x_76_ = l_Repr_addAppParen(v___x_75_, v_prec_66_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___boxed(lean_object* v_x_81_, lean_object* v_prec_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr(v_x_81_, v_prec_82_);
lean_dec(v_prec_82_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f(lean_object* v_e_91_){
_start:
{
lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_92_ = l_Lean_Expr_cleanupAnnotations(v_e_91_);
v___x_93_ = l_Lean_Expr_isApp(v___x_92_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
lean_dec_ref(v___x_92_);
v___x_94_ = lean_box(0);
return v___x_94_;
}
else
{
lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_95_ = l_Lean_Expr_appFnCleanup___redArg(v___x_92_);
v___x_96_ = l_Lean_Expr_isApp(v___x_95_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
lean_dec_ref(v___x_95_);
v___x_97_ = lean_box(0);
return v___x_97_;
}
else
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = l_Lean_Expr_appFnCleanup___redArg(v___x_95_);
v___x_99_ = l_Lean_Expr_isApp(v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
lean_dec_ref(v___x_98_);
v___x_100_ = lean_box(0);
return v___x_100_;
}
else
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = l_Lean_Expr_appFnCleanup___redArg(v___x_98_);
v___x_102_ = l_Lean_Expr_isApp(v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
lean_dec_ref(v___x_101_);
v___x_103_ = lean_box(0);
return v___x_103_;
}
else
{
lean_object* v_arg_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v_arg_104_ = lean_ctor_get(v___x_101_, 1);
lean_inc_ref(v_arg_104_);
v___x_105_ = l_Lean_Expr_appFnCleanup___redArg(v___x_101_);
v___x_106_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__2));
v___x_107_ = l_Lean_Expr_isConstOf(v___x_105_, v___x_106_);
lean_dec_ref(v___x_105_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
lean_dec_ref(v_arg_104_);
v___x_108_ = lean_box(0);
return v___x_108_;
}
else
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = l_Lean_Expr_cleanupAnnotations(v_arg_104_);
v___x_110_ = l_Lean_Expr_isApp(v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; 
lean_dec_ref(v___x_109_);
v___x_111_ = lean_box(0);
return v___x_111_;
}
else
{
lean_object* v_arg_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v_arg_112_ = lean_ctor_get(v___x_109_, 1);
lean_inc_ref(v_arg_112_);
v___x_113_ = l_Lean_Expr_appFnCleanup___redArg(v___x_109_);
v___x_114_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__1));
v___x_115_ = l_Lean_Expr_isConstOf(v___x_113_, v___x_114_);
lean_dec_ref(v___x_113_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; 
lean_dec_ref(v_arg_112_);
v___x_116_ = lean_box(0);
return v___x_116_;
}
else
{
lean_object* v___x_117_; 
v___x_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_117_, 0, v_arg_112_);
return v___x_117_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(lean_object* v_x_118_){
_start:
{
if (lean_obj_tag(v_x_118_) == 5)
{
lean_object* v_fn_119_; 
v_fn_119_ = lean_ctor_get(v_x_118_, 0);
lean_inc_ref(v_fn_119_);
lean_dec_ref(v_x_118_);
if (lean_obj_tag(v_fn_119_) == 5)
{
lean_object* v_fn_120_; lean_object* v___x_121_; 
v_fn_120_ = lean_ctor_get(v_fn_119_, 0);
lean_inc_ref(v_fn_120_);
lean_dec_ref(v_fn_119_);
v___x_121_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f(v_fn_120_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; 
lean_dec_ref(v_fn_119_);
v___x_122_ = lean_box(0);
return v___x_122_;
}
}
else
{
lean_object* v___x_123_; 
lean_dec_ref(v_x_118_);
v___x_123_ = lean_box(0);
return v___x_123_;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = l_Lean_Level_ofNat(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__1(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = lean_box(0);
v___x_127_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0);
v___x_128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__2(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__1);
v___x_130_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0);
v___x_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___x_129_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__3(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__2);
v___x_133_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0);
v___x_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_132_);
return v___x_134_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__4(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__3);
v___x_136_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__2));
v___x_137_ = l_Lean_mkConst(v___x_136_, v___x_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(lean_object* v_x_138_){
_start:
{
lean_object* v_bv_139_; lean_object* v_inst_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
lean_inc_ref(v_x_138_);
v_bv_139_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType(v_x_138_);
v_inst_140_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul(v_x_138_);
v___x_141_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__4);
lean_inc_ref_n(v_bv_139_, 2);
v___x_142_ = l_Lean_mkApp4(v___x_141_, v_bv_139_, v_bv_139_, v_bv_139_, v_inst_140_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_neutralElement(lean_object* v_x_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit(v_x_143_, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind___redArg(lean_object* v_op_x27_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f(v_op_x27_146_);
if (lean_obj_tag(v___x_147_) == 1)
{
uint8_t v___x_148_; 
lean_dec_ref(v___x_147_);
v___x_148_ = 1;
return v___x_148_;
}
else
{
uint8_t v___x_149_; 
lean_dec(v___x_147_);
v___x_149_ = 0;
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind___redArg___boxed(lean_object* v_op_x27_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind___redArg(v_op_x27_150_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind(lean_object* v_op_153_, lean_object* v_op_x27_154_){
_start:
{
uint8_t v___x_155_; 
v___x_155_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind___redArg(v_op_x27_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind___boxed(lean_object* v_op_156_, lean_object* v_op_x27_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind(v_op_156_, v_op_x27_157_);
lean_dec_ref(v_op_156_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_instToMessageData___lam__0(lean_object* v_op_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_op_160_);
v___x_162_ = l_Lean_MessageData_ofExpr(v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg(lean_object* v_x_165_, lean_object* v_s_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v___x_172_; 
lean_inc(v_a_170_);
lean_inc_ref(v_a_169_);
lean_inc(v_a_168_);
lean_inc_ref(v_a_167_);
v___x_172_ = lean_apply_6(v_x_165_, v_s_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, lean_box(0));
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_181_; 
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
lean_object* v_fst_177_; lean_object* v___x_179_; 
v_fst_177_ = lean_ctor_get(v_a_173_, 0);
lean_inc(v_fst_177_);
lean_dec(v_a_173_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v_fst_177_);
v___x_179_ = v___x_175_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_fst_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
v_a_182_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___x_172_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_172_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg___boxed(lean_object* v_x_190_, lean_object* v_s_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg(v_x_190_, v_s_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27(lean_object* v_00_u03b1_198_, lean_object* v_x_199_, lean_object* v_s_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg(v_x_199_, v_s_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___boxed(lean_object* v_00_u03b1_207_, lean_object* v_x_208_, lean_object* v_s_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27(v_00_u03b1_207_, v_x_208_, v_s_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(lean_object* v_a_216_, lean_object* v_x_217_){
_start:
{
if (lean_obj_tag(v_x_217_) == 0)
{
lean_object* v___x_218_; 
v___x_218_ = lean_box(0);
return v___x_218_;
}
else
{
lean_object* v_key_219_; lean_object* v_value_220_; lean_object* v_tail_221_; uint8_t v___x_222_; 
v_key_219_ = lean_ctor_get(v_x_217_, 0);
v_value_220_ = lean_ctor_get(v_x_217_, 1);
v_tail_221_ = lean_ctor_get(v_x_217_, 2);
v___x_222_ = lean_expr_eqv(v_key_219_, v_a_216_);
if (v___x_222_ == 0)
{
v_x_217_ = v_tail_221_;
goto _start;
}
else
{
lean_object* v___x_224_; 
lean_inc(v_value_220_);
v___x_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_224_, 0, v_value_220_);
return v___x_224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_225_, lean_object* v_x_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_225_, v_x_226_);
lean_dec(v_x_226_);
lean_dec_ref(v_a_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0___redArg(lean_object* v_m_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_buckets_230_; lean_object* v___x_231_; uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v_fold_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; size_t v___x_239_; size_t v___x_240_; size_t v___x_241_; size_t v___x_242_; size_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_buckets_230_ = lean_ctor_get(v_m_228_, 1);
v___x_231_ = lean_array_get_size(v_buckets_230_);
v___x_232_ = l_Lean_Expr_hash(v_a_229_);
v___x_233_ = 32ULL;
v___x_234_ = lean_uint64_shift_right(v___x_232_, v___x_233_);
v_fold_235_ = lean_uint64_xor(v___x_232_, v___x_234_);
v___x_236_ = 16ULL;
v___x_237_ = lean_uint64_shift_right(v_fold_235_, v___x_236_);
v___x_238_ = lean_uint64_xor(v_fold_235_, v___x_237_);
v___x_239_ = lean_uint64_to_usize(v___x_238_);
v___x_240_ = lean_usize_of_nat(v___x_231_);
v___x_241_ = ((size_t)1ULL);
v___x_242_ = lean_usize_sub(v___x_240_, v___x_241_);
v___x_243_ = lean_usize_land(v___x_239_, v___x_242_);
v___x_244_ = lean_array_uget_borrowed(v_buckets_230_, v___x_243_);
v___x_245_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_229_, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0___redArg___boxed(lean_object* v_m_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0___redArg(v_m_246_, v_a_247_);
lean_dec_ref(v_a_247_);
lean_dec_ref(v_m_246_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
if (lean_obj_tag(v_x_250_) == 0)
{
return v_x_249_;
}
else
{
lean_object* v_key_251_; lean_object* v_value_252_; lean_object* v_tail_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_276_; 
v_key_251_ = lean_ctor_get(v_x_250_, 0);
v_value_252_ = lean_ctor_get(v_x_250_, 1);
v_tail_253_ = lean_ctor_get(v_x_250_, 2);
v_isSharedCheck_276_ = !lean_is_exclusive(v_x_250_);
if (v_isSharedCheck_276_ == 0)
{
v___x_255_ = v_x_250_;
v_isShared_256_ = v_isSharedCheck_276_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_tail_253_);
lean_inc(v_value_252_);
lean_inc(v_key_251_);
lean_dec(v_x_250_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_276_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; uint64_t v___x_258_; uint64_t v___x_259_; uint64_t v___x_260_; uint64_t v_fold_261_; uint64_t v___x_262_; uint64_t v___x_263_; uint64_t v___x_264_; size_t v___x_265_; size_t v___x_266_; size_t v___x_267_; size_t v___x_268_; size_t v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_257_ = lean_array_get_size(v_x_249_);
v___x_258_ = l_Lean_Expr_hash(v_key_251_);
v___x_259_ = 32ULL;
v___x_260_ = lean_uint64_shift_right(v___x_258_, v___x_259_);
v_fold_261_ = lean_uint64_xor(v___x_258_, v___x_260_);
v___x_262_ = 16ULL;
v___x_263_ = lean_uint64_shift_right(v_fold_261_, v___x_262_);
v___x_264_ = lean_uint64_xor(v_fold_261_, v___x_263_);
v___x_265_ = lean_uint64_to_usize(v___x_264_);
v___x_266_ = lean_usize_of_nat(v___x_257_);
v___x_267_ = ((size_t)1ULL);
v___x_268_ = lean_usize_sub(v___x_266_, v___x_267_);
v___x_269_ = lean_usize_land(v___x_265_, v___x_268_);
v___x_270_ = lean_array_uget_borrowed(v_x_249_, v___x_269_);
lean_inc(v___x_270_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 2, v___x_270_);
v___x_272_ = v___x_255_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_key_251_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_value_252_);
lean_ctor_set(v_reuseFailAlloc_275_, 2, v___x_270_);
v___x_272_ = v_reuseFailAlloc_275_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_273_; 
v___x_273_ = lean_array_uset(v_x_249_, v___x_269_, v___x_272_);
v_x_249_ = v___x_273_;
v_x_250_ = v_tail_253_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(lean_object* v_i_277_, lean_object* v_source_278_, lean_object* v_target_279_){
_start:
{
lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_280_ = lean_array_get_size(v_source_278_);
v___x_281_ = lean_nat_dec_lt(v_i_277_, v___x_280_);
if (v___x_281_ == 0)
{
lean_dec_ref(v_source_278_);
lean_dec(v_i_277_);
return v_target_279_;
}
else
{
lean_object* v_es_282_; lean_object* v___x_283_; lean_object* v_source_284_; lean_object* v_target_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_es_282_ = lean_array_fget(v_source_278_, v_i_277_);
v___x_283_ = lean_box(0);
v_source_284_ = lean_array_fset(v_source_278_, v_i_277_, v___x_283_);
v_target_285_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(v_target_279_, v_es_282_);
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_nat_add(v_i_277_, v___x_286_);
lean_dec(v_i_277_);
v_i_277_ = v___x_287_;
v_source_278_ = v_source_284_;
v_target_279_ = v_target_285_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(lean_object* v_data_289_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v_nbuckets_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_290_ = lean_array_get_size(v_data_289_);
v___x_291_ = lean_unsigned_to_nat(2u);
v_nbuckets_292_ = lean_nat_mul(v___x_290_, v___x_291_);
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = lean_box(0);
v___x_295_ = lean_mk_array(v_nbuckets_292_, v___x_294_);
v___x_296_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(v___x_293_, v_data_289_, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(lean_object* v_a_297_, lean_object* v_b_298_, lean_object* v_x_299_){
_start:
{
if (lean_obj_tag(v_x_299_) == 0)
{
lean_dec(v_b_298_);
lean_dec_ref(v_a_297_);
return v_x_299_;
}
else
{
lean_object* v_key_300_; lean_object* v_value_301_; lean_object* v_tail_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_314_; 
v_key_300_ = lean_ctor_get(v_x_299_, 0);
v_value_301_ = lean_ctor_get(v_x_299_, 1);
v_tail_302_ = lean_ctor_get(v_x_299_, 2);
v_isSharedCheck_314_ = !lean_is_exclusive(v_x_299_);
if (v_isSharedCheck_314_ == 0)
{
v___x_304_ = v_x_299_;
v_isShared_305_ = v_isSharedCheck_314_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_tail_302_);
lean_inc(v_value_301_);
lean_inc(v_key_300_);
lean_dec(v_x_299_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_314_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
uint8_t v___x_306_; 
v___x_306_ = lean_expr_eqv(v_key_300_, v_a_297_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_307_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_297_, v_b_298_, v_tail_302_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 2, v___x_307_);
v___x_309_ = v___x_304_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_key_300_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_value_301_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
else
{
lean_object* v___x_312_; 
lean_dec(v_value_301_);
lean_dec(v_key_300_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 1, v_b_298_);
lean_ctor_set(v___x_304_, 0, v_a_297_);
v___x_312_ = v___x_304_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_297_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_b_298_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_tail_302_);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(lean_object* v_a_315_, lean_object* v_x_316_){
_start:
{
if (lean_obj_tag(v_x_316_) == 0)
{
uint8_t v___x_317_; 
v___x_317_ = 0;
return v___x_317_;
}
else
{
lean_object* v_key_318_; lean_object* v_tail_319_; uint8_t v___x_320_; 
v_key_318_ = lean_ctor_get(v_x_316_, 0);
v_tail_319_ = lean_ctor_get(v_x_316_, 2);
v___x_320_ = lean_expr_eqv(v_key_318_, v_a_315_);
if (v___x_320_ == 0)
{
v_x_316_ = v_tail_319_;
goto _start;
}
else
{
return v___x_320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg___boxed(lean_object* v_a_322_, lean_object* v_x_323_){
_start:
{
uint8_t v_res_324_; lean_object* v_r_325_; 
v_res_324_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_322_, v_x_323_);
lean_dec(v_x_323_);
lean_dec_ref(v_a_322_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1___redArg(lean_object* v_m_326_, lean_object* v_a_327_, lean_object* v_b_328_){
_start:
{
lean_object* v_size_329_; lean_object* v_buckets_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_373_; 
v_size_329_ = lean_ctor_get(v_m_326_, 0);
v_buckets_330_ = lean_ctor_get(v_m_326_, 1);
v_isSharedCheck_373_ = !lean_is_exclusive(v_m_326_);
if (v_isSharedCheck_373_ == 0)
{
v___x_332_ = v_m_326_;
v_isShared_333_ = v_isSharedCheck_373_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_buckets_330_);
lean_inc(v_size_329_);
lean_dec(v_m_326_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_373_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v_fold_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v___x_345_; size_t v___x_346_; lean_object* v_bkt_347_; uint8_t v___x_348_; 
v___x_334_ = lean_array_get_size(v_buckets_330_);
v___x_335_ = l_Lean_Expr_hash(v_a_327_);
v___x_336_ = 32ULL;
v___x_337_ = lean_uint64_shift_right(v___x_335_, v___x_336_);
v_fold_338_ = lean_uint64_xor(v___x_335_, v___x_337_);
v___x_339_ = 16ULL;
v___x_340_ = lean_uint64_shift_right(v_fold_338_, v___x_339_);
v___x_341_ = lean_uint64_xor(v_fold_338_, v___x_340_);
v___x_342_ = lean_uint64_to_usize(v___x_341_);
v___x_343_ = lean_usize_of_nat(v___x_334_);
v___x_344_ = ((size_t)1ULL);
v___x_345_ = lean_usize_sub(v___x_343_, v___x_344_);
v___x_346_ = lean_usize_land(v___x_342_, v___x_345_);
v_bkt_347_ = lean_array_uget_borrowed(v_buckets_330_, v___x_346_);
v___x_348_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_327_, v_bkt_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v_size_x27_350_; lean_object* v___x_351_; lean_object* v_buckets_x27_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_349_ = lean_unsigned_to_nat(1u);
v_size_x27_350_ = lean_nat_add(v_size_329_, v___x_349_);
lean_dec(v_size_329_);
lean_inc(v_bkt_347_);
v___x_351_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_351_, 0, v_a_327_);
lean_ctor_set(v___x_351_, 1, v_b_328_);
lean_ctor_set(v___x_351_, 2, v_bkt_347_);
v_buckets_x27_352_ = lean_array_uset(v_buckets_330_, v___x_346_, v___x_351_);
v___x_353_ = lean_unsigned_to_nat(4u);
v___x_354_ = lean_nat_mul(v_size_x27_350_, v___x_353_);
v___x_355_ = lean_unsigned_to_nat(3u);
v___x_356_ = lean_nat_div(v___x_354_, v___x_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_array_get_size(v_buckets_x27_352_);
v___x_358_ = lean_nat_dec_le(v___x_356_, v___x_357_);
lean_dec(v___x_356_);
if (v___x_358_ == 0)
{
lean_object* v_val_359_; lean_object* v___x_361_; 
v_val_359_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(v_buckets_x27_352_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v_val_359_);
lean_ctor_set(v___x_332_, 0, v_size_x27_350_);
v___x_361_ = v___x_332_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_size_x27_350_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_val_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
else
{
lean_object* v___x_364_; 
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v_buckets_x27_352_);
lean_ctor_set(v___x_332_, 0, v_size_x27_350_);
v___x_364_ = v___x_332_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_size_x27_350_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_buckets_x27_352_);
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
lean_object* v___x_366_; lean_object* v_buckets_x27_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
lean_inc(v_bkt_347_);
v___x_366_ = lean_box(0);
v_buckets_x27_367_ = lean_array_uset(v_buckets_330_, v___x_346_, v___x_366_);
v___x_368_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_327_, v_b_328_, v_bkt_347_);
v___x_369_ = lean_array_uset(v_buckets_x27_367_, v___x_346_, v___x_368_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v___x_369_);
v___x_371_ = v___x_332_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_size_329_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v___x_369_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar___redArg(lean_object* v_e_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_op_377_; lean_object* v_exprToVarIndex_378_; lean_object* v_varToExpr_379_; lean_object* v___x_380_; 
v_op_377_ = lean_ctor_get(v_a_375_, 0);
v_exprToVarIndex_378_ = lean_ctor_get(v_a_375_, 1);
v_varToExpr_379_ = lean_ctor_get(v_a_375_, 2);
v___x_380_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0___redArg(v_exprToVarIndex_378_, v_e_374_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_392_; 
lean_inc_ref(v_varToExpr_379_);
lean_inc_ref(v_exprToVarIndex_378_);
lean_inc_ref(v_op_377_);
v_isSharedCheck_392_ = !lean_is_exclusive(v_a_375_);
if (v_isSharedCheck_392_ == 0)
{
lean_object* v_unused_393_; lean_object* v_unused_394_; lean_object* v_unused_395_; 
v_unused_393_ = lean_ctor_get(v_a_375_, 2);
lean_dec(v_unused_393_);
v_unused_394_ = lean_ctor_get(v_a_375_, 1);
lean_dec(v_unused_394_);
v_unused_395_ = lean_ctor_get(v_a_375_, 0);
lean_dec(v_unused_395_);
v___x_382_ = v_a_375_;
v_isShared_383_ = v_isSharedCheck_392_;
goto v_resetjp_381_;
}
else
{
lean_dec(v_a_375_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_392_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v_size_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v_size_384_ = lean_ctor_get(v_exprToVarIndex_378_, 0);
lean_inc_n(v_size_384_, 2);
lean_inc_ref(v_e_374_);
v___x_385_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1___redArg(v_exprToVarIndex_378_, v_e_374_, v_size_384_);
v___x_386_ = lean_array_push(v_varToExpr_379_, v_e_374_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 2, v___x_386_);
lean_ctor_set(v___x_382_, 1, v___x_385_);
v___x_388_ = v___x_382_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_op_377_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_391_, 2, v___x_386_);
v___x_388_ = v_reuseFailAlloc_391_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v_size_384_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
}
}
else
{
lean_object* v_val_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_404_; 
lean_dec_ref(v_e_374_);
v_val_396_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_404_ == 0)
{
v___x_398_ = v___x_380_;
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_val_396_);
lean_dec(v___x_380_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v_val_396_);
lean_ctor_set(v___x_400_, 1, v_a_375_);
if (v_isShared_399_ == 0)
{
lean_ctor_set_tag(v___x_398_, 0);
lean_ctor_set(v___x_398_, 0, v___x_400_);
v___x_402_ = v___x_398_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar___redArg___boxed(lean_object* v_e_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar___redArg(v_e_405_, v_a_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar(lean_object* v_e_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar___redArg(v_e_409_, v_a_410_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar___boxed(lean_object* v_e_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar(v_e_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0(lean_object* v_00_u03b2_425_, lean_object* v_m_426_, lean_object* v_a_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0___redArg(v_m_426_, v_a_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0___boxed(lean_object* v_00_u03b2_429_, lean_object* v_m_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0(v_00_u03b2_429_, v_m_430_, v_a_431_);
lean_dec_ref(v_a_431_);
lean_dec_ref(v_m_430_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1(lean_object* v_00_u03b2_433_, lean_object* v_m_434_, lean_object* v_a_435_, lean_object* v_b_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1___redArg(v_m_434_, v_a_435_, v_b_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0(lean_object* v_00_u03b2_438_, lean_object* v_a_439_, lean_object* v_x_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_439_, v_x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_442_, lean_object* v_a_443_, lean_object* v_x_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0(v_00_u03b2_442_, v_a_443_, v_x_444_);
lean_dec(v_x_444_);
lean_dec_ref(v_a_443_);
return v_res_445_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2(lean_object* v_00_u03b2_446_, lean_object* v_a_447_, lean_object* v_x_448_){
_start:
{
uint8_t v___x_449_; 
v___x_449_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_447_, v_x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_450_, lean_object* v_a_451_, lean_object* v_x_452_){
_start:
{
uint8_t v_res_453_; lean_object* v_r_454_; 
v_res_453_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2(v_00_u03b2_450_, v_a_451_, v_x_452_);
lean_dec(v_x_452_);
lean_dec_ref(v_a_451_);
v_r_454_ = lean_box(v_res_453_);
return v_r_454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3(lean_object* v_00_u03b2_455_, lean_object* v_data_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(v_data_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__4(lean_object* v_00_u03b2_458_, lean_object* v_a_459_, lean_object* v_b_460_, lean_object* v_x_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_459_, v_b_460_, v_x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_463_, lean_object* v_i_464_, lean_object* v_source_465_, lean_object* v_target_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(v_i_464_, v_source_465_, v_target_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_468_, lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(v_x_469_, v_x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1(lean_object* v_msgData_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v___x_478_; lean_object* v_env_479_; lean_object* v___x_480_; lean_object* v_mctx_481_; lean_object* v_lctx_482_; lean_object* v_options_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_478_ = lean_st_ref_get(v___y_476_);
v_env_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc_ref(v_env_479_);
lean_dec(v___x_478_);
v___x_480_ = lean_st_ref_get(v___y_474_);
v_mctx_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc_ref(v_mctx_481_);
lean_dec(v___x_480_);
v_lctx_482_ = lean_ctor_get(v___y_473_, 2);
v_options_483_ = lean_ctor_get(v___y_475_, 2);
lean_inc_ref(v_options_483_);
lean_inc_ref(v_lctx_482_);
v___x_484_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_484_, 0, v_env_479_);
lean_ctor_set(v___x_484_, 1, v_mctx_481_);
lean_ctor_set(v___x_484_, 2, v_lctx_482_);
lean_ctor_set(v___x_484_, 3, v_options_483_);
v___x_485_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v_msgData_472_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1___boxed(lean_object* v_msgData_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msgData_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1___redArg(lean_object* v_msg_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_ref_500_; lean_object* v___x_501_; lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_510_; 
v_ref_500_ = lean_ctor_get(v___y_497_, 5);
v___x_501_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_510_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_510_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_510_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; lean_object* v___x_508_; 
lean_inc(v_ref_500_);
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v_ref_500_);
lean_ctor_set(v___x_506_, 1, v_a_502_);
if (v_isShared_505_ == 0)
{
lean_ctor_set_tag(v___x_504_, 1);
lean_ctor_set(v___x_504_, 0, v___x_506_);
v___x_508_ = v___x_504_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1___redArg___boxed(lean_object* v_msg_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__0(lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
if (lean_obj_tag(v_a_518_) == 0)
{
lean_object* v___x_520_; 
v___x_520_ = l_List_reverse___redArg(v_a_519_);
return v___x_520_;
}
else
{
lean_object* v_head_521_; lean_object* v_tail_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_531_; 
v_head_521_ = lean_ctor_get(v_a_518_, 0);
v_tail_522_ = lean_ctor_get(v_a_518_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_a_518_);
if (v_isSharedCheck_531_ == 0)
{
v___x_524_ = v_a_518_;
v_isShared_525_ = v_isSharedCheck_531_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_tail_522_);
lean_inc(v_head_521_);
lean_dec(v_a_518_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_531_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = l_Lean_MessageData_ofExpr(v_head_521_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 1, v_a_519_);
lean_ctor_set(v___x_524_, 0, v___x_526_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_a_519_);
v___x_528_ = v_reuseFailAlloc_530_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
v_a_518_ = v_tail_522_;
v_a_519_ = v___x_528_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__1(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__0));
v___x_534_ = l_Lean_stringToMessageData(v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__3(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__2));
v___x_537_ = l_Lean_stringToMessageData(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__5(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__4));
v___x_540_ = l_Lean_stringToMessageData(v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr(lean_object* v_idx_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_varToExpr_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v_varToExpr_548_ = lean_ctor_get(v_a_542_, 2);
v___x_549_ = lean_array_get_size(v_varToExpr_548_);
v___x_550_ = lean_nat_dec_lt(v_idx_541_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
lean_inc_ref(v_varToExpr_548_);
lean_dec_ref(v_a_542_);
v___x_551_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__1);
v___x_552_ = l_Nat_reprFast(v_idx_541_);
v___x_553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
v___x_554_ = l_Lean_MessageData_ofFormat(v___x_553_);
v___x_555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_551_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__3);
v___x_557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = l_Nat_reprFast(v___x_549_);
v___x_559_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
v___x_560_ = l_Lean_MessageData_ofFormat(v___x_559_);
v___x_561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_557_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__5);
v___x_563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_561_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = lean_array_to_list(v_varToExpr_548_);
v___x_565_ = lean_box(0);
v___x_566_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__0(v___x_564_, v___x_565_);
v___x_567_ = l_Lean_MessageData_ofList(v___x_566_);
v___x_568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_563_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1___redArg(v___x_568_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
return v___x_569_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = lean_array_fget(v_varToExpr_548_, v_idx_541_);
lean_dec(v_idx_541_);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v_a_542_);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___boxed(lean_object* v_idx_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr(v_idx_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1(lean_object* v_00_u03b1_581_, lean_object* v_msg_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_582_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1___boxed(lean_object* v_00_u03b1_590_, lean_object* v_msg_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1(v_00_u03b1_590_, v_msg_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec_ref(v___y_592_);
return v_res_598_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(lean_object* v_a_599_, lean_object* v_x_600_){
_start:
{
if (lean_obj_tag(v_x_600_) == 0)
{
uint8_t v___x_601_; 
v___x_601_ = 0;
return v___x_601_;
}
else
{
lean_object* v_key_602_; lean_object* v_tail_603_; uint8_t v___x_604_; 
v_key_602_ = lean_ctor_get(v_x_600_, 0);
v_tail_603_ = lean_ctor_get(v_x_600_, 2);
v___x_604_ = lean_nat_dec_eq(v_key_602_, v_a_599_);
if (v___x_604_ == 0)
{
v_x_600_ = v_tail_603_;
goto _start;
}
else
{
return v___x_604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_606_, lean_object* v_x_607_){
_start:
{
uint8_t v_res_608_; lean_object* v_r_609_; 
v_res_608_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_606_, v_x_607_);
lean_dec(v_x_607_);
lean_dec(v_a_606_);
v_r_609_ = lean_box(v_res_608_);
return v_r_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(lean_object* v_c_610_){
_start:
{
lean_object* v___y_612_; 
if (lean_obj_tag(v_c_610_) == 0)
{
lean_object* v___x_616_; 
v___x_616_ = lean_unsigned_to_nat(0u);
v___y_612_ = v___x_616_;
goto v___jp_611_;
}
else
{
lean_object* v_val_617_; 
v_val_617_ = lean_ctor_get(v_c_610_, 0);
v___y_612_ = v_val_617_;
goto v___jp_611_;
}
v___jp_611_:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = lean_nat_add(v___y_612_, v___x_613_);
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0___boxed(lean_object* v_c_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v_c_618_);
lean_dec(v_c_618_);
return v_res_619_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_box(0);
v___x_621_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(lean_object* v_a_622_, lean_object* v_x_623_){
_start:
{
if (lean_obj_tag(v_x_623_) == 0)
{
lean_object* v___x_624_; lean_object* v_val_625_; lean_object* v___x_626_; 
v___x_624_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0, &l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0);
v_val_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_val_625_);
v___x_626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_626_, 0, v_a_622_);
lean_ctor_set(v___x_626_, 1, v_val_625_);
lean_ctor_set(v___x_626_, 2, v_x_623_);
return v___x_626_;
}
else
{
lean_object* v_key_627_; lean_object* v_value_628_; lean_object* v_tail_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_644_; 
v_key_627_ = lean_ctor_get(v_x_623_, 0);
v_value_628_ = lean_ctor_get(v_x_623_, 1);
v_tail_629_ = lean_ctor_get(v_x_623_, 2);
v_isSharedCheck_644_ = !lean_is_exclusive(v_x_623_);
if (v_isSharedCheck_644_ == 0)
{
v___x_631_ = v_x_623_;
v_isShared_632_ = v_isSharedCheck_644_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_tail_629_);
lean_inc(v_value_628_);
lean_inc(v_key_627_);
lean_dec(v_x_623_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_644_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
uint8_t v___x_633_; 
v___x_633_ = lean_nat_dec_eq(v_key_627_, v_a_622_);
if (v___x_633_ == 0)
{
lean_object* v_tail_634_; lean_object* v___x_636_; 
v_tail_634_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(v_a_622_, v_tail_629_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 2, v_tail_634_);
v___x_636_ = v___x_631_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_key_627_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_value_628_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_tail_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v_val_640_; lean_object* v___x_642_; 
lean_dec(v_key_627_);
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v_value_628_);
v___x_639_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v___x_638_);
lean_dec_ref(v___x_638_);
v_val_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_val_640_);
lean_dec(v___x_639_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 1, v_val_640_);
lean_ctor_set(v___x_631_, 0, v_a_622_);
v___x_642_ = v___x_631_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_622_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_val_640_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v_tail_629_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_645_, lean_object* v_x_646_){
_start:
{
if (lean_obj_tag(v_x_646_) == 0)
{
return v_x_645_;
}
else
{
lean_object* v_key_647_; lean_object* v_value_648_; lean_object* v_tail_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_672_; 
v_key_647_ = lean_ctor_get(v_x_646_, 0);
v_value_648_ = lean_ctor_get(v_x_646_, 1);
v_tail_649_ = lean_ctor_get(v_x_646_, 2);
v_isSharedCheck_672_ = !lean_is_exclusive(v_x_646_);
if (v_isSharedCheck_672_ == 0)
{
v___x_651_ = v_x_646_;
v_isShared_652_ = v_isSharedCheck_672_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_tail_649_);
lean_inc(v_value_648_);
lean_inc(v_key_647_);
lean_dec(v_x_646_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_672_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; uint64_t v___x_654_; uint64_t v___x_655_; uint64_t v___x_656_; uint64_t v_fold_657_; uint64_t v___x_658_; uint64_t v___x_659_; uint64_t v___x_660_; size_t v___x_661_; size_t v___x_662_; size_t v___x_663_; size_t v___x_664_; size_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_653_ = lean_array_get_size(v_x_645_);
v___x_654_ = lean_uint64_of_nat(v_key_647_);
v___x_655_ = 32ULL;
v___x_656_ = lean_uint64_shift_right(v___x_654_, v___x_655_);
v_fold_657_ = lean_uint64_xor(v___x_654_, v___x_656_);
v___x_658_ = 16ULL;
v___x_659_ = lean_uint64_shift_right(v_fold_657_, v___x_658_);
v___x_660_ = lean_uint64_xor(v_fold_657_, v___x_659_);
v___x_661_ = lean_uint64_to_usize(v___x_660_);
v___x_662_ = lean_usize_of_nat(v___x_653_);
v___x_663_ = ((size_t)1ULL);
v___x_664_ = lean_usize_sub(v___x_662_, v___x_663_);
v___x_665_ = lean_usize_land(v___x_661_, v___x_664_);
v___x_666_ = lean_array_uget_borrowed(v_x_645_, v___x_665_);
lean_inc(v___x_666_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 2, v___x_666_);
v___x_668_ = v___x_651_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_key_647_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_value_648_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v___x_666_);
v___x_668_ = v_reuseFailAlloc_671_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; 
v___x_669_ = lean_array_uset(v_x_645_, v___x_665_, v___x_668_);
v_x_645_ = v___x_669_;
v_x_646_ = v_tail_649_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(lean_object* v_i_673_, lean_object* v_source_674_, lean_object* v_target_675_){
_start:
{
lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_676_ = lean_array_get_size(v_source_674_);
v___x_677_ = lean_nat_dec_lt(v_i_673_, v___x_676_);
if (v___x_677_ == 0)
{
lean_dec_ref(v_source_674_);
lean_dec(v_i_673_);
return v_target_675_;
}
else
{
lean_object* v_es_678_; lean_object* v___x_679_; lean_object* v_source_680_; lean_object* v_target_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v_es_678_ = lean_array_fget(v_source_674_, v_i_673_);
v___x_679_ = lean_box(0);
v_source_680_ = lean_array_fset(v_source_674_, v_i_673_, v___x_679_);
v_target_681_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(v_target_675_, v_es_678_);
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = lean_nat_add(v_i_673_, v___x_682_);
lean_dec(v_i_673_);
v_i_673_ = v___x_683_;
v_source_674_ = v_source_680_;
v_target_675_ = v_target_681_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(lean_object* v_data_685_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v_nbuckets_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_686_ = lean_array_get_size(v_data_685_);
v___x_687_ = lean_unsigned_to_nat(2u);
v_nbuckets_688_ = lean_nat_mul(v___x_686_, v___x_687_);
v___x_689_ = lean_unsigned_to_nat(0u);
v___x_690_ = lean_box(0);
v___x_691_ = lean_mk_array(v_nbuckets_688_, v___x_690_);
v___x_692_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(v___x_689_, v_data_685_, v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(lean_object* v_m_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_size_695_; lean_object* v_buckets_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_744_; 
v_size_695_ = lean_ctor_get(v_m_693_, 0);
v_buckets_696_ = lean_ctor_get(v_m_693_, 1);
v_isSharedCheck_744_ = !lean_is_exclusive(v_m_693_);
if (v_isSharedCheck_744_ == 0)
{
v___x_698_ = v_m_693_;
v_isShared_699_ = v_isSharedCheck_744_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_buckets_696_);
lean_inc(v_size_695_);
lean_dec(v_m_693_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_744_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; uint64_t v___x_701_; uint64_t v___x_702_; uint64_t v___x_703_; uint64_t v_fold_704_; uint64_t v___x_705_; uint64_t v___x_706_; uint64_t v___x_707_; size_t v___x_708_; size_t v___x_709_; size_t v___x_710_; size_t v___x_711_; size_t v___x_712_; lean_object* v_bkt_713_; uint8_t v___x_714_; 
v___x_700_ = lean_array_get_size(v_buckets_696_);
v___x_701_ = lean_uint64_of_nat(v_a_694_);
v___x_702_ = 32ULL;
v___x_703_ = lean_uint64_shift_right(v___x_701_, v___x_702_);
v_fold_704_ = lean_uint64_xor(v___x_701_, v___x_703_);
v___x_705_ = 16ULL;
v___x_706_ = lean_uint64_shift_right(v_fold_704_, v___x_705_);
v___x_707_ = lean_uint64_xor(v_fold_704_, v___x_706_);
v___x_708_ = lean_uint64_to_usize(v___x_707_);
v___x_709_ = lean_usize_of_nat(v___x_700_);
v___x_710_ = ((size_t)1ULL);
v___x_711_ = lean_usize_sub(v___x_709_, v___x_710_);
v___x_712_ = lean_usize_land(v___x_708_, v___x_711_);
v_bkt_713_ = lean_array_uget_borrowed(v_buckets_696_, v___x_712_);
v___x_714_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_694_, v_bkt_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v_size_x27_716_; lean_object* v___x_717_; lean_object* v_buckets_x27_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_715_ = lean_unsigned_to_nat(1u);
v_size_x27_716_ = lean_nat_add(v_size_695_, v___x_715_);
lean_dec(v_size_695_);
lean_inc(v_bkt_713_);
v___x_717_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_717_, 0, v_a_694_);
lean_ctor_set(v___x_717_, 1, v___x_715_);
lean_ctor_set(v___x_717_, 2, v_bkt_713_);
v_buckets_x27_718_ = lean_array_uset(v_buckets_696_, v___x_712_, v___x_717_);
v___x_719_ = lean_unsigned_to_nat(4u);
v___x_720_ = lean_nat_mul(v_size_x27_716_, v___x_719_);
v___x_721_ = lean_unsigned_to_nat(3u);
v___x_722_ = lean_nat_div(v___x_720_, v___x_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_array_get_size(v_buckets_x27_718_);
v___x_724_ = lean_nat_dec_le(v___x_722_, v___x_723_);
lean_dec(v___x_722_);
if (v___x_724_ == 0)
{
lean_object* v_val_725_; lean_object* v___x_727_; 
v_val_725_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_718_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v_val_725_);
lean_ctor_set(v___x_698_, 0, v_size_x27_716_);
v___x_727_ = v___x_698_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_size_x27_716_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_val_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
else
{
lean_object* v___x_730_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v_buckets_x27_718_);
lean_ctor_set(v___x_698_, 0, v_size_x27_716_);
v___x_730_ = v___x_698_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_size_x27_716_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_buckets_x27_718_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
else
{
lean_object* v___x_732_; lean_object* v_buckets_x27_733_; lean_object* v_bkt_x27_734_; lean_object* v___y_736_; uint8_t v___x_741_; 
lean_inc(v_bkt_713_);
v___x_732_ = lean_box(0);
v_buckets_x27_733_ = lean_array_uset(v_buckets_696_, v___x_712_, v___x_732_);
lean_inc(v_a_694_);
v_bkt_x27_734_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(v_a_694_, v_bkt_713_);
v___x_741_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_694_, v_bkt_x27_734_);
lean_dec(v_a_694_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = lean_unsigned_to_nat(1u);
v___x_743_ = lean_nat_sub(v_size_695_, v___x_742_);
lean_dec(v_size_695_);
v___y_736_ = v___x_743_;
goto v___jp_735_;
}
else
{
v___y_736_ = v_size_695_;
goto v___jp_735_;
}
v___jp_735_:
{
lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_737_ = lean_array_uset(v_buckets_x27_733_, v___x_712_, v_bkt_x27_734_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_737_);
lean_ctor_set(v___x_698_, 0, v___y_736_);
v___x_739_ = v___x_698_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___y_736_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(lean_object* v_coeff_745_, lean_object* v_e_746_, lean_object* v_a_747_){
_start:
{
lean_object* v___x_749_; lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_767_; 
v___x_749_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar___redArg(v_e_746_, v_a_747_);
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_767_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_767_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_767_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v_fst_754_; lean_object* v_snd_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_766_; 
v_fst_754_ = lean_ctor_get(v_a_750_, 0);
v_snd_755_ = lean_ctor_get(v_a_750_, 1);
v_isSharedCheck_766_ = !lean_is_exclusive(v_a_750_);
if (v_isSharedCheck_766_ == 0)
{
v___x_757_ = v_a_750_;
v_isShared_758_ = v_isSharedCheck_766_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_snd_755_);
lean_inc(v_fst_754_);
lean_dec(v_a_750_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_766_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_759_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(v_coeff_745_, v_fst_754_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_759_);
v___x_761_ = v___x_757_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_759_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_snd_755_);
v___x_761_ = v_reuseFailAlloc_765_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_763_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_761_);
v___x_763_ = v___x_752_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg___boxed(lean_object* v_coeff_768_, lean_object* v_e_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_768_, v_e_769_, v_a_770_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar(lean_object* v_coeff_773_, lean_object* v_e_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_773_, v_e_774_, v_a_775_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___boxed(lean_object* v_coeff_782_, lean_object* v_e_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar(v_coeff_782_, v_e_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
return v_res_790_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(lean_object* v_00_u03b2_791_, lean_object* v_a_792_, lean_object* v_x_793_){
_start:
{
uint8_t v___x_794_; 
v___x_794_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_792_, v_x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_795_, lean_object* v_a_796_, lean_object* v_x_797_){
_start:
{
uint8_t v_res_798_; lean_object* v_r_799_; 
v_res_798_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(v_00_u03b2_795_, v_a_796_, v_x_797_);
lean_dec(v_x_797_);
lean_dec(v_a_796_);
v_r_799_ = lean_box(v_res_798_);
return v_r_799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1(lean_object* v_00_u03b2_800_, lean_object* v_data_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_data_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_803_, lean_object* v_i_804_, lean_object* v_source_805_, lean_object* v_target_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(v_i_804_, v_source_805_, v_target_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_808_, lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_809_, v_x_810_);
return v___x_811_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_812_; double v___x_813_; 
v___x_812_ = lean_unsigned_to_nat(0u);
v___x_813_ = lean_float_of_nat(v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0(lean_object* v_cls_817_, lean_object* v_msg_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_ref_825_; lean_object* v___x_826_; lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_873_; 
v_ref_825_ = lean_ctor_get(v___y_822_, 5);
v___x_826_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_818_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_873_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_873_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_873_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v_traceState_832_; lean_object* v_env_833_; lean_object* v_nextMacroScope_834_; lean_object* v_ngen_835_; lean_object* v_auxDeclNGen_836_; lean_object* v_cache_837_; lean_object* v_messages_838_; lean_object* v_infoState_839_; lean_object* v_snapshotTasks_840_; lean_object* v_newDecls_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_872_; 
v___x_831_ = lean_st_ref_take(v___y_823_);
v_traceState_832_ = lean_ctor_get(v___x_831_, 4);
v_env_833_ = lean_ctor_get(v___x_831_, 0);
v_nextMacroScope_834_ = lean_ctor_get(v___x_831_, 1);
v_ngen_835_ = lean_ctor_get(v___x_831_, 2);
v_auxDeclNGen_836_ = lean_ctor_get(v___x_831_, 3);
v_cache_837_ = lean_ctor_get(v___x_831_, 5);
v_messages_838_ = lean_ctor_get(v___x_831_, 6);
v_infoState_839_ = lean_ctor_get(v___x_831_, 7);
v_snapshotTasks_840_ = lean_ctor_get(v___x_831_, 8);
v_newDecls_841_ = lean_ctor_get(v___x_831_, 9);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_872_ == 0)
{
v___x_843_ = v___x_831_;
v_isShared_844_ = v_isSharedCheck_872_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_newDecls_841_);
lean_inc(v_snapshotTasks_840_);
lean_inc(v_infoState_839_);
lean_inc(v_messages_838_);
lean_inc(v_cache_837_);
lean_inc(v_traceState_832_);
lean_inc(v_auxDeclNGen_836_);
lean_inc(v_ngen_835_);
lean_inc(v_nextMacroScope_834_);
lean_inc(v_env_833_);
lean_dec(v___x_831_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_872_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
uint64_t v_tid_845_; lean_object* v_traces_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_871_; 
v_tid_845_ = lean_ctor_get_uint64(v_traceState_832_, sizeof(void*)*1);
v_traces_846_ = lean_ctor_get(v_traceState_832_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v_traceState_832_);
if (v_isSharedCheck_871_ == 0)
{
v___x_848_ = v_traceState_832_;
v_isShared_849_ = v_isSharedCheck_871_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_traces_846_);
lean_dec(v_traceState_832_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_871_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; double v___x_851_; uint8_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_850_ = lean_box(0);
v___x_851_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0);
v___x_852_ = 0;
v___x_853_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1));
v___x_854_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_854_, 0, v_cls_817_);
lean_ctor_set(v___x_854_, 1, v___x_850_);
lean_ctor_set(v___x_854_, 2, v___x_853_);
lean_ctor_set_float(v___x_854_, sizeof(void*)*3, v___x_851_);
lean_ctor_set_float(v___x_854_, sizeof(void*)*3 + 8, v___x_851_);
lean_ctor_set_uint8(v___x_854_, sizeof(void*)*3 + 16, v___x_852_);
v___x_855_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__2));
v___x_856_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set(v___x_856_, 1, v_a_827_);
lean_ctor_set(v___x_856_, 2, v___x_855_);
lean_inc(v_ref_825_);
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v_ref_825_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = l_Lean_PersistentArray_push___redArg(v_traces_846_, v___x_857_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_858_);
v___x_860_ = v___x_848_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_858_);
lean_ctor_set_uint64(v_reuseFailAlloc_870_, sizeof(void*)*1, v_tid_845_);
v___x_860_ = v_reuseFailAlloc_870_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_862_; 
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 4, v___x_860_);
v___x_862_ = v___x_843_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_env_833_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_nextMacroScope_834_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v_ngen_835_);
lean_ctor_set(v_reuseFailAlloc_869_, 3, v_auxDeclNGen_836_);
lean_ctor_set(v_reuseFailAlloc_869_, 4, v___x_860_);
lean_ctor_set(v_reuseFailAlloc_869_, 5, v_cache_837_);
lean_ctor_set(v_reuseFailAlloc_869_, 6, v_messages_838_);
lean_ctor_set(v_reuseFailAlloc_869_, 7, v_infoState_839_);
lean_ctor_set(v_reuseFailAlloc_869_, 8, v_snapshotTasks_840_);
lean_ctor_set(v_reuseFailAlloc_869_, 9, v_newDecls_841_);
v___x_862_ = v_reuseFailAlloc_869_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_863_ = lean_st_ref_set(v___y_823_, v___x_862_);
v___x_864_ = lean_box(0);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v___y_819_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_865_);
v___x_867_ = v___x_829_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___boxed(lean_object* v_cls_874_, lean_object* v_msg_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0(v_cls_874_, v_msg_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
return v_res_882_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6(void){
_start:
{
lean_object* v_cls_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_cls_893_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_894_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_895_ = l_Lean_Name_append(v___x_894_, v_cls_893_);
return v___x_895_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__8(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__7));
v___x_898_ = l_Lean_stringToMessageData(v___x_897_);
return v___x_898_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__9));
v___x_901_ = l_Lean_stringToMessageData(v___x_900_);
return v___x_901_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__12(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__11));
v___x_904_ = l_Lean_stringToMessageData(v___x_903_);
return v___x_904_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__14(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__13));
v___x_907_ = l_Lean_stringToMessageData(v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go(lean_object* v_op_908_, lean_object* v_coeff_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
if (lean_obj_tag(v_a_910_) == 5)
{
lean_object* v_fn_917_; 
v_fn_917_ = lean_ctor_get(v_a_910_, 0);
if (lean_obj_tag(v_fn_917_) == 5)
{
lean_object* v_arg_918_; lean_object* v_fn_919_; lean_object* v_arg_920_; uint8_t v___x_921_; 
v_arg_918_ = lean_ctor_get(v_a_910_, 1);
v_fn_919_ = lean_ctor_get(v_fn_917_, 0);
v_arg_920_ = lean_ctor_get(v_fn_917_, 1);
lean_inc_ref(v_fn_919_);
v___x_921_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind___redArg(v_fn_919_);
if (v___x_921_ == 0)
{
lean_object* v_options_922_; uint8_t v_hasTrace_923_; 
v_options_922_ = lean_ctor_get(v_a_914_, 2);
v_hasTrace_923_ = lean_ctor_get_uint8(v_options_922_, sizeof(void*)*1);
if (v_hasTrace_923_ == 0)
{
lean_object* v___x_924_; 
lean_dec_ref(v_op_908_);
v___x_924_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_909_, v_a_910_, v_a_911_);
return v___x_924_;
}
else
{
lean_object* v_inheritedTraceOptions_925_; lean_object* v_cls_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v_inheritedTraceOptions_925_ = lean_ctor_get(v_a_914_, 13);
v_cls_926_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_927_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_928_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_925_, v_options_922_, v___x_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; 
lean_dec_ref(v_op_908_);
v___x_929_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_909_, v_a_910_, v_a_911_);
return v___x_929_;
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_930_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__8, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__8_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__8);
lean_inc_ref(v_fn_919_);
v___x_931_ = l_Lean_MessageData_ofExpr(v_fn_919_);
v___x_932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10);
v___x_934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_932_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
lean_inc_ref(v_arg_920_);
v___x_935_ = l_Lean_MessageData_ofExpr(v_arg_920_);
v___x_936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_934_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___x_933_);
lean_inc_ref(v_arg_918_);
v___x_938_ = l_Lean_MessageData_ofExpr(v_arg_918_);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__12, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__12_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__12);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_op_908_);
v___x_943_ = l_Lean_MessageData_ofExpr(v___x_942_);
v___x_944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_941_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__14, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__14_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__14);
v___x_946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0(v_cls_926_, v___x_946_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v_snd_949_; lean_object* v___x_950_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_948_);
lean_dec_ref(v___x_947_);
v_snd_949_ = lean_ctor_get(v_a_948_, 1);
lean_inc(v_snd_949_);
lean_dec(v_a_948_);
v___x_950_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_909_, v_a_910_, v_snd_949_);
return v___x_950_;
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
lean_dec_ref(v_a_910_);
lean_dec_ref(v_coeff_909_);
v_a_951_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_947_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_947_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
}
else
{
lean_object* v___x_959_; 
lean_inc_ref(v_arg_920_);
lean_inc_ref(v_arg_918_);
lean_dec_ref(v_a_910_);
lean_inc_ref(v_op_908_);
v___x_959_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go(v_op_908_, v_coeff_909_, v_arg_920_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v_fst_961_; lean_object* v_snd_962_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref(v___x_959_);
v_fst_961_ = lean_ctor_get(v_a_960_, 0);
lean_inc(v_fst_961_);
v_snd_962_ = lean_ctor_get(v_a_960_, 1);
lean_inc(v_snd_962_);
lean_dec(v_a_960_);
v_coeff_909_ = v_fst_961_;
v_a_910_ = v_arg_918_;
v_a_911_ = v_snd_962_;
goto _start;
}
else
{
lean_dec_ref(v_arg_918_);
lean_dec_ref(v_op_908_);
return v___x_959_;
}
}
}
else
{
lean_object* v___x_964_; 
lean_dec_ref(v_op_908_);
v___x_964_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_909_, v_a_910_, v_a_911_);
return v___x_964_;
}
}
else
{
lean_object* v___x_965_; 
lean_dec_ref(v_op_908_);
v___x_965_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_909_, v_a_910_, v_a_911_);
return v___x_965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___boxed(lean_object* v_op_966_, lean_object* v_coeff_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go(v_op_966_, v_coeff_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
return v_res_975_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_976_ = lean_box(0);
v___x_977_ = lean_unsigned_to_nat(16u);
v___x_978_ = lean_mk_array(v___x_977_, v___x_976_);
return v___x_978_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_980_ = lean_unsigned_to_nat(0u);
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v___x_979_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(lean_object* v_op_982_, lean_object* v_e_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_991_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go(v_op_982_, v___x_990_, v_e_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___boxed(lean_object* v_op_992_, lean_object* v_e_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(v_op_992_, v_e_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0(lean_object* v_commonCnt_1001_, lean_object* v_a_1002_, lean_object* v_x_1003_){
_start:
{
if (lean_obj_tag(v_x_1003_) == 0)
{
lean_dec(v_a_1002_);
return v_x_1003_;
}
else
{
lean_object* v_key_1004_; lean_object* v_value_1005_; lean_object* v_tail_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1019_; 
v_key_1004_ = lean_ctor_get(v_x_1003_, 0);
v_value_1005_ = lean_ctor_get(v_x_1003_, 1);
v_tail_1006_ = lean_ctor_get(v_x_1003_, 2);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_x_1003_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1008_ = v_x_1003_;
v_isShared_1009_ = v_isSharedCheck_1019_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_tail_1006_);
lean_inc(v_value_1005_);
lean_inc(v_key_1004_);
lean_dec(v_x_1003_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1019_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
uint8_t v___x_1010_; 
v___x_1010_ = lean_nat_dec_eq(v_key_1004_, v_a_1002_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1011_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1001_, v_a_1002_, v_tail_1006_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 2, v___x_1011_);
v___x_1013_ = v___x_1008_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_key_1004_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_value_1005_);
lean_ctor_set(v_reuseFailAlloc_1014_, 2, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1017_; 
lean_dec(v_key_1004_);
v___x_1015_ = lean_nat_sub(v_value_1005_, v_commonCnt_1001_);
lean_dec(v_value_1005_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v___x_1015_);
lean_ctor_set(v___x_1008_, 0, v_a_1002_);
v___x_1017_ = v___x_1008_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1002_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1018_, 2, v_tail_1006_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0___boxed(lean_object* v_commonCnt_1020_, lean_object* v_a_1021_, lean_object* v_x_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1020_, v_a_1021_, v_x_1022_);
lean_dec(v_commonCnt_1020_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0(lean_object* v_commonCnt_1024_, lean_object* v_m_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v_size_1027_; lean_object* v_buckets_1028_; lean_object* v___x_1029_; uint64_t v___x_1030_; uint64_t v___x_1031_; uint64_t v___x_1032_; uint64_t v_fold_1033_; uint64_t v___x_1034_; uint64_t v___x_1035_; uint64_t v___x_1036_; size_t v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; lean_object* v_bucket_1042_; uint8_t v___x_1043_; 
v_size_1027_ = lean_ctor_get(v_m_1025_, 0);
v_buckets_1028_ = lean_ctor_get(v_m_1025_, 1);
v___x_1029_ = lean_array_get_size(v_buckets_1028_);
v___x_1030_ = lean_uint64_of_nat(v_a_1026_);
v___x_1031_ = 32ULL;
v___x_1032_ = lean_uint64_shift_right(v___x_1030_, v___x_1031_);
v_fold_1033_ = lean_uint64_xor(v___x_1030_, v___x_1032_);
v___x_1034_ = 16ULL;
v___x_1035_ = lean_uint64_shift_right(v_fold_1033_, v___x_1034_);
v___x_1036_ = lean_uint64_xor(v_fold_1033_, v___x_1035_);
v___x_1037_ = lean_uint64_to_usize(v___x_1036_);
v___x_1038_ = lean_usize_of_nat(v___x_1029_);
v___x_1039_ = ((size_t)1ULL);
v___x_1040_ = lean_usize_sub(v___x_1038_, v___x_1039_);
v___x_1041_ = lean_usize_land(v___x_1037_, v___x_1040_);
v_bucket_1042_ = lean_array_uget_borrowed(v_buckets_1028_, v___x_1041_);
v___x_1043_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1026_, v_bucket_1042_);
if (v___x_1043_ == 0)
{
lean_dec(v_a_1026_);
return v_m_1025_;
}
else
{
lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1054_; 
lean_inc(v_bucket_1042_);
lean_inc_ref(v_buckets_1028_);
lean_inc(v_size_1027_);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_m_1025_);
if (v_isSharedCheck_1054_ == 0)
{
lean_object* v_unused_1055_; lean_object* v_unused_1056_; 
v_unused_1055_ = lean_ctor_get(v_m_1025_, 1);
lean_dec(v_unused_1055_);
v_unused_1056_ = lean_ctor_get(v_m_1025_, 0);
lean_dec(v_unused_1056_);
v___x_1045_ = v_m_1025_;
v_isShared_1046_ = v_isSharedCheck_1054_;
goto v_resetjp_1044_;
}
else
{
lean_dec(v_m_1025_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1054_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v_buckets_1048_; lean_object* v_bucket_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1047_ = lean_box(0);
v_buckets_1048_ = lean_array_uset(v_buckets_1028_, v___x_1041_, v___x_1047_);
v_bucket_1049_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1024_, v_a_1026_, v_bucket_1042_);
v___x_1050_ = lean_array_uset(v_buckets_1048_, v___x_1041_, v_bucket_1049_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 1, v___x_1050_);
v___x_1052_ = v___x_1045_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_size_1027_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0___boxed(lean_object* v_commonCnt_1057_, lean_object* v_m_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0(v_commonCnt_1057_, v_m_1058_, v_a_1059_);
lean_dec(v_commonCnt_1057_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__1_spec__2(lean_object* v_x_1061_, lean_object* v_x_1062_){
_start:
{
if (lean_obj_tag(v_x_1062_) == 0)
{
return v_x_1061_;
}
else
{
lean_object* v_key_1063_; lean_object* v_value_1064_; lean_object* v_tail_1065_; lean_object* v___x_1066_; 
v_key_1063_ = lean_ctor_get(v_x_1062_, 0);
lean_inc(v_key_1063_);
v_value_1064_ = lean_ctor_get(v_x_1062_, 1);
lean_inc(v_value_1064_);
v_tail_1065_ = lean_ctor_get(v_x_1062_, 2);
lean_inc(v_tail_1065_);
lean_dec_ref(v_x_1062_);
v___x_1066_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0(v_value_1064_, v_x_1061_, v_key_1063_);
lean_dec(v_value_1064_);
v_x_1061_ = v___x_1066_;
v_x_1062_ = v_tail_1065_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__1(lean_object* v_x_1068_, lean_object* v_x_1069_){
_start:
{
if (lean_obj_tag(v_x_1069_) == 0)
{
return v_x_1068_;
}
else
{
lean_object* v_key_1070_; lean_object* v_value_1071_; lean_object* v_tail_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_key_1070_ = lean_ctor_get(v_x_1069_, 0);
lean_inc(v_key_1070_);
v_value_1071_ = lean_ctor_get(v_x_1069_, 1);
lean_inc(v_value_1071_);
v_tail_1072_ = lean_ctor_get(v_x_1069_, 2);
lean_inc(v_tail_1072_);
lean_dec_ref(v_x_1069_);
v___x_1073_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0(v_value_1071_, v_x_1068_, v_key_1070_);
lean_dec(v_value_1071_);
v___x_1074_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__1_spec__2(v___x_1073_, v_tail_1072_);
return v___x_1074_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(lean_object* v_as_1075_, size_t v_i_1076_, size_t v_stop_1077_, lean_object* v_b_1078_){
_start:
{
uint8_t v___x_1079_; 
v___x_1079_ = lean_usize_dec_eq(v_i_1076_, v_stop_1077_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1081_; size_t v___x_1082_; size_t v___x_1083_; 
v___x_1080_ = lean_array_uget_borrowed(v_as_1075_, v_i_1076_);
lean_inc(v___x_1080_);
v___x_1081_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__1(v_b_1078_, v___x_1080_);
v___x_1082_ = ((size_t)1ULL);
v___x_1083_ = lean_usize_add(v_i_1076_, v___x_1082_);
v_i_1076_ = v___x_1083_;
v_b_1078_ = v___x_1081_;
goto _start;
}
else
{
return v_b_1078_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2___boxed(lean_object* v_as_1085_, lean_object* v_i_1086_, lean_object* v_stop_1087_, lean_object* v_b_1088_){
_start:
{
size_t v_i_boxed_1089_; size_t v_stop_boxed_1090_; lean_object* v_res_1091_; 
v_i_boxed_1089_ = lean_unbox_usize(v_i_1086_);
lean_dec(v_i_1086_);
v_stop_boxed_1090_ = lean_unbox_usize(v_stop_1087_);
lean_dec(v_stop_1087_);
v_res_1091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(v_as_1085_, v_i_boxed_1089_, v_stop_boxed_1090_, v_b_1088_);
lean_dec_ref(v_as_1085_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(lean_object* v_a_1092_, lean_object* v_x_1093_){
_start:
{
if (lean_obj_tag(v_x_1093_) == 0)
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_box(0);
return v___x_1094_;
}
else
{
lean_object* v_key_1095_; lean_object* v_value_1096_; lean_object* v_tail_1097_; uint8_t v___x_1098_; 
v_key_1095_ = lean_ctor_get(v_x_1093_, 0);
v_value_1096_ = lean_ctor_get(v_x_1093_, 1);
v_tail_1097_ = lean_ctor_get(v_x_1093_, 2);
v___x_1098_ = lean_nat_dec_eq(v_key_1095_, v_a_1092_);
if (v___x_1098_ == 0)
{
v_x_1093_ = v_tail_1097_;
goto _start;
}
else
{
lean_object* v___x_1100_; 
lean_inc(v_value_1096_);
v___x_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1100_, 0, v_value_1096_);
return v___x_1100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg___boxed(lean_object* v_a_1101_, lean_object* v_x_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1101_, v_x_1102_);
lean_dec(v_x_1102_);
lean_dec(v_a_1101_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg(lean_object* v_m_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v_buckets_1106_; lean_object* v___x_1107_; uint64_t v___x_1108_; uint64_t v___x_1109_; uint64_t v___x_1110_; uint64_t v_fold_1111_; uint64_t v___x_1112_; uint64_t v___x_1113_; uint64_t v___x_1114_; size_t v___x_1115_; size_t v___x_1116_; size_t v___x_1117_; size_t v___x_1118_; size_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v_buckets_1106_ = lean_ctor_get(v_m_1104_, 1);
v___x_1107_ = lean_array_get_size(v_buckets_1106_);
v___x_1108_ = lean_uint64_of_nat(v_a_1105_);
v___x_1109_ = 32ULL;
v___x_1110_ = lean_uint64_shift_right(v___x_1108_, v___x_1109_);
v_fold_1111_ = lean_uint64_xor(v___x_1108_, v___x_1110_);
v___x_1112_ = 16ULL;
v___x_1113_ = lean_uint64_shift_right(v_fold_1111_, v___x_1112_);
v___x_1114_ = lean_uint64_xor(v_fold_1111_, v___x_1113_);
v___x_1115_ = lean_uint64_to_usize(v___x_1114_);
v___x_1116_ = lean_usize_of_nat(v___x_1107_);
v___x_1117_ = ((size_t)1ULL);
v___x_1118_ = lean_usize_sub(v___x_1116_, v___x_1117_);
v___x_1119_ = lean_usize_land(v___x_1115_, v___x_1118_);
v___x_1120_ = lean_array_uget_borrowed(v_buckets_1106_, v___x_1119_);
v___x_1121_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1105_, v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg___boxed(lean_object* v_m_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1122_, v_a_1123_);
lean_dec(v_a_1123_);
lean_dec_ref(v_m_1122_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(lean_object* v_a_1125_, lean_object* v_b_1126_, lean_object* v_x_1127_){
_start:
{
if (lean_obj_tag(v_x_1127_) == 0)
{
lean_dec(v_b_1126_);
lean_dec(v_a_1125_);
return v_x_1127_;
}
else
{
lean_object* v_key_1128_; lean_object* v_value_1129_; lean_object* v_tail_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1142_; 
v_key_1128_ = lean_ctor_get(v_x_1127_, 0);
v_value_1129_ = lean_ctor_get(v_x_1127_, 1);
v_tail_1130_ = lean_ctor_get(v_x_1127_, 2);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_x_1127_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1132_ = v_x_1127_;
v_isShared_1133_ = v_isSharedCheck_1142_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_tail_1130_);
lean_inc(v_value_1129_);
lean_inc(v_key_1128_);
lean_dec(v_x_1127_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1142_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
uint8_t v___x_1134_; 
v___x_1134_ = lean_nat_dec_eq(v_key_1128_, v_a_1125_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1135_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1125_, v_b_1126_, v_tail_1130_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 2, v___x_1135_);
v___x_1137_ = v___x_1132_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_key_1128_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_value_1129_);
lean_ctor_set(v_reuseFailAlloc_1138_, 2, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
else
{
lean_object* v___x_1140_; 
lean_dec(v_value_1129_);
lean_dec(v_key_1128_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 1, v_b_1126_);
lean_ctor_set(v___x_1132_, 0, v_a_1125_);
v___x_1140_ = v___x_1132_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1125_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_b_1126_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_tail_1130_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3___redArg(lean_object* v_m_1143_, lean_object* v_a_1144_, lean_object* v_b_1145_){
_start:
{
lean_object* v_size_1146_; lean_object* v_buckets_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1190_; 
v_size_1146_ = lean_ctor_get(v_m_1143_, 0);
v_buckets_1147_ = lean_ctor_get(v_m_1143_, 1);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_m_1143_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1149_ = v_m_1143_;
v_isShared_1150_ = v_isSharedCheck_1190_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_buckets_1147_);
lean_inc(v_size_1146_);
lean_dec(v_m_1143_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1190_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; uint64_t v___x_1152_; uint64_t v___x_1153_; uint64_t v___x_1154_; uint64_t v_fold_1155_; uint64_t v___x_1156_; uint64_t v___x_1157_; uint64_t v___x_1158_; size_t v___x_1159_; size_t v___x_1160_; size_t v___x_1161_; size_t v___x_1162_; size_t v___x_1163_; lean_object* v_bkt_1164_; uint8_t v___x_1165_; 
v___x_1151_ = lean_array_get_size(v_buckets_1147_);
v___x_1152_ = lean_uint64_of_nat(v_a_1144_);
v___x_1153_ = 32ULL;
v___x_1154_ = lean_uint64_shift_right(v___x_1152_, v___x_1153_);
v_fold_1155_ = lean_uint64_xor(v___x_1152_, v___x_1154_);
v___x_1156_ = 16ULL;
v___x_1157_ = lean_uint64_shift_right(v_fold_1155_, v___x_1156_);
v___x_1158_ = lean_uint64_xor(v_fold_1155_, v___x_1157_);
v___x_1159_ = lean_uint64_to_usize(v___x_1158_);
v___x_1160_ = lean_usize_of_nat(v___x_1151_);
v___x_1161_ = ((size_t)1ULL);
v___x_1162_ = lean_usize_sub(v___x_1160_, v___x_1161_);
v___x_1163_ = lean_usize_land(v___x_1159_, v___x_1162_);
v_bkt_1164_ = lean_array_uget_borrowed(v_buckets_1147_, v___x_1163_);
v___x_1165_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1144_, v_bkt_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v_size_x27_1167_; lean_object* v___x_1168_; lean_object* v_buckets_x27_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1166_ = lean_unsigned_to_nat(1u);
v_size_x27_1167_ = lean_nat_add(v_size_1146_, v___x_1166_);
lean_dec(v_size_1146_);
lean_inc(v_bkt_1164_);
v___x_1168_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1168_, 0, v_a_1144_);
lean_ctor_set(v___x_1168_, 1, v_b_1145_);
lean_ctor_set(v___x_1168_, 2, v_bkt_1164_);
v_buckets_x27_1169_ = lean_array_uset(v_buckets_1147_, v___x_1163_, v___x_1168_);
v___x_1170_ = lean_unsigned_to_nat(4u);
v___x_1171_ = lean_nat_mul(v_size_x27_1167_, v___x_1170_);
v___x_1172_ = lean_unsigned_to_nat(3u);
v___x_1173_ = lean_nat_div(v___x_1171_, v___x_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_array_get_size(v_buckets_x27_1169_);
v___x_1175_ = lean_nat_dec_le(v___x_1173_, v___x_1174_);
lean_dec(v___x_1173_);
if (v___x_1175_ == 0)
{
lean_object* v_val_1176_; lean_object* v___x_1178_; 
v_val_1176_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_1169_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 1, v_val_1176_);
lean_ctor_set(v___x_1149_, 0, v_size_x27_1167_);
v___x_1178_ = v___x_1149_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_size_x27_1167_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_val_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
else
{
lean_object* v___x_1181_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 1, v_buckets_x27_1169_);
lean_ctor_set(v___x_1149_, 0, v_size_x27_1167_);
v___x_1181_ = v___x_1149_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_size_x27_1167_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_buckets_x27_1169_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
else
{
lean_object* v___x_1183_; lean_object* v_buckets_x27_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1188_; 
lean_inc(v_bkt_1164_);
v___x_1183_ = lean_box(0);
v_buckets_x27_1184_ = lean_array_uset(v_buckets_1147_, v___x_1163_, v___x_1183_);
v___x_1185_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1144_, v_b_1145_, v_bkt_1164_);
v___x_1186_ = lean_array_uset(v_buckets_x27_1184_, v___x_1163_, v___x_1185_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 1, v___x_1186_);
v___x_1188_ = v___x_1149_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_size_1146_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v___x_1186_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__5(lean_object* v_snd_1191_, lean_object* v_x_1192_, lean_object* v_x_1193_){
_start:
{
if (lean_obj_tag(v_x_1193_) == 0)
{
return v_x_1192_;
}
else
{
lean_object* v_key_1194_; lean_object* v_value_1195_; lean_object* v_tail_1196_; lean_object* v___y_1198_; lean_object* v___x_1201_; 
v_key_1194_ = lean_ctor_get(v_x_1193_, 0);
lean_inc(v_key_1194_);
v_value_1195_ = lean_ctor_get(v_x_1193_, 1);
lean_inc(v_value_1195_);
v_tail_1196_ = lean_ctor_get(v_x_1193_, 2);
lean_inc(v_tail_1196_);
lean_dec_ref(v_x_1193_);
v___x_1201_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg(v_snd_1191_, v_key_1194_);
if (lean_obj_tag(v___x_1201_) == 1)
{
lean_object* v_val_1202_; uint8_t v___x_1203_; 
v_val_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_val_1202_);
lean_dec_ref(v___x_1201_);
v___x_1203_ = lean_nat_dec_le(v_value_1195_, v_val_1202_);
if (v___x_1203_ == 0)
{
lean_dec(v_value_1195_);
v___y_1198_ = v_val_1202_;
goto v___jp_1197_;
}
else
{
lean_dec(v_val_1202_);
v___y_1198_ = v_value_1195_;
goto v___jp_1197_;
}
}
else
{
lean_dec(v___x_1201_);
lean_dec(v_value_1195_);
lean_dec(v_key_1194_);
v_x_1193_ = v_tail_1196_;
goto _start;
}
v___jp_1197_:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3___redArg(v_x_1192_, v_key_1194_, v___y_1198_);
v_x_1192_ = v___x_1199_;
v_x_1193_ = v_tail_1196_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__5___boxed(lean_object* v_snd_1205_, lean_object* v_x_1206_, lean_object* v_x_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__5(v_snd_1205_, v_x_1206_, v_x_1207_);
lean_dec_ref(v_snd_1205_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6(lean_object* v_snd_1209_, lean_object* v_as_1210_, size_t v_i_1211_, size_t v_stop_1212_, lean_object* v_b_1213_){
_start:
{
uint8_t v___x_1214_; 
v___x_1214_ = lean_usize_dec_eq(v_i_1211_, v_stop_1212_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; lean_object* v___x_1216_; size_t v___x_1217_; size_t v___x_1218_; 
v___x_1215_ = lean_array_uget_borrowed(v_as_1210_, v_i_1211_);
lean_inc(v___x_1215_);
v___x_1216_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__5(v_snd_1209_, v_b_1213_, v___x_1215_);
v___x_1217_ = ((size_t)1ULL);
v___x_1218_ = lean_usize_add(v_i_1211_, v___x_1217_);
v_i_1211_ = v___x_1218_;
v_b_1213_ = v___x_1216_;
goto _start;
}
else
{
return v_b_1213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6___boxed(lean_object* v_snd_1220_, lean_object* v_as_1221_, lean_object* v_i_1222_, lean_object* v_stop_1223_, lean_object* v_b_1224_){
_start:
{
size_t v_i_boxed_1225_; size_t v_stop_boxed_1226_; lean_object* v_res_1227_; 
v_i_boxed_1225_ = lean_unbox_usize(v_i_1222_);
lean_dec(v_i_1222_);
v_stop_boxed_1226_ = lean_unbox_usize(v_stop_1223_);
lean_dec(v_stop_1223_);
v_res_1227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6(v_snd_1220_, v_as_1221_, v_i_boxed_1225_, v_stop_boxed_1226_, v_b_1224_);
lean_dec_ref(v_as_1221_);
lean_dec_ref(v_snd_1220_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(lean_object* v_x_1228_, lean_object* v_y_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v___y_1233_; lean_object* v_fst_1234_; lean_object* v_snd_1235_; lean_object* v_size_1239_; lean_object* v_buckets_1240_; lean_object* v_size_1241_; lean_object* v_buckets_1242_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v_buckets_1251_; lean_object* v___y_1252_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v_buckets_1267_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v_fst_1284_; lean_object* v_buckets_1285_; lean_object* v_snd_1286_; uint8_t v___x_1299_; 
v_size_1239_ = lean_ctor_get(v_y_1229_, 0);
lean_inc(v_size_1239_);
v_buckets_1240_ = lean_ctor_get(v_y_1229_, 1);
v_size_1241_ = lean_ctor_get(v_x_1228_, 0);
lean_inc(v_size_1241_);
v_buckets_1242_ = lean_ctor_get(v_x_1228_, 1);
v___x_1299_ = lean_nat_dec_lt(v_size_1239_, v_size_1241_);
if (v___x_1299_ == 0)
{
lean_inc_ref(v_buckets_1242_);
v_fst_1284_ = v_x_1228_;
v_buckets_1285_ = v_buckets_1242_;
v_snd_1286_ = v_y_1229_;
goto v___jp_1283_;
}
else
{
lean_inc_ref(v_buckets_1240_);
v_fst_1284_ = v_y_1229_;
v_buckets_1285_ = v_buckets_1240_;
v_snd_1286_ = v_x_1228_;
goto v___jp_1283_;
}
v___jp_1232_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1236_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1236_, 0, v___y_1233_);
lean_ctor_set(v___x_1236_, 1, v_fst_1234_);
lean_ctor_set(v___x_1236_, 2, v_snd_1235_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
lean_ctor_set(v___x_1237_, 1, v_a_1230_);
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
return v___x_1238_;
}
v___jp_1243_:
{
uint8_t v___x_1247_; 
v___x_1247_ = lean_nat_dec_lt(v_size_1239_, v_size_1241_);
lean_dec(v_size_1241_);
lean_dec(v_size_1239_);
if (v___x_1247_ == 0)
{
v___y_1233_ = v___y_1245_;
v_fst_1234_ = v___y_1244_;
v_snd_1235_ = v___y_1246_;
goto v___jp_1232_;
}
else
{
v___y_1233_ = v___y_1245_;
v_fst_1234_ = v___y_1246_;
v_snd_1235_ = v___y_1244_;
goto v___jp_1232_;
}
}
v___jp_1248_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1253_ = lean_unsigned_to_nat(0u);
v___x_1254_ = lean_array_get_size(v_buckets_1251_);
v___x_1255_ = lean_nat_dec_lt(v___x_1253_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_dec_ref(v_buckets_1251_);
v___y_1244_ = v___y_1252_;
v___y_1245_ = v___y_1250_;
v___y_1246_ = v___y_1249_;
goto v___jp_1243_;
}
else
{
uint8_t v___x_1256_; 
v___x_1256_ = lean_nat_dec_le(v___x_1254_, v___x_1254_);
if (v___x_1256_ == 0)
{
if (v___x_1255_ == 0)
{
lean_dec_ref(v_buckets_1251_);
v___y_1244_ = v___y_1252_;
v___y_1245_ = v___y_1250_;
v___y_1246_ = v___y_1249_;
goto v___jp_1243_;
}
else
{
size_t v___x_1257_; size_t v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = ((size_t)0ULL);
v___x_1258_ = lean_usize_of_nat(v___x_1254_);
v___x_1259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1251_, v___x_1257_, v___x_1258_, v___y_1249_);
lean_dec_ref(v_buckets_1251_);
v___y_1244_ = v___y_1252_;
v___y_1245_ = v___y_1250_;
v___y_1246_ = v___x_1259_;
goto v___jp_1243_;
}
}
else
{
size_t v___x_1260_; size_t v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = ((size_t)0ULL);
v___x_1261_ = lean_usize_of_nat(v___x_1254_);
v___x_1262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1251_, v___x_1260_, v___x_1261_, v___y_1249_);
lean_dec_ref(v_buckets_1251_);
v___y_1244_ = v___y_1252_;
v___y_1245_ = v___y_1250_;
v___y_1246_ = v___x_1262_;
goto v___jp_1243_;
}
}
}
v___jp_1263_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = lean_array_get_size(v_buckets_1267_);
v___x_1270_ = lean_nat_dec_lt(v___x_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
v___y_1249_ = v___y_1264_;
v___y_1250_ = v___y_1266_;
v_buckets_1251_ = v_buckets_1267_;
v___y_1252_ = v___y_1265_;
goto v___jp_1248_;
}
else
{
uint8_t v___x_1271_; 
v___x_1271_ = lean_nat_dec_le(v___x_1269_, v___x_1269_);
if (v___x_1271_ == 0)
{
if (v___x_1270_ == 0)
{
v___y_1249_ = v___y_1264_;
v___y_1250_ = v___y_1266_;
v_buckets_1251_ = v_buckets_1267_;
v___y_1252_ = v___y_1265_;
goto v___jp_1248_;
}
else
{
size_t v___x_1272_; size_t v___x_1273_; lean_object* v___x_1274_; 
v___x_1272_ = ((size_t)0ULL);
v___x_1273_ = lean_usize_of_nat(v___x_1269_);
v___x_1274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1267_, v___x_1272_, v___x_1273_, v___y_1265_);
v___y_1249_ = v___y_1264_;
v___y_1250_ = v___y_1266_;
v_buckets_1251_ = v_buckets_1267_;
v___y_1252_ = v___x_1274_;
goto v___jp_1248_;
}
}
else
{
size_t v___x_1275_; size_t v___x_1276_; lean_object* v___x_1277_; 
v___x_1275_ = ((size_t)0ULL);
v___x_1276_ = lean_usize_of_nat(v___x_1269_);
v___x_1277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1267_, v___x_1275_, v___x_1276_, v___y_1265_);
v___y_1249_ = v___y_1264_;
v___y_1250_ = v___y_1266_;
v_buckets_1251_ = v_buckets_1267_;
v___y_1252_ = v___x_1277_;
goto v___jp_1248_;
}
}
}
v___jp_1278_:
{
lean_object* v_buckets_1282_; 
v_buckets_1282_ = lean_ctor_get(v___y_1281_, 1);
lean_inc_ref(v_buckets_1282_);
v___y_1264_ = v___y_1279_;
v___y_1265_ = v___y_1280_;
v___y_1266_ = v___y_1281_;
v_buckets_1267_ = v_buckets_1282_;
goto v___jp_1263_;
}
v___jp_1283_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1287_ = lean_unsigned_to_nat(0u);
v___x_1288_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1289_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1290_ = lean_array_get_size(v_buckets_1285_);
v___x_1291_ = lean_nat_dec_lt(v___x_1287_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_dec_ref(v_buckets_1285_);
v___y_1264_ = v_snd_1286_;
v___y_1265_ = v_fst_1284_;
v___y_1266_ = v___x_1289_;
v_buckets_1267_ = v___x_1288_;
goto v___jp_1263_;
}
else
{
uint8_t v___x_1292_; 
v___x_1292_ = lean_nat_dec_le(v___x_1290_, v___x_1290_);
if (v___x_1292_ == 0)
{
if (v___x_1291_ == 0)
{
lean_dec_ref(v_buckets_1285_);
v___y_1264_ = v_snd_1286_;
v___y_1265_ = v_fst_1284_;
v___y_1266_ = v___x_1289_;
v_buckets_1267_ = v___x_1288_;
goto v___jp_1263_;
}
else
{
size_t v___x_1293_; size_t v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = ((size_t)0ULL);
v___x_1294_ = lean_usize_of_nat(v___x_1290_);
v___x_1295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6(v_snd_1286_, v_buckets_1285_, v___x_1293_, v___x_1294_, v___x_1289_);
lean_dec_ref(v_buckets_1285_);
v___y_1279_ = v_snd_1286_;
v___y_1280_ = v_fst_1284_;
v___y_1281_ = v___x_1295_;
goto v___jp_1278_;
}
}
else
{
size_t v___x_1296_; size_t v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = ((size_t)0ULL);
v___x_1297_ = lean_usize_of_nat(v___x_1290_);
v___x_1298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6(v_snd_1286_, v_buckets_1285_, v___x_1296_, v___x_1297_, v___x_1289_);
lean_dec_ref(v_buckets_1285_);
v___y_1279_ = v_snd_1286_;
v___y_1280_ = v_fst_1284_;
v___y_1281_ = v___x_1298_;
goto v___jp_1278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg___boxed(lean_object* v_x_1300_, lean_object* v_y_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(v_x_1300_, v_y_1301_, v_a_1302_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute(lean_object* v_x_1305_, lean_object* v_y_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(v_x_1305_, v_y_1306_, v_a_1307_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___boxed(lean_object* v_x_1314_, lean_object* v_y_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute(v_x_1314_, v_y_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3(lean_object* v_00_u03b2_1323_, lean_object* v_m_1324_, lean_object* v_a_1325_, lean_object* v_b_1326_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3___redArg(v_m_1324_, v_a_1325_, v_b_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4(lean_object* v_00_u03b2_1328_, lean_object* v_m_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1329_, v_a_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___boxed(lean_object* v_00_u03b2_1332_, lean_object* v_m_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4(v_00_u03b2_1332_, v_m_1333_, v_a_1334_);
lean_dec(v_a_1334_);
lean_dec_ref(v_m_1333_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5(lean_object* v_00_u03b2_1336_, lean_object* v_a_1337_, lean_object* v_b_1338_, lean_object* v_x_1339_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1337_, v_b_1338_, v_x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7(lean_object* v_00_u03b2_1341_, lean_object* v_a_1342_, lean_object* v_x_1343_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1342_, v_x_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1345_, lean_object* v_a_1346_, lean_object* v_x_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7(v_00_u03b2_1345_, v_a_1346_, v_x_1347_);
lean_dec(v_x_1347_);
lean_dec(v_a_1346_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(lean_object* v_hi_1349_, lean_object* v_pivot_1350_, lean_object* v_as_1351_, lean_object* v_i_1352_, lean_object* v_k_1353_){
_start:
{
uint8_t v___x_1354_; 
v___x_1354_ = lean_nat_dec_lt(v_k_1353_, v_hi_1349_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec(v_k_1353_);
v___x_1355_ = lean_array_fswap(v_as_1351_, v_i_1352_, v_hi_1349_);
v___x_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1356_, 0, v_i_1352_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
return v___x_1356_;
}
else
{
lean_object* v___x_1357_; lean_object* v_fst_1358_; lean_object* v_fst_1359_; uint8_t v___x_1360_; 
v___x_1357_ = lean_array_fget_borrowed(v_as_1351_, v_k_1353_);
v_fst_1358_ = lean_ctor_get(v___x_1357_, 0);
v_fst_1359_ = lean_ctor_get(v_pivot_1350_, 0);
v___x_1360_ = lean_nat_dec_lt(v_fst_1358_, v_fst_1359_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = lean_unsigned_to_nat(1u);
v___x_1362_ = lean_nat_add(v_k_1353_, v___x_1361_);
lean_dec(v_k_1353_);
v_k_1353_ = v___x_1362_;
goto _start;
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1364_ = lean_array_fswap(v_as_1351_, v_i_1352_, v_k_1353_);
v___x_1365_ = lean_unsigned_to_nat(1u);
v___x_1366_ = lean_nat_add(v_i_1352_, v___x_1365_);
lean_dec(v_i_1352_);
v___x_1367_ = lean_nat_add(v_k_1353_, v___x_1365_);
lean_dec(v_k_1353_);
v_as_1351_ = v___x_1364_;
v_i_1352_ = v___x_1366_;
v_k_1353_ = v___x_1367_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg___boxed(lean_object* v_hi_1369_, lean_object* v_pivot_1370_, lean_object* v_as_1371_, lean_object* v_i_1372_, lean_object* v_k_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1369_, v_pivot_1370_, v_as_1371_, v_i_1372_, v_k_1373_);
lean_dec_ref(v_pivot_1370_);
lean_dec(v_hi_1369_);
return v_res_1374_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(lean_object* v_x1_1375_, lean_object* v_x2_1376_){
_start:
{
lean_object* v_fst_1377_; lean_object* v_fst_1378_; uint8_t v___x_1379_; 
v_fst_1377_ = lean_ctor_get(v_x1_1375_, 0);
v_fst_1378_ = lean_ctor_get(v_x2_1376_, 0);
v___x_1379_ = lean_nat_dec_lt(v_fst_1377_, v_fst_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed(lean_object* v_x1_1380_, lean_object* v_x2_1381_){
_start:
{
uint8_t v_res_1382_; lean_object* v_r_1383_; 
v_res_1382_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v_x1_1380_, v_x2_1381_);
lean_dec_ref(v_x2_1381_);
lean_dec_ref(v_x1_1380_);
v_r_1383_ = lean_box(v_res_1382_);
return v_r_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(lean_object* v_n_1384_, lean_object* v_as_1385_, lean_object* v_lo_1386_, lean_object* v_hi_1387_){
_start:
{
lean_object* v___y_1389_; uint8_t v___x_1399_; 
v___x_1399_ = lean_nat_dec_lt(v_lo_1386_, v_hi_1387_);
if (v___x_1399_ == 0)
{
lean_dec(v_lo_1386_);
return v_as_1385_;
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v_mid_1402_; lean_object* v___y_1404_; lean_object* v___y_1410_; lean_object* v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1400_ = lean_nat_add(v_lo_1386_, v_hi_1387_);
v___x_1401_ = lean_unsigned_to_nat(1u);
v_mid_1402_ = lean_nat_shiftr(v___x_1400_, v___x_1401_);
lean_dec(v___x_1400_);
v___x_1415_ = lean_array_fget_borrowed(v_as_1385_, v_mid_1402_);
v___x_1416_ = lean_array_fget_borrowed(v_as_1385_, v_lo_1386_);
v___x_1417_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1415_, v___x_1416_);
if (v___x_1417_ == 0)
{
v___y_1410_ = v_as_1385_;
goto v___jp_1409_;
}
else
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_array_fswap(v_as_1385_, v_lo_1386_, v_mid_1402_);
v___y_1410_ = v___x_1418_;
goto v___jp_1409_;
}
v___jp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1405_ = lean_array_fget_borrowed(v___y_1404_, v_mid_1402_);
v___x_1406_ = lean_array_fget_borrowed(v___y_1404_, v_hi_1387_);
v___x_1407_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1405_, v___x_1406_);
if (v___x_1407_ == 0)
{
lean_dec(v_mid_1402_);
v___y_1389_ = v___y_1404_;
goto v___jp_1388_;
}
else
{
lean_object* v___x_1408_; 
v___x_1408_ = lean_array_fswap(v___y_1404_, v_mid_1402_, v_hi_1387_);
lean_dec(v_mid_1402_);
v___y_1389_ = v___x_1408_;
goto v___jp_1388_;
}
}
v___jp_1409_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v___x_1411_ = lean_array_fget_borrowed(v___y_1410_, v_hi_1387_);
v___x_1412_ = lean_array_fget_borrowed(v___y_1410_, v_lo_1386_);
v___x_1413_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1411_, v___x_1412_);
if (v___x_1413_ == 0)
{
v___y_1404_ = v___y_1410_;
goto v___jp_1403_;
}
else
{
lean_object* v___x_1414_; 
v___x_1414_ = lean_array_fswap(v___y_1410_, v_lo_1386_, v_hi_1387_);
v___y_1404_ = v___x_1414_;
goto v___jp_1403_;
}
}
}
v___jp_1388_:
{
lean_object* v_pivot_1390_; lean_object* v___x_1391_; lean_object* v_fst_1392_; lean_object* v_snd_1393_; uint8_t v___x_1394_; 
v_pivot_1390_ = lean_array_fget(v___y_1389_, v_hi_1387_);
lean_inc_n(v_lo_1386_, 2);
v___x_1391_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1387_, v_pivot_1390_, v___y_1389_, v_lo_1386_, v_lo_1386_);
lean_dec(v_pivot_1390_);
v_fst_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_fst_1392_);
v_snd_1393_ = lean_ctor_get(v___x_1391_, 1);
lean_inc(v_snd_1393_);
lean_dec_ref(v___x_1391_);
v___x_1394_ = lean_nat_dec_le(v_hi_1387_, v_fst_1392_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1395_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1384_, v_snd_1393_, v_lo_1386_, v_fst_1392_);
v___x_1396_ = lean_unsigned_to_nat(1u);
v___x_1397_ = lean_nat_add(v_fst_1392_, v___x_1396_);
lean_dec(v_fst_1392_);
v_as_1385_ = v___x_1395_;
v_lo_1386_ = v___x_1397_;
goto _start;
}
else
{
lean_dec(v_fst_1392_);
lean_dec(v_lo_1386_);
return v_snd_1393_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___boxed(lean_object* v_n_1419_, lean_object* v_as_1420_, lean_object* v_lo_1421_, lean_object* v_hi_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1419_, v_as_1420_, v_lo_1421_, v_hi_1422_);
lean_dec(v_hi_1422_);
lean_dec(v_n_1419_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg(lean_object* v_upperBound_1424_, lean_object* v___x_1425_, lean_object* v_op_1426_, lean_object* v_a_1427_, lean_object* v_b_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___y_1432_; uint8_t v___x_1436_; 
v___x_1436_ = lean_nat_dec_lt(v_a_1427_, v_upperBound_1424_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
lean_dec(v_a_1427_);
lean_dec_ref(v_op_1426_);
lean_dec_ref(v___x_1425_);
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v_b_1428_);
lean_ctor_set(v___x_1437_, 1, v___y_1429_);
v___x_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
return v___x_1438_;
}
else
{
if (lean_obj_tag(v_b_1428_) == 0)
{
lean_object* v___x_1439_; 
lean_inc_ref(v___x_1425_);
v___x_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1425_);
v___y_1432_ = v___x_1439_;
goto v___jp_1431_;
}
else
{
lean_object* v_val_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1449_; 
v_val_1440_ = lean_ctor_get(v_b_1428_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_b_1428_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1442_ = v_b_1428_;
v_isShared_1443_ = v_isSharedCheck_1449_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_val_1440_);
lean_dec(v_b_1428_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1449_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1447_; 
lean_inc_ref(v_op_1426_);
v___x_1444_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_op_1426_);
lean_inc_ref(v___x_1425_);
v___x_1445_ = l_Lean_mkAppB(v___x_1444_, v_val_1440_, v___x_1425_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v___x_1445_);
v___x_1447_ = v___x_1442_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
v___y_1432_ = v___x_1447_;
goto v___jp_1431_;
}
}
}
}
v___jp_1431_:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = lean_unsigned_to_nat(1u);
v___x_1434_ = lean_nat_add(v_a_1427_, v___x_1433_);
lean_dec(v_a_1427_);
v_a_1427_ = v___x_1434_;
v_b_1428_ = v___y_1432_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg___boxed(lean_object* v_upperBound_1450_, lean_object* v___x_1451_, lean_object* v_op_1452_, lean_object* v_a_1453_, lean_object* v_b_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1450_, v___x_1451_, v_op_1452_, v_a_1453_, v_b_1454_, v___y_1455_);
lean_dec(v_upperBound_1450_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__1(lean_object* v_op_1458_, lean_object* v_as_1459_, size_t v_sz_1460_, size_t v_i_1461_, lean_object* v_b_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
uint8_t v___x_1469_; 
v___x_1469_ = lean_usize_dec_lt(v_i_1461_, v_sz_1460_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_dec_ref(v_op_1458_);
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v_b_1462_);
lean_ctor_set(v___x_1470_, 1, v___y_1463_);
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
else
{
lean_object* v_a_1472_; lean_object* v_fst_1473_; lean_object* v_snd_1474_; lean_object* v_varToExpr_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v_a_1472_ = lean_array_uget_borrowed(v_as_1459_, v_i_1461_);
v_fst_1473_ = lean_ctor_get(v_a_1472_, 0);
v_snd_1474_ = lean_ctor_get(v_a_1472_, 1);
v_varToExpr_1475_ = lean_ctor_get(v___y_1463_, 2);
v___x_1476_ = l_Lean_instInhabitedExpr;
v___x_1477_ = lean_unsigned_to_nat(0u);
v___x_1478_ = lean_array_get(v___x_1476_, v_varToExpr_1475_, v_fst_1473_);
lean_inc_ref(v_op_1458_);
v___x_1479_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_snd_1474_, v___x_1478_, v_op_1458_, v___x_1477_, v_b_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v_fst_1481_; lean_object* v_snd_1482_; size_t v___x_1483_; size_t v___x_1484_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1480_);
lean_dec_ref(v___x_1479_);
v_fst_1481_ = lean_ctor_get(v_a_1480_, 0);
lean_inc(v_fst_1481_);
v_snd_1482_ = lean_ctor_get(v_a_1480_, 1);
lean_inc(v_snd_1482_);
lean_dec(v_a_1480_);
v___x_1483_ = ((size_t)1ULL);
v___x_1484_ = lean_usize_add(v_i_1461_, v___x_1483_);
v_i_1461_ = v___x_1484_;
v_b_1462_ = v_fst_1481_;
v___y_1463_ = v_snd_1482_;
goto _start;
}
else
{
lean_dec_ref(v_op_1458_);
return v___x_1479_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__1___boxed(lean_object* v_op_1486_, lean_object* v_as_1487_, lean_object* v_sz_1488_, lean_object* v_i_1489_, lean_object* v_b_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
size_t v_sz_boxed_1497_; size_t v_i_boxed_1498_; lean_object* v_res_1499_; 
v_sz_boxed_1497_ = lean_unbox_usize(v_sz_1488_);
lean_dec(v_sz_1488_);
v_i_boxed_1498_ = lean_unbox_usize(v_i_1489_);
lean_dec(v_i_1489_);
v_res_1499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1486_, v_as_1487_, v_sz_boxed_1497_, v_i_boxed_1498_, v_b_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec_ref(v_as_1487_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__3(lean_object* v_x_1500_, lean_object* v_x_1501_){
_start:
{
if (lean_obj_tag(v_x_1501_) == 0)
{
return v_x_1500_;
}
else
{
lean_object* v_key_1502_; lean_object* v_value_1503_; lean_object* v_tail_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v_key_1502_ = lean_ctor_get(v_x_1501_, 0);
v_value_1503_ = lean_ctor_get(v_x_1501_, 1);
v_tail_1504_ = lean_ctor_get(v_x_1501_, 2);
lean_inc(v_value_1503_);
lean_inc(v_key_1502_);
v___x_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1505_, 0, v_key_1502_);
lean_ctor_set(v___x_1505_, 1, v_value_1503_);
v___x_1506_ = lean_array_push(v_x_1500_, v___x_1505_);
v_x_1500_ = v___x_1506_;
v_x_1501_ = v_tail_1504_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__3___boxed(lean_object* v_x_1508_, lean_object* v_x_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__3(v_x_1508_, v_x_1509_);
lean_dec(v_x_1509_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4(lean_object* v_as_1511_, size_t v_i_1512_, size_t v_stop_1513_, lean_object* v_b_1514_){
_start:
{
uint8_t v___x_1515_; 
v___x_1515_ = lean_usize_dec_eq(v_i_1512_, v_stop_1513_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; size_t v___x_1518_; size_t v___x_1519_; 
v___x_1516_ = lean_array_uget_borrowed(v_as_1511_, v_i_1512_);
v___x_1517_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__3(v_b_1514_, v___x_1516_);
v___x_1518_ = ((size_t)1ULL);
v___x_1519_ = lean_usize_add(v_i_1512_, v___x_1518_);
v_i_1512_ = v___x_1519_;
v_b_1514_ = v___x_1517_;
goto _start;
}
else
{
return v_b_1514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4___boxed(lean_object* v_as_1521_, lean_object* v_i_1522_, lean_object* v_stop_1523_, lean_object* v_b_1524_){
_start:
{
size_t v_i_boxed_1525_; size_t v_stop_boxed_1526_; lean_object* v_res_1527_; 
v_i_boxed_1525_ = lean_unbox_usize(v_i_1522_);
lean_dec(v_i_1522_);
v_stop_boxed_1526_ = lean_unbox_usize(v_stop_1523_);
lean_dec(v_stop_1523_);
v_res_1527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4(v_as_1521_, v_i_boxed_1525_, v_stop_boxed_1526_, v_b_1524_);
lean_dec_ref(v_as_1521_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(lean_object* v_coeff_1528_, lean_object* v_op_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v___y_1537_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1555_; lean_object* v_size_1562_; lean_object* v_buckets_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; 
v_size_1562_ = lean_ctor_get(v_coeff_1528_, 0);
v_buckets_1563_ = lean_ctor_get(v_coeff_1528_, 1);
v___x_1564_ = lean_mk_empty_array_with_capacity(v_size_1562_);
v___x_1565_ = lean_unsigned_to_nat(0u);
v___x_1566_ = lean_array_get_size(v_buckets_1563_);
v___x_1567_ = lean_nat_dec_lt(v___x_1565_, v___x_1566_);
if (v___x_1567_ == 0)
{
v___y_1555_ = v___x_1564_;
goto v___jp_1554_;
}
else
{
uint8_t v___x_1568_; 
v___x_1568_ = lean_nat_dec_le(v___x_1566_, v___x_1566_);
if (v___x_1568_ == 0)
{
if (v___x_1567_ == 0)
{
v___y_1555_ = v___x_1564_;
goto v___jp_1554_;
}
else
{
size_t v___x_1569_; size_t v___x_1570_; lean_object* v___x_1571_; 
v___x_1569_ = ((size_t)0ULL);
v___x_1570_ = lean_usize_of_nat(v___x_1566_);
v___x_1571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4(v_buckets_1563_, v___x_1569_, v___x_1570_, v___x_1564_);
v___y_1555_ = v___x_1571_;
goto v___jp_1554_;
}
}
else
{
size_t v___x_1572_; size_t v___x_1573_; lean_object* v___x_1574_; 
v___x_1572_ = ((size_t)0ULL);
v___x_1573_ = lean_usize_of_nat(v___x_1566_);
v___x_1574_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4(v_buckets_1563_, v___x_1572_, v___x_1573_, v___x_1564_);
v___y_1555_ = v___x_1574_;
goto v___jp_1554_;
}
}
v___jp_1536_:
{
lean_object* v_acc_1538_; size_t v_sz_1539_; size_t v___x_1540_; lean_object* v___x_1541_; 
v_acc_1538_ = lean_box(0);
v_sz_1539_ = lean_array_size(v___y_1537_);
v___x_1540_ = ((size_t)0ULL);
v___x_1541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1529_, v___y_1537_, v_sz_1539_, v___x_1540_, v_acc_1538_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
lean_dec_ref(v___y_1537_);
return v___x_1541_;
}
v___jp_1542_:
{
lean_object* v___x_1547_; 
v___x_1547_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v___y_1545_, v___y_1544_, v___y_1543_, v___y_1546_);
lean_dec(v___y_1546_);
lean_dec(v___y_1545_);
v___y_1537_ = v___x_1547_;
goto v___jp_1536_;
}
v___jp_1548_:
{
uint8_t v___x_1553_; 
v___x_1553_ = lean_nat_dec_le(v___y_1552_, v___y_1551_);
if (v___x_1553_ == 0)
{
lean_dec(v___y_1551_);
lean_inc(v___y_1552_);
v___y_1543_ = v___y_1552_;
v___y_1544_ = v___y_1549_;
v___y_1545_ = v___y_1550_;
v___y_1546_ = v___y_1552_;
goto v___jp_1542_;
}
else
{
v___y_1543_ = v___y_1552_;
v___y_1544_ = v___y_1549_;
v___y_1545_ = v___y_1550_;
v___y_1546_ = v___y_1551_;
goto v___jp_1542_;
}
}
v___jp_1554_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1556_ = lean_array_get_size(v___y_1555_);
v___x_1557_ = lean_unsigned_to_nat(0u);
v___x_1558_ = lean_nat_dec_eq(v___x_1556_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
v___x_1559_ = lean_unsigned_to_nat(1u);
v___x_1560_ = lean_nat_sub(v___x_1556_, v___x_1559_);
v___x_1561_ = lean_nat_dec_le(v___x_1557_, v___x_1560_);
if (v___x_1561_ == 0)
{
lean_inc(v___x_1560_);
v___y_1549_ = v___y_1555_;
v___y_1550_ = v___x_1556_;
v___y_1551_ = v___x_1560_;
v___y_1552_ = v___x_1560_;
goto v___jp_1548_;
}
else
{
v___y_1549_ = v___y_1555_;
v___y_1550_ = v___x_1556_;
v___y_1551_ = v___x_1560_;
v___y_1552_ = v___x_1557_;
goto v___jp_1548_;
}
}
else
{
v___y_1537_ = v___y_1555_;
goto v___jp_1536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr___boxed(lean_object* v_coeff_1575_, lean_object* v_op_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_coeff_1575_, v_op_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
lean_dec(v_a_1579_);
lean_dec_ref(v_a_1578_);
lean_dec_ref(v_coeff_1575_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0(lean_object* v_upperBound_1584_, lean_object* v___x_1585_, lean_object* v_op_1586_, lean_object* v_inst_1587_, lean_object* v_R_1588_, lean_object* v_a_1589_, lean_object* v_b_1590_, lean_object* v_c_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1584_, v___x_1585_, v_op_1586_, v_a_1589_, v_b_1590_, v___y_1592_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___boxed(lean_object* v_upperBound_1599_, lean_object* v___x_1600_, lean_object* v_op_1601_, lean_object* v_inst_1602_, lean_object* v_R_1603_, lean_object* v_a_1604_, lean_object* v_b_1605_, lean_object* v_c_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0(v_upperBound_1599_, v___x_1600_, v_op_1601_, v_inst_1602_, v_R_1603_, v_a_1604_, v_b_1605_, v_c_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v_upperBound_1599_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2(lean_object* v_n_1614_, lean_object* v_as_1615_, lean_object* v_lo_1616_, lean_object* v_hi_1617_, lean_object* v_w_1618_, lean_object* v_hlo_1619_, lean_object* v_hhi_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1614_, v_as_1615_, v_lo_1616_, v_hi_1617_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___boxed(lean_object* v_n_1622_, lean_object* v_as_1623_, lean_object* v_lo_1624_, lean_object* v_hi_1625_, lean_object* v_w_1626_, lean_object* v_hlo_1627_, lean_object* v_hhi_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2(v_n_1622_, v_as_1623_, v_lo_1624_, v_hi_1625_, v_w_1626_, v_hlo_1627_, v_hhi_1628_);
lean_dec(v_hi_1625_);
lean_dec(v_n_1622_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(lean_object* v_n_1630_, lean_object* v_lo_1631_, lean_object* v_hi_1632_, lean_object* v_hhi_1633_, lean_object* v_pivot_1634_, lean_object* v_as_1635_, lean_object* v_i_1636_, lean_object* v_k_1637_, lean_object* v_ilo_1638_, lean_object* v_ik_1639_, lean_object* v_w_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1632_, v_pivot_1634_, v_as_1635_, v_i_1636_, v_k_1637_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___boxed(lean_object* v_n_1642_, lean_object* v_lo_1643_, lean_object* v_hi_1644_, lean_object* v_hhi_1645_, lean_object* v_pivot_1646_, lean_object* v_as_1647_, lean_object* v_i_1648_, lean_object* v_k_1649_, lean_object* v_ilo_1650_, lean_object* v_ik_1651_, lean_object* v_w_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(v_n_1642_, v_lo_1643_, v_hi_1644_, v_hhi_1645_, v_pivot_1646_, v_as_1647_, v_i_1648_, v_k_1649_, v_ilo_1650_, v_ik_1651_, v_w_1652_);
lean_dec_ref(v_pivot_1646_);
lean_dec(v_hi_1644_);
lean_dec(v_lo_1643_);
lean_dec(v_n_1642_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(lean_object* v_e_1654_, lean_object* v___y_1655_){
_start:
{
uint8_t v___x_1657_; 
v___x_1657_ = l_Lean_Expr_hasMVar(v_e_1654_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v_e_1654_);
return v___x_1658_;
}
else
{
lean_object* v___x_1659_; lean_object* v_mctx_1660_; lean_object* v___x_1661_; lean_object* v_fst_1662_; lean_object* v_snd_1663_; lean_object* v___x_1664_; lean_object* v_cache_1665_; lean_object* v_zetaDeltaFVarIds_1666_; lean_object* v_postponed_1667_; lean_object* v_diag_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1677_; 
v___x_1659_ = lean_st_ref_get(v___y_1655_);
v_mctx_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc_ref(v_mctx_1660_);
lean_dec(v___x_1659_);
v___x_1661_ = l_Lean_instantiateMVarsCore(v_mctx_1660_, v_e_1654_);
v_fst_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_fst_1662_);
v_snd_1663_ = lean_ctor_get(v___x_1661_, 1);
lean_inc(v_snd_1663_);
lean_dec_ref(v___x_1661_);
v___x_1664_ = lean_st_ref_take(v___y_1655_);
v_cache_1665_ = lean_ctor_get(v___x_1664_, 1);
v_zetaDeltaFVarIds_1666_ = lean_ctor_get(v___x_1664_, 2);
v_postponed_1667_ = lean_ctor_get(v___x_1664_, 3);
v_diag_1668_ = lean_ctor_get(v___x_1664_, 4);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1677_ == 0)
{
lean_object* v_unused_1678_; 
v_unused_1678_ = lean_ctor_get(v___x_1664_, 0);
lean_dec(v_unused_1678_);
v___x_1670_ = v___x_1664_;
v_isShared_1671_ = v_isSharedCheck_1677_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_diag_1668_);
lean_inc(v_postponed_1667_);
lean_inc(v_zetaDeltaFVarIds_1666_);
lean_inc(v_cache_1665_);
lean_dec(v___x_1664_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1677_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v_snd_1663_);
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_snd_1663_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_cache_1665_);
lean_ctor_set(v_reuseFailAlloc_1676_, 2, v_zetaDeltaFVarIds_1666_);
lean_ctor_set(v_reuseFailAlloc_1676_, 3, v_postponed_1667_);
lean_ctor_set(v_reuseFailAlloc_1676_, 4, v_diag_1668_);
v___x_1673_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = lean_st_ref_set(v___y_1655_, v___x_1673_);
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v_fst_1662_);
return v___x_1675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg___boxed(lean_object* v_e_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1679_, v___y_1680_);
lean_dec(v___y_1680_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0(lean_object* v_e_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1683_, v___y_1685_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___boxed(lean_object* v_e_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0(v_e_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC(lean_object* v_x_1697_, lean_object* v_y_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_Meta_mkEq(v_x_1697_, v_y_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1727_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1727_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1727_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set_tag(v___x_1707_, 1);
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
uint8_t v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1711_ = 0;
v___x_1712_ = lean_box(0);
v___x_1713_ = l_Lean_Meta_mkFreshExprMVar(v___x_1710_, v___x_1711_, v___x_1712_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1714_);
lean_dec_ref(v___x_1713_);
v___x_1715_ = l_Lean_Expr_mvarId_x21(v_a_1714_);
v___x_1716_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v___x_1715_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v___x_1717_; 
lean_dec_ref(v___x_1716_);
v___x_1717_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(v_a_1714_, v_a_1700_);
return v___x_1717_;
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec(v_a_1714_);
v_a_1718_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1716_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1716_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
else
{
return v___x_1713_;
}
}
}
}
else
{
return v___x_1704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC___boxed(lean_object* v_x_1728_, lean_object* v_y_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC(v_x_1728_, v_y_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
return v_res_1735_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = lean_unsigned_to_nat(32u);
v___x_1737_ = lean_mk_empty_array_with_capacity(v___x_1736_);
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
return v___x_1738_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1739_ = ((size_t)5ULL);
v___x_1740_ = lean_unsigned_to_nat(0u);
v___x_1741_ = lean_unsigned_to_nat(32u);
v___x_1742_ = lean_mk_empty_array_with_capacity(v___x_1741_);
v___x_1743_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0);
v___x_1744_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
lean_ctor_set(v___x_1744_, 1, v___x_1742_);
lean_ctor_set(v___x_1744_, 2, v___x_1740_);
lean_ctor_set(v___x_1744_, 3, v___x_1740_);
lean_ctor_set_usize(v___x_1744_, 4, v___x_1739_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(lean_object* v___y_1745_){
_start:
{
lean_object* v___x_1747_; lean_object* v_traceState_1748_; lean_object* v_traces_1749_; lean_object* v___x_1750_; lean_object* v_traceState_1751_; lean_object* v_env_1752_; lean_object* v_nextMacroScope_1753_; lean_object* v_ngen_1754_; lean_object* v_auxDeclNGen_1755_; lean_object* v_cache_1756_; lean_object* v_messages_1757_; lean_object* v_infoState_1758_; lean_object* v_snapshotTasks_1759_; lean_object* v_newDecls_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1779_; 
v___x_1747_ = lean_st_ref_get(v___y_1745_);
v_traceState_1748_ = lean_ctor_get(v___x_1747_, 4);
lean_inc_ref(v_traceState_1748_);
lean_dec(v___x_1747_);
v_traces_1749_ = lean_ctor_get(v_traceState_1748_, 0);
lean_inc_ref(v_traces_1749_);
lean_dec_ref(v_traceState_1748_);
v___x_1750_ = lean_st_ref_take(v___y_1745_);
v_traceState_1751_ = lean_ctor_get(v___x_1750_, 4);
v_env_1752_ = lean_ctor_get(v___x_1750_, 0);
v_nextMacroScope_1753_ = lean_ctor_get(v___x_1750_, 1);
v_ngen_1754_ = lean_ctor_get(v___x_1750_, 2);
v_auxDeclNGen_1755_ = lean_ctor_get(v___x_1750_, 3);
v_cache_1756_ = lean_ctor_get(v___x_1750_, 5);
v_messages_1757_ = lean_ctor_get(v___x_1750_, 6);
v_infoState_1758_ = lean_ctor_get(v___x_1750_, 7);
v_snapshotTasks_1759_ = lean_ctor_get(v___x_1750_, 8);
v_newDecls_1760_ = lean_ctor_get(v___x_1750_, 9);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1762_ = v___x_1750_;
v_isShared_1763_ = v_isSharedCheck_1779_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_newDecls_1760_);
lean_inc(v_snapshotTasks_1759_);
lean_inc(v_infoState_1758_);
lean_inc(v_messages_1757_);
lean_inc(v_cache_1756_);
lean_inc(v_traceState_1751_);
lean_inc(v_auxDeclNGen_1755_);
lean_inc(v_ngen_1754_);
lean_inc(v_nextMacroScope_1753_);
lean_inc(v_env_1752_);
lean_dec(v___x_1750_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1779_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
uint64_t v_tid_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1777_; 
v_tid_1764_ = lean_ctor_get_uint64(v_traceState_1751_, sizeof(void*)*1);
v_isSharedCheck_1777_ = !lean_is_exclusive(v_traceState_1751_);
if (v_isSharedCheck_1777_ == 0)
{
lean_object* v_unused_1778_; 
v_unused_1778_ = lean_ctor_get(v_traceState_1751_, 0);
lean_dec(v_unused_1778_);
v___x_1766_ = v_traceState_1751_;
v_isShared_1767_ = v_isSharedCheck_1777_;
goto v_resetjp_1765_;
}
else
{
lean_dec(v_traceState_1751_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1777_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1768_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v___x_1768_);
v___x_1770_ = v___x_1766_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1768_);
lean_ctor_set_uint64(v_reuseFailAlloc_1776_, sizeof(void*)*1, v_tid_1764_);
v___x_1770_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1772_; 
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 4, v___x_1770_);
v___x_1772_ = v___x_1762_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_env_1752_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_nextMacroScope_1753_);
lean_ctor_set(v_reuseFailAlloc_1775_, 2, v_ngen_1754_);
lean_ctor_set(v_reuseFailAlloc_1775_, 3, v_auxDeclNGen_1755_);
lean_ctor_set(v_reuseFailAlloc_1775_, 4, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1775_, 5, v_cache_1756_);
lean_ctor_set(v_reuseFailAlloc_1775_, 6, v_messages_1757_);
lean_ctor_set(v_reuseFailAlloc_1775_, 7, v_infoState_1758_);
lean_ctor_set(v_reuseFailAlloc_1775_, 8, v_snapshotTasks_1759_);
lean_ctor_set(v_reuseFailAlloc_1775_, 9, v_newDecls_1760_);
v___x_1772_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = lean_st_ref_set(v___y_1745_, v___x_1772_);
v___x_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1774_, 0, v_traces_1749_);
return v___x_1774_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___boxed(lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1780_);
lean_dec(v___y_1780_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1(lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1789_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1(v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
return v_res_1800_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(lean_object* v_opts_1801_, lean_object* v_opt_1802_){
_start:
{
lean_object* v_name_1803_; lean_object* v_defValue_1804_; lean_object* v_map_1805_; lean_object* v___x_1806_; 
v_name_1803_ = lean_ctor_get(v_opt_1802_, 0);
v_defValue_1804_ = lean_ctor_get(v_opt_1802_, 1);
v_map_1805_ = lean_ctor_get(v_opts_1801_, 0);
v___x_1806_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1805_, v_name_1803_);
if (lean_obj_tag(v___x_1806_) == 0)
{
uint8_t v___x_1807_; 
v___x_1807_ = lean_unbox(v_defValue_1804_);
return v___x_1807_;
}
else
{
lean_object* v_val_1808_; 
v_val_1808_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_val_1808_);
lean_dec_ref(v___x_1806_);
if (lean_obj_tag(v_val_1808_) == 1)
{
uint8_t v_v_1809_; 
v_v_1809_ = lean_ctor_get_uint8(v_val_1808_, 0);
lean_dec_ref(v_val_1808_);
return v_v_1809_;
}
else
{
uint8_t v___x_1810_; 
lean_dec(v_val_1808_);
v___x_1810_ = lean_unbox(v_defValue_1804_);
return v___x_1810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object* v_opts_1811_, lean_object* v_opt_1812_){
_start:
{
uint8_t v_res_1813_; lean_object* v_r_1814_; 
v_res_1813_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(v_opts_1811_, v_opt_1812_);
lean_dec_ref(v_opt_1812_);
lean_dec_ref(v_opts_1811_);
v_r_1814_ = lean_box(v_res_1813_);
return v_r_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(lean_object* v_cls_1815_, lean_object* v_____do__lift_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_options_1825_; uint8_t v_hasTrace_1826_; 
v_options_1825_ = lean_ctor_get(v___y_1822_, 2);
v_hasTrace_1826_ = lean_ctor_get_uint8(v_options_1825_, sizeof(void*)*1);
if (v_hasTrace_1826_ == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_dec(v_cls_1815_);
v___x_1827_ = lean_box(v_hasTrace_1826_);
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
return v___x_1828_;
}
else
{
lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1829_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_1830_ = l_Lean_Name_append(v___x_1829_, v_cls_1815_);
v___x_1831_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_1816_, v_options_1825_, v___x_1830_);
lean_dec(v___x_1830_);
v___x_1832_ = lean_box(v___x_1831_);
v___x_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
return v___x_1833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0___boxed(lean_object* v_cls_1834_, lean_object* v_____do__lift_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_1834_, v_____do__lift_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v_____do__lift_1835_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__1(lean_object* v___x_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_mkAppB(v___x_1845_, v___y_1846_, v___y_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2(lean_object* v_val_1849_, lean_object* v_lhs_1850_, lean_object* v_rhs_1851_, lean_object* v_P_1852_, uint8_t v___x_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v___x_1860_; 
lean_inc_ref(v_lhs_1850_);
lean_inc_ref(v_val_1849_);
v___x_1860_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(v_val_1849_, v_lhs_1850_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v_fst_1862_; lean_object* v_snd_1863_; lean_object* v___x_1864_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1861_);
lean_dec_ref(v___x_1860_);
v_fst_1862_ = lean_ctor_get(v_a_1861_, 0);
lean_inc(v_fst_1862_);
v_snd_1863_ = lean_ctor_get(v_a_1861_, 1);
lean_inc(v_snd_1863_);
lean_dec(v_a_1861_);
lean_inc_ref(v_rhs_1851_);
lean_inc_ref(v_val_1849_);
v___x_1864_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(v_val_1849_, v_rhs_1851_, v_snd_1863_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v_fst_1866_; lean_object* v_snd_1867_; lean_object* v___x_1868_; lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1959_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref(v___x_1864_);
v_fst_1866_ = lean_ctor_get(v_a_1865_, 0);
lean_inc(v_fst_1866_);
v_snd_1867_ = lean_ctor_get(v_a_1865_, 1);
lean_inc(v_snd_1867_);
lean_dec(v_a_1865_);
v___x_1868_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(v_fst_1862_, v_fst_1866_, v_snd_1867_);
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1871_ = v___x_1868_;
v_isShared_1872_ = v_isSharedCheck_1959_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1868_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1959_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v_fst_1873_; lean_object* v_snd_1874_; lean_object* v_common_1875_; lean_object* v_x_1876_; lean_object* v_y_1877_; lean_object* v___x_1878_; 
v_fst_1873_ = lean_ctor_get(v_a_1869_, 0);
lean_inc(v_fst_1873_);
v_snd_1874_ = lean_ctor_get(v_a_1869_, 1);
lean_inc(v_snd_1874_);
lean_dec(v_a_1869_);
v_common_1875_ = lean_ctor_get(v_fst_1873_, 0);
lean_inc_ref(v_common_1875_);
v_x_1876_ = lean_ctor_get(v_fst_1873_, 1);
lean_inc_ref(v_x_1876_);
v_y_1877_ = lean_ctor_get(v_fst_1873_, 2);
lean_inc_ref(v_y_1877_);
lean_dec(v_fst_1873_);
lean_inc_ref(v_val_1849_);
v___x_1878_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_common_1875_, v_val_1849_, v_snd_1874_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
lean_dec_ref(v_common_1875_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v_fst_1880_; lean_object* v_snd_1881_; lean_object* v___x_1882_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
lean_dec_ref(v___x_1878_);
v_fst_1880_ = lean_ctor_get(v_a_1879_, 0);
lean_inc(v_fst_1880_);
v_snd_1881_ = lean_ctor_get(v_a_1879_, 1);
lean_inc(v_snd_1881_);
lean_dec(v_a_1879_);
lean_inc_ref(v_val_1849_);
v___x_1882_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_x_1876_, v_val_1849_, v_snd_1881_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
lean_dec_ref(v_x_1876_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v_fst_1884_; lean_object* v_snd_1885_; lean_object* v___x_1886_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref(v___x_1882_);
v_fst_1884_ = lean_ctor_get(v_a_1883_, 0);
lean_inc(v_fst_1884_);
v_snd_1885_ = lean_ctor_get(v_a_1883_, 1);
lean_inc(v_snd_1885_);
lean_dec(v_a_1883_);
lean_inc_ref(v_val_1849_);
v___x_1886_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_y_1877_, v_val_1849_, v_snd_1885_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
lean_dec_ref(v_y_1877_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v_fst_1888_; lean_object* v_snd_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1934_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref(v___x_1886_);
v_fst_1888_ = lean_ctor_get(v_a_1887_, 0);
v_snd_1889_ = lean_ctor_get(v_a_1887_, 1);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_a_1887_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1891_ = v_a_1887_;
v_isShared_1892_ = v_isSharedCheck_1934_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_snd_1889_);
lean_inc(v_fst_1888_);
lean_dec(v_a_1887_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1934_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___x_1924_; lean_object* v___f_1925_; lean_object* v___y_1927_; lean_object* v___x_1931_; 
lean_inc_ref(v_val_1849_);
v___x_1924_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_1849_);
v___f_1925_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_1925_, 0, v___x_1924_);
lean_inc(v_fst_1880_);
lean_inc_ref(v___f_1925_);
v___x_1931_ = l_Option_merge___redArg(v___f_1925_, v_fst_1880_, v_fst_1884_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v___x_1932_; 
lean_inc_ref(v_val_1849_);
v___x_1932_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_neutralElement(v_val_1849_);
v___y_1927_ = v___x_1932_;
goto v___jp_1926_;
}
else
{
lean_object* v_val_1933_; 
v_val_1933_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_val_1933_);
lean_dec_ref(v___x_1931_);
v___y_1927_ = v_val_1933_;
goto v___jp_1926_;
}
v___jp_1893_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
lean_inc_ref(v_P_1852_);
v___x_1896_ = l_Lean_mkAppB(v_P_1852_, v_lhs_1850_, v_rhs_1851_);
v___x_1897_ = l_Lean_mkAppB(v_P_1852_, v___y_1894_, v___y_1895_);
lean_inc_ref(v___x_1897_);
v___x_1898_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC(v___x_1896_, v___x_1897_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1915_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_1915_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1915_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set_tag(v___x_1871_, 1);
lean_ctor_set(v___x_1871_, 0, v_a_1899_);
v___x_1904_ = v___x_1871_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1905_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1905_, 0, v___x_1897_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
lean_ctor_set_uint8(v___x_1905_, sizeof(void*)*2, v___x_1853_);
v___x_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
v___x_1907_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1907_);
v___x_1909_ = v___x_1891_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1907_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_snd_1889_);
v___x_1909_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1911_; 
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v___x_1909_);
v___x_1911_ = v___x_1901_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec_ref(v___x_1897_);
lean_del_object(v___x_1891_);
lean_dec(v_snd_1889_);
lean_del_object(v___x_1871_);
v_a_1916_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1898_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1898_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
v___jp_1926_:
{
lean_object* v___x_1928_; 
v___x_1928_ = l_Option_merge___redArg(v___f_1925_, v_fst_1880_, v_fst_1888_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v___x_1929_; 
v___x_1929_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_neutralElement(v_val_1849_);
v___y_1894_ = v___y_1927_;
v___y_1895_ = v___x_1929_;
goto v___jp_1893_;
}
else
{
lean_object* v_val_1930_; 
lean_dec_ref(v_val_1849_);
v_val_1930_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_val_1930_);
lean_dec_ref(v___x_1928_);
v___y_1894_ = v___y_1927_;
v___y_1895_ = v_val_1930_;
goto v___jp_1893_;
}
}
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_dec(v_fst_1884_);
lean_dec(v_fst_1880_);
lean_del_object(v___x_1871_);
lean_dec_ref(v_P_1852_);
lean_dec_ref(v_rhs_1851_);
lean_dec_ref(v_lhs_1850_);
lean_dec_ref(v_val_1849_);
v_a_1935_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1886_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1886_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec(v_fst_1880_);
lean_dec_ref(v_y_1877_);
lean_del_object(v___x_1871_);
lean_dec_ref(v_P_1852_);
lean_dec_ref(v_rhs_1851_);
lean_dec_ref(v_lhs_1850_);
lean_dec_ref(v_val_1849_);
v_a_1943_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1882_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1882_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec_ref(v_y_1877_);
lean_dec_ref(v_x_1876_);
lean_del_object(v___x_1871_);
lean_dec_ref(v_P_1852_);
lean_dec_ref(v_rhs_1851_);
lean_dec_ref(v_lhs_1850_);
lean_dec_ref(v_val_1849_);
v_a_1951_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1878_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1878_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
lean_dec(v_fst_1862_);
lean_dec_ref(v_P_1852_);
lean_dec_ref(v_rhs_1851_);
lean_dec_ref(v_lhs_1850_);
lean_dec_ref(v_val_1849_);
v_a_1960_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1864_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1864_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_dec_ref(v_P_1852_);
lean_dec_ref(v_rhs_1851_);
lean_dec_ref(v_lhs_1850_);
lean_dec_ref(v_val_1849_);
v_a_1968_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1860_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1860_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object* v_val_1976_, lean_object* v_lhs_1977_, lean_object* v_rhs_1978_, lean_object* v_P_1979_, lean_object* v___x_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
uint8_t v___x_118211__boxed_1987_; lean_object* v_res_1988_; 
v___x_118211__boxed_1987_ = lean_unbox(v___x_1980_);
v_res_1988_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2(v_val_1976_, v_lhs_1977_, v_rhs_1978_, v_P_1979_, v___x_118211__boxed_1987_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
return v_res_1988_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_1991_ = l_Lean_stringToMessageData(v___x_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3(lean_object* v_x_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__1);
v___x_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object* v_x_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3(v_x_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v_x_2003_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__5(lean_object* v_val_2013_, lean_object* v_lhs_2014_, lean_object* v_rhs_2015_, lean_object* v_P_2016_, uint8_t v_hasTrace_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v___x_2024_; 
lean_inc_ref(v_lhs_2014_);
lean_inc_ref(v_val_2013_);
v___x_2024_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(v_val_2013_, v_lhs_2014_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v_fst_2026_; lean_object* v_snd_2027_; lean_object* v___x_2028_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref(v___x_2024_);
v_fst_2026_ = lean_ctor_get(v_a_2025_, 0);
lean_inc(v_fst_2026_);
v_snd_2027_ = lean_ctor_get(v_a_2025_, 1);
lean_inc(v_snd_2027_);
lean_dec(v_a_2025_);
lean_inc_ref(v_rhs_2015_);
lean_inc_ref(v_val_2013_);
v___x_2028_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(v_val_2013_, v_rhs_2015_, v_snd_2027_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v_fst_2030_; lean_object* v_snd_2031_; lean_object* v___x_2032_; lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2123_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_a_2029_);
lean_dec_ref(v___x_2028_);
v_fst_2030_ = lean_ctor_get(v_a_2029_, 0);
lean_inc(v_fst_2030_);
v_snd_2031_ = lean_ctor_get(v_a_2029_, 1);
lean_inc(v_snd_2031_);
lean_dec(v_a_2029_);
v___x_2032_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(v_fst_2026_, v_fst_2030_, v_snd_2031_);
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2035_ = v___x_2032_;
v_isShared_2036_ = v_isSharedCheck_2123_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2032_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2123_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v_fst_2037_; lean_object* v_snd_2038_; lean_object* v_common_2039_; lean_object* v_x_2040_; lean_object* v_y_2041_; lean_object* v___x_2042_; 
v_fst_2037_ = lean_ctor_get(v_a_2033_, 0);
lean_inc(v_fst_2037_);
v_snd_2038_ = lean_ctor_get(v_a_2033_, 1);
lean_inc(v_snd_2038_);
lean_dec(v_a_2033_);
v_common_2039_ = lean_ctor_get(v_fst_2037_, 0);
lean_inc_ref(v_common_2039_);
v_x_2040_ = lean_ctor_get(v_fst_2037_, 1);
lean_inc_ref(v_x_2040_);
v_y_2041_ = lean_ctor_get(v_fst_2037_, 2);
lean_inc_ref(v_y_2041_);
lean_dec(v_fst_2037_);
lean_inc_ref(v_val_2013_);
v___x_2042_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_common_2039_, v_val_2013_, v_snd_2038_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
lean_dec_ref(v_common_2039_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v_fst_2044_; lean_object* v_snd_2045_; lean_object* v___x_2046_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref(v___x_2042_);
v_fst_2044_ = lean_ctor_get(v_a_2043_, 0);
lean_inc(v_fst_2044_);
v_snd_2045_ = lean_ctor_get(v_a_2043_, 1);
lean_inc(v_snd_2045_);
lean_dec(v_a_2043_);
lean_inc_ref(v_val_2013_);
v___x_2046_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_x_2040_, v_val_2013_, v_snd_2045_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
lean_dec_ref(v_x_2040_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v_fst_2048_; lean_object* v_snd_2049_; lean_object* v___x_2050_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref(v___x_2046_);
v_fst_2048_ = lean_ctor_get(v_a_2047_, 0);
lean_inc(v_fst_2048_);
v_snd_2049_ = lean_ctor_get(v_a_2047_, 1);
lean_inc(v_snd_2049_);
lean_dec(v_a_2047_);
lean_inc_ref(v_val_2013_);
v___x_2050_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_y_2041_, v_val_2013_, v_snd_2049_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
lean_dec_ref(v_y_2041_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v_fst_2052_; lean_object* v_snd_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2098_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref(v___x_2050_);
v_fst_2052_ = lean_ctor_get(v_a_2051_, 0);
v_snd_2053_ = lean_ctor_get(v_a_2051_, 1);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_a_2051_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2055_ = v_a_2051_;
v_isShared_2056_ = v_isSharedCheck_2098_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_snd_2053_);
lean_inc(v_fst_2052_);
lean_dec(v_a_2051_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2098_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___x_2088_; lean_object* v___f_2089_; lean_object* v___y_2091_; lean_object* v___x_2095_; 
lean_inc_ref(v_val_2013_);
v___x_2088_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2013_);
v___f_2089_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_2089_, 0, v___x_2088_);
lean_inc(v_fst_2044_);
lean_inc_ref(v___f_2089_);
v___x_2095_ = l_Option_merge___redArg(v___f_2089_, v_fst_2044_, v_fst_2048_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v___x_2096_; 
lean_inc_ref(v_val_2013_);
v___x_2096_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_neutralElement(v_val_2013_);
v___y_2091_ = v___x_2096_;
goto v___jp_2090_;
}
else
{
lean_object* v_val_2097_; 
v_val_2097_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_val_2097_);
lean_dec_ref(v___x_2095_);
v___y_2091_ = v_val_2097_;
goto v___jp_2090_;
}
v___jp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
lean_inc_ref(v_P_2016_);
v___x_2060_ = l_Lean_mkAppB(v_P_2016_, v_lhs_2014_, v_rhs_2015_);
v___x_2061_ = l_Lean_mkAppB(v_P_2016_, v___y_2058_, v___y_2059_);
lean_inc_ref(v___x_2061_);
v___x_2062_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC(v___x_2060_, v___x_2061_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2079_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2079_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2079_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2036_ == 0)
{
lean_ctor_set_tag(v___x_2035_, 1);
lean_ctor_set(v___x_2035_, 0, v_a_2063_);
v___x_2068_ = v___x_2035_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2069_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2069_, 0, v___x_2061_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*2, v_hasTrace_2017_);
v___x_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
v___x_2071_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v___x_2071_);
v___x_2073_ = v___x_2055_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_snd_2053_);
v___x_2073_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2075_; 
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2073_);
v___x_2075_ = v___x_2065_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2073_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec_ref(v___x_2061_);
lean_del_object(v___x_2055_);
lean_dec(v_snd_2053_);
lean_del_object(v___x_2035_);
v_a_2080_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2062_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2062_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
v___jp_2090_:
{
lean_object* v___x_2092_; 
v___x_2092_ = l_Option_merge___redArg(v___f_2089_, v_fst_2044_, v_fst_2052_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_neutralElement(v_val_2013_);
v___y_2058_ = v___y_2091_;
v___y_2059_ = v___x_2093_;
goto v___jp_2057_;
}
else
{
lean_object* v_val_2094_; 
lean_dec_ref(v_val_2013_);
v_val_2094_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_val_2094_);
lean_dec_ref(v___x_2092_);
v___y_2058_ = v___y_2091_;
v___y_2059_ = v_val_2094_;
goto v___jp_2057_;
}
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec(v_fst_2048_);
lean_dec(v_fst_2044_);
lean_del_object(v___x_2035_);
lean_dec_ref(v_P_2016_);
lean_dec_ref(v_rhs_2015_);
lean_dec_ref(v_lhs_2014_);
lean_dec_ref(v_val_2013_);
v_a_2099_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2050_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2050_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec(v_fst_2044_);
lean_dec_ref(v_y_2041_);
lean_del_object(v___x_2035_);
lean_dec_ref(v_P_2016_);
lean_dec_ref(v_rhs_2015_);
lean_dec_ref(v_lhs_2014_);
lean_dec_ref(v_val_2013_);
v_a_2107_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2046_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2046_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
lean_dec_ref(v_y_2041_);
lean_dec_ref(v_x_2040_);
lean_del_object(v___x_2035_);
lean_dec_ref(v_P_2016_);
lean_dec_ref(v_rhs_2015_);
lean_dec_ref(v_lhs_2014_);
lean_dec_ref(v_val_2013_);
v_a_2115_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2042_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2042_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec(v_fst_2026_);
lean_dec_ref(v_P_2016_);
lean_dec_ref(v_rhs_2015_);
lean_dec_ref(v_lhs_2014_);
lean_dec_ref(v_val_2013_);
v_a_2124_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2028_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2028_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec_ref(v_P_2016_);
lean_dec_ref(v_rhs_2015_);
lean_dec_ref(v_lhs_2014_);
lean_dec_ref(v_val_2013_);
v_a_2132_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2024_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2024_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__5___boxed(lean_object* v_val_2140_, lean_object* v_lhs_2141_, lean_object* v_rhs_2142_, lean_object* v_P_2143_, lean_object* v_hasTrace_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
uint8_t v_hasTrace_boxed_2151_; lean_object* v_res_2152_; 
v_hasTrace_boxed_2151_ = lean_unbox(v_hasTrace_2144_);
v_res_2152_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__5(v_val_2140_, v_lhs_2141_, v_rhs_2142_, v_P_2143_, v_hasTrace_boxed_2151_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object* v_cls_2153_, lean_object* v_msg_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_ref_2160_; lean_object* v___x_2161_; lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2207_; 
v_ref_2160_ = lean_ctor_get(v___y_2157_, 5);
v___x_2161_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2164_ = v___x_2161_;
v_isShared_2165_ = v_isSharedCheck_2207_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2161_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2207_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; lean_object* v_traceState_2167_; lean_object* v_env_2168_; lean_object* v_nextMacroScope_2169_; lean_object* v_ngen_2170_; lean_object* v_auxDeclNGen_2171_; lean_object* v_cache_2172_; lean_object* v_messages_2173_; lean_object* v_infoState_2174_; lean_object* v_snapshotTasks_2175_; lean_object* v_newDecls_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2206_; 
v___x_2166_ = lean_st_ref_take(v___y_2158_);
v_traceState_2167_ = lean_ctor_get(v___x_2166_, 4);
v_env_2168_ = lean_ctor_get(v___x_2166_, 0);
v_nextMacroScope_2169_ = lean_ctor_get(v___x_2166_, 1);
v_ngen_2170_ = lean_ctor_get(v___x_2166_, 2);
v_auxDeclNGen_2171_ = lean_ctor_get(v___x_2166_, 3);
v_cache_2172_ = lean_ctor_get(v___x_2166_, 5);
v_messages_2173_ = lean_ctor_get(v___x_2166_, 6);
v_infoState_2174_ = lean_ctor_get(v___x_2166_, 7);
v_snapshotTasks_2175_ = lean_ctor_get(v___x_2166_, 8);
v_newDecls_2176_ = lean_ctor_get(v___x_2166_, 9);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2178_ = v___x_2166_;
v_isShared_2179_ = v_isSharedCheck_2206_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_newDecls_2176_);
lean_inc(v_snapshotTasks_2175_);
lean_inc(v_infoState_2174_);
lean_inc(v_messages_2173_);
lean_inc(v_cache_2172_);
lean_inc(v_traceState_2167_);
lean_inc(v_auxDeclNGen_2171_);
lean_inc(v_ngen_2170_);
lean_inc(v_nextMacroScope_2169_);
lean_inc(v_env_2168_);
lean_dec(v___x_2166_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2206_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
uint64_t v_tid_2180_; lean_object* v_traces_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2205_; 
v_tid_2180_ = lean_ctor_get_uint64(v_traceState_2167_, sizeof(void*)*1);
v_traces_2181_ = lean_ctor_get(v_traceState_2167_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_traceState_2167_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2183_ = v_traceState_2167_;
v_isShared_2184_ = v_isSharedCheck_2205_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_traces_2181_);
lean_dec(v_traceState_2167_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2205_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2185_; double v___x_2186_; uint8_t v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2185_ = lean_box(0);
v___x_2186_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0);
v___x_2187_ = 0;
v___x_2188_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1));
v___x_2189_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2189_, 0, v_cls_2153_);
lean_ctor_set(v___x_2189_, 1, v___x_2185_);
lean_ctor_set(v___x_2189_, 2, v___x_2188_);
lean_ctor_set_float(v___x_2189_, sizeof(void*)*3, v___x_2186_);
lean_ctor_set_float(v___x_2189_, sizeof(void*)*3 + 8, v___x_2186_);
lean_ctor_set_uint8(v___x_2189_, sizeof(void*)*3 + 16, v___x_2187_);
v___x_2190_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__2));
v___x_2191_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set(v___x_2191_, 1, v_a_2162_);
lean_ctor_set(v___x_2191_, 2, v___x_2190_);
lean_inc(v_ref_2160_);
v___x_2192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2192_, 0, v_ref_2160_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
v___x_2193_ = l_Lean_PersistentArray_push___redArg(v_traces_2181_, v___x_2192_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v___x_2193_);
v___x_2195_ = v___x_2183_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2193_);
lean_ctor_set_uint64(v_reuseFailAlloc_2204_, sizeof(void*)*1, v_tid_2180_);
v___x_2195_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2197_; 
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 4, v___x_2195_);
v___x_2197_ = v___x_2178_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_env_2168_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_nextMacroScope_2169_);
lean_ctor_set(v_reuseFailAlloc_2203_, 2, v_ngen_2170_);
lean_ctor_set(v_reuseFailAlloc_2203_, 3, v_auxDeclNGen_2171_);
lean_ctor_set(v_reuseFailAlloc_2203_, 4, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2203_, 5, v_cache_2172_);
lean_ctor_set(v_reuseFailAlloc_2203_, 6, v_messages_2173_);
lean_ctor_set(v_reuseFailAlloc_2203_, 7, v_infoState_2174_);
lean_ctor_set(v_reuseFailAlloc_2203_, 8, v_snapshotTasks_2175_);
lean_ctor_set(v_reuseFailAlloc_2203_, 9, v_newDecls_2176_);
v___x_2197_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2201_; 
v___x_2198_ = lean_st_ref_set(v___y_2158_, v___x_2197_);
v___x_2199_ = lean_box(0);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v___x_2199_);
v___x_2201_ = v___x_2164_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2199_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object* v_cls_2208_, lean_object* v_msg_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2208_, v_msg_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
return v_res_2215_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__1));
v___x_2220_ = l_Lean_stringToMessageData(v___x_2219_);
return v___x_2220_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__3));
v___x_2223_ = l_Lean_stringToMessageData(v___x_2222_);
return v___x_2223_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__5));
v___x_2226_ = l_Lean_stringToMessageData(v___x_2225_);
return v___x_2226_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__7(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2227_ = lean_box(0);
v___x_2228_ = lean_unsigned_to_nat(16u);
v___x_2229_ = lean_mk_array(v___x_2228_, v___x_2227_);
return v___x_2229_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2230_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__7);
v___x_2231_ = lean_unsigned_to_nat(0u);
v___x_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v___x_2230_);
return v___x_2232_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__10));
v___x_2237_ = l_Lean_stringToMessageData(v___x_2236_);
return v___x_2237_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13(void){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__12));
v___x_2240_ = l_Lean_stringToMessageData(v___x_2239_);
return v___x_2240_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15(void){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__14));
v___x_2243_ = l_Lean_stringToMessageData(v___x_2242_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4(lean_object* v_lhs_2244_, lean_object* v_rhs_2245_, lean_object* v___f_2246_, lean_object* v_cls_2247_, uint8_t v___x_2248_, lean_object* v_P_2249_, uint8_t v_hasTrace_2250_, lean_object* v_____r_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v___x_2269_; 
lean_inc_ref(v_lhs_2244_);
v___x_2269_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_lhs_2244_);
if (lean_obj_tag(v___x_2269_) == 1)
{
lean_object* v_val_2270_; lean_object* v___x_2271_; 
v_val_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_val_2270_);
lean_dec_ref(v___x_2269_);
lean_inc_ref(v_rhs_2245_);
v___x_2271_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_rhs_2245_);
if (lean_obj_tag(v___x_2271_) == 1)
{
lean_object* v_val_2272_; uint8_t v___x_2311_; 
v_val_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_val_2272_);
lean_dec_ref(v___x_2271_);
v___x_2311_ = lean_expr_eqv(v_val_2270_, v_val_2272_);
if (v___x_2311_ == 0)
{
lean_dec_ref(v_P_2249_);
goto v___jp_2273_;
}
else
{
if (v___x_2248_ == 0)
{
lean_object* v_options_2312_; lean_object* v_inheritedTraceOptions_2313_; uint8_t v_hasTrace_2314_; lean_object* v___x_2315_; lean_object* v___f_2316_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; 
lean_dec(v_val_2272_);
lean_dec_ref(v___f_2246_);
v_options_2312_ = lean_ctor_get(v___y_2257_, 2);
v_inheritedTraceOptions_2313_ = lean_ctor_get(v___y_2257_, 13);
v_hasTrace_2314_ = lean_ctor_get_uint8(v_options_2312_, sizeof(void*)*1);
v___x_2315_ = lean_box(v_hasTrace_2250_);
lean_inc(v_val_2270_);
v___f_2316_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__5___boxed), 11, 5);
lean_closure_set(v___f_2316_, 0, v_val_2270_);
lean_closure_set(v___f_2316_, 1, v_lhs_2244_);
lean_closure_set(v___f_2316_, 2, v_rhs_2245_);
lean_closure_set(v___f_2316_, 3, v_P_2249_);
lean_closure_set(v___f_2316_, 4, v___x_2315_);
if (v_hasTrace_2314_ == 0)
{
lean_dec(v_cls_2247_);
v___y_2318_ = v___y_2255_;
v___y_2319_ = v___y_2256_;
v___y_2320_ = v___y_2257_;
v___y_2321_ = v___y_2258_;
goto v___jp_2317_;
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; 
v___x_2326_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2247_);
v___x_2327_ = l_Lean_Name_append(v___x_2326_, v_cls_2247_);
v___x_2328_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2313_, v_options_2312_, v___x_2327_);
lean_dec(v___x_2327_);
if (v___x_2328_ == 0)
{
lean_dec(v_cls_2247_);
v___y_2318_ = v___y_2255_;
v___y_2319_ = v___y_2256_;
v___y_2320_ = v___y_2257_;
v___y_2321_ = v___y_2258_;
goto v___jp_2317_;
}
else
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2329_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11);
lean_inc(v_val_2270_);
v___x_2330_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2270_);
v___x_2331_ = l_Lean_MessageData_ofExpr(v___x_2330_);
v___x_2332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2329_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
v___x_2333_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13);
v___x_2334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2332_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2247_, v___x_2334_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_dec_ref(v___x_2335_);
v___y_2318_ = v___y_2255_;
v___y_2319_ = v___y_2256_;
v___y_2320_ = v___y_2257_;
v___y_2321_ = v___y_2258_;
goto v___jp_2317_;
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec_ref(v___f_2316_);
lean_dec(v_val_2270_);
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2335_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
}
v___jp_2317_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2322_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8);
v___x_2323_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__9));
v___x_2324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2324_, 0, v_val_2270_);
lean_ctor_set(v___x_2324_, 1, v___x_2322_);
lean_ctor_set(v___x_2324_, 2, v___x_2323_);
v___x_2325_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg(v___f_2316_, v___x_2324_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
return v___x_2325_;
}
}
else
{
lean_dec_ref(v_P_2249_);
goto v___jp_2273_;
}
}
v___jp_2273_:
{
lean_object* v_inheritedTraceOptions_2274_; lean_object* v___x_2275_; 
v_inheritedTraceOptions_2274_ = lean_ctor_get(v___y_2257_, 13);
lean_inc(v___y_2258_);
lean_inc_ref(v___y_2257_);
lean_inc(v___y_2256_);
lean_inc_ref(v___y_2255_);
lean_inc(v___y_2254_);
lean_inc_ref(v___y_2253_);
lean_inc(v___y_2252_);
lean_inc_ref(v_inheritedTraceOptions_2274_);
v___x_2275_ = lean_apply_9(v___f_2246_, v_inheritedTraceOptions_2274_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, lean_box(0));
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; uint8_t v___x_2277_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref(v___x_2275_);
v___x_2277_ = lean_unbox(v_a_2276_);
lean_dec(v_a_2276_);
if (v___x_2277_ == 0)
{
lean_dec(v_val_2272_);
lean_dec(v_val_2270_);
lean_dec(v_cls_2247_);
lean_dec_ref(v_rhs_2245_);
lean_dec_ref(v_lhs_2244_);
goto v___jp_2260_;
}
else
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2278_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2);
v___x_2279_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2270_);
v___x_2280_ = l_Lean_MessageData_ofExpr(v___x_2279_);
v___x_2281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2278_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
v___x_2282_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4);
v___x_2283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2281_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = l_Lean_indentExpr(v_lhs_2244_);
v___x_2285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2283_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v___x_2286_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6);
v___x_2287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2285_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
v___x_2288_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2272_);
v___x_2289_ = l_Lean_MessageData_ofExpr(v___x_2288_);
v___x_2290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2287_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
lean_ctor_set(v___x_2291_, 1, v___x_2282_);
v___x_2292_ = l_Lean_indentExpr(v_rhs_2245_);
v___x_2293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2247_, v___x_2293_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_dec_ref(v___x_2294_);
goto v___jp_2260_;
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2294_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec(v_val_2272_);
lean_dec(v_val_2270_);
lean_dec(v_cls_2247_);
lean_dec_ref(v_rhs_2245_);
lean_dec_ref(v_lhs_2244_);
v_a_2303_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2275_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2275_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2344_; lean_object* v___x_2345_; 
lean_dec(v___x_2271_);
lean_dec(v_val_2270_);
lean_dec_ref(v_P_2249_);
lean_dec_ref(v_lhs_2244_);
v_inheritedTraceOptions_2344_ = lean_ctor_get(v___y_2257_, 13);
lean_inc(v___y_2258_);
lean_inc_ref(v___y_2257_);
lean_inc(v___y_2256_);
lean_inc_ref(v___y_2255_);
lean_inc(v___y_2254_);
lean_inc_ref(v___y_2253_);
lean_inc(v___y_2252_);
lean_inc_ref(v_inheritedTraceOptions_2344_);
v___x_2345_ = lean_apply_9(v___f_2246_, v_inheritedTraceOptions_2344_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, lean_box(0));
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; uint8_t v___x_2347_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref(v___x_2345_);
v___x_2347_ = lean_unbox(v_a_2346_);
lean_dec(v_a_2346_);
if (v___x_2347_ == 0)
{
lean_dec(v_cls_2247_);
lean_dec_ref(v_rhs_2245_);
goto v___jp_2263_;
}
else
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2348_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2349_ = l_Lean_indentExpr(v_rhs_2245_);
v___x_2350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2348_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
v___x_2351_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2247_, v___x_2350_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_dec_ref(v___x_2351_);
goto v___jp_2263_;
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2351_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v_cls_2247_);
lean_dec_ref(v_rhs_2245_);
v_a_2360_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2345_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2345_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2368_; lean_object* v___x_2369_; 
lean_dec(v___x_2269_);
lean_dec_ref(v_P_2249_);
lean_dec_ref(v_rhs_2245_);
v_inheritedTraceOptions_2368_ = lean_ctor_get(v___y_2257_, 13);
lean_inc(v___y_2258_);
lean_inc_ref(v___y_2257_);
lean_inc(v___y_2256_);
lean_inc_ref(v___y_2255_);
lean_inc(v___y_2254_);
lean_inc_ref(v___y_2253_);
lean_inc(v___y_2252_);
lean_inc_ref(v_inheritedTraceOptions_2368_);
v___x_2369_ = lean_apply_9(v___f_2246_, v_inheritedTraceOptions_2368_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, lean_box(0));
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; uint8_t v___x_2371_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_a_2370_);
lean_dec_ref(v___x_2369_);
v___x_2371_ = lean_unbox(v_a_2370_);
lean_dec(v_a_2370_);
if (v___x_2371_ == 0)
{
lean_dec(v_cls_2247_);
lean_dec_ref(v_lhs_2244_);
goto v___jp_2266_;
}
else
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2372_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2373_ = l_Lean_indentExpr(v_lhs_2244_);
v___x_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2247_, v___x_2374_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_dec_ref(v___x_2375_);
goto v___jp_2266_;
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2375_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2375_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_dec(v_cls_2247_);
lean_dec_ref(v_lhs_2244_);
v_a_2384_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2369_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2369_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
v___jp_2260_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
return v___x_2262_;
}
v___jp_2263_:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
return v___x_2265_;
}
v___jp_2266_:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
return v___x_2268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___boxed(lean_object* v_lhs_2392_, lean_object* v_rhs_2393_, lean_object* v___f_2394_, lean_object* v_cls_2395_, lean_object* v___x_2396_, lean_object* v_P_2397_, lean_object* v_hasTrace_2398_, lean_object* v_____r_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
uint8_t v___x_118921__boxed_2408_; uint8_t v_hasTrace_boxed_2409_; lean_object* v_res_2410_; 
v___x_118921__boxed_2408_ = lean_unbox(v___x_2396_);
v_hasTrace_boxed_2409_ = lean_unbox(v_hasTrace_2398_);
v_res_2410_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2392_, v_rhs_2393_, v___f_2394_, v_cls_2395_, v___x_118921__boxed_2408_, v_P_2397_, v_hasTrace_boxed_2409_, v_____r_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__8(lean_object* v_lhs_2411_, lean_object* v_rhs_2412_, lean_object* v_P_2413_, uint8_t v___x_2414_, lean_object* v_cls_2415_, lean_object* v___f_2416_, lean_object* v_____r_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v___x_2435_; 
lean_inc_ref(v_lhs_2411_);
v___x_2435_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_lhs_2411_);
if (lean_obj_tag(v___x_2435_) == 1)
{
lean_object* v_val_2436_; lean_object* v___x_2437_; 
v_val_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_val_2436_);
lean_dec_ref(v___x_2435_);
lean_inc_ref(v_rhs_2412_);
v___x_2437_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_rhs_2412_);
if (lean_obj_tag(v___x_2437_) == 1)
{
lean_object* v_val_2438_; lean_object* v___x_2439_; lean_object* v___f_2440_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; uint8_t v___x_2472_; 
v_val_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_val_2438_);
lean_dec_ref(v___x_2437_);
v___x_2439_ = lean_box(v___x_2414_);
lean_inc_ref(v_rhs_2412_);
lean_inc_ref(v_lhs_2411_);
lean_inc(v_val_2436_);
v___f_2440_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___boxed), 11, 5);
lean_closure_set(v___f_2440_, 0, v_val_2436_);
lean_closure_set(v___f_2440_, 1, v_lhs_2411_);
lean_closure_set(v___f_2440_, 2, v_rhs_2412_);
lean_closure_set(v___f_2440_, 3, v_P_2413_);
lean_closure_set(v___f_2440_, 4, v___x_2439_);
v___x_2472_ = lean_expr_eqv(v_val_2436_, v_val_2438_);
if (v___x_2472_ == 0)
{
if (v___x_2414_ == 0)
{
lean_dec(v_val_2438_);
lean_dec_ref(v___f_2416_);
lean_dec_ref(v_rhs_2412_);
lean_dec_ref(v_lhs_2411_);
goto v___jp_2450_;
}
else
{
lean_object* v_inheritedTraceOptions_2473_; lean_object* v___x_2474_; 
lean_dec_ref(v___f_2440_);
v_inheritedTraceOptions_2473_ = lean_ctor_get(v___y_2423_, 13);
lean_inc(v___y_2424_);
lean_inc_ref(v___y_2423_);
lean_inc(v___y_2422_);
lean_inc_ref(v___y_2421_);
lean_inc(v___y_2420_);
lean_inc_ref(v___y_2419_);
lean_inc(v___y_2418_);
lean_inc_ref(v_inheritedTraceOptions_2473_);
v___x_2474_ = lean_apply_9(v___f_2416_, v_inheritedTraceOptions_2473_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, lean_box(0));
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; uint8_t v___x_2476_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref(v___x_2474_);
v___x_2476_ = lean_unbox(v_a_2475_);
lean_dec(v_a_2475_);
if (v___x_2476_ == 0)
{
lean_dec(v_val_2438_);
lean_dec(v_val_2436_);
lean_dec(v_cls_2415_);
lean_dec_ref(v_rhs_2412_);
lean_dec_ref(v_lhs_2411_);
goto v___jp_2426_;
}
else
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2477_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2);
v___x_2478_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2436_);
v___x_2479_ = l_Lean_MessageData_ofExpr(v___x_2478_);
v___x_2480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2477_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
v___x_2481_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4);
v___x_2482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2480_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
v___x_2483_ = l_Lean_indentExpr(v_lhs_2411_);
v___x_2484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2482_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
v___x_2485_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6);
v___x_2486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2484_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___x_2487_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2438_);
v___x_2488_ = l_Lean_MessageData_ofExpr(v___x_2487_);
v___x_2489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2486_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
v___x_2490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2489_);
lean_ctor_set(v___x_2490_, 1, v___x_2481_);
v___x_2491_ = l_Lean_indentExpr(v_rhs_2412_);
v___x_2492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2490_);
lean_ctor_set(v___x_2492_, 1, v___x_2491_);
v___x_2493_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2415_, v___x_2492_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_dec_ref(v___x_2493_);
goto v___jp_2426_;
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2493_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2493_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
}
else
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
lean_dec(v_val_2438_);
lean_dec(v_val_2436_);
lean_dec(v_cls_2415_);
lean_dec_ref(v_rhs_2412_);
lean_dec_ref(v_lhs_2411_);
v_a_2502_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v___x_2474_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2474_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
}
}
else
{
lean_dec(v_val_2438_);
lean_dec_ref(v___f_2416_);
lean_dec_ref(v_rhs_2412_);
lean_dec_ref(v_lhs_2411_);
goto v___jp_2450_;
}
v___jp_2441_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2446_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8);
v___x_2447_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__9));
v___x_2448_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2448_, 0, v_val_2436_);
lean_ctor_set(v___x_2448_, 1, v___x_2446_);
lean_ctor_set(v___x_2448_, 2, v___x_2447_);
v___x_2449_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg(v___f_2440_, v___x_2448_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
return v___x_2449_;
}
v___jp_2450_:
{
lean_object* v_options_2451_; uint8_t v_hasTrace_2452_; 
v_options_2451_ = lean_ctor_get(v___y_2423_, 2);
v_hasTrace_2452_ = lean_ctor_get_uint8(v_options_2451_, sizeof(void*)*1);
if (v_hasTrace_2452_ == 0)
{
lean_dec(v_cls_2415_);
v___y_2442_ = v___y_2421_;
v___y_2443_ = v___y_2422_;
v___y_2444_ = v___y_2423_;
v___y_2445_ = v___y_2424_;
goto v___jp_2441_;
}
else
{
lean_object* v_inheritedTraceOptions_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; 
v_inheritedTraceOptions_2453_ = lean_ctor_get(v___y_2423_, 13);
v___x_2454_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2415_);
v___x_2455_ = l_Lean_Name_append(v___x_2454_, v_cls_2415_);
v___x_2456_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2453_, v_options_2451_, v___x_2455_);
lean_dec(v___x_2455_);
if (v___x_2456_ == 0)
{
lean_dec(v_cls_2415_);
v___y_2442_ = v___y_2421_;
v___y_2443_ = v___y_2422_;
v___y_2444_ = v___y_2423_;
v___y_2445_ = v___y_2424_;
goto v___jp_2441_;
}
else
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2457_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11);
lean_inc(v_val_2436_);
v___x_2458_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2436_);
v___x_2459_ = l_Lean_MessageData_ofExpr(v___x_2458_);
v___x_2460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2457_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___x_2461_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13);
v___x_2462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2460_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2415_, v___x_2462_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_dec_ref(v___x_2463_);
v___y_2442_ = v___y_2421_;
v___y_2443_ = v___y_2422_;
v___y_2444_ = v___y_2423_;
v___y_2445_ = v___y_2424_;
goto v___jp_2441_;
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec_ref(v___f_2440_);
lean_dec(v_val_2436_);
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2463_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2463_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2510_; lean_object* v___x_2511_; 
lean_dec(v___x_2437_);
lean_dec(v_val_2436_);
lean_dec_ref(v_P_2413_);
lean_dec_ref(v_lhs_2411_);
v_inheritedTraceOptions_2510_ = lean_ctor_get(v___y_2423_, 13);
lean_inc(v___y_2424_);
lean_inc_ref(v___y_2423_);
lean_inc(v___y_2422_);
lean_inc_ref(v___y_2421_);
lean_inc(v___y_2420_);
lean_inc_ref(v___y_2419_);
lean_inc(v___y_2418_);
lean_inc_ref(v_inheritedTraceOptions_2510_);
v___x_2511_ = lean_apply_9(v___f_2416_, v_inheritedTraceOptions_2510_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, lean_box(0));
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; uint8_t v___x_2513_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2512_);
lean_dec_ref(v___x_2511_);
v___x_2513_ = lean_unbox(v_a_2512_);
lean_dec(v_a_2512_);
if (v___x_2513_ == 0)
{
lean_dec(v_cls_2415_);
lean_dec_ref(v_rhs_2412_);
goto v___jp_2429_;
}
else
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2514_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2515_ = l_Lean_indentExpr(v_rhs_2412_);
v___x_2516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2514_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2415_, v___x_2516_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_dec_ref(v___x_2517_);
goto v___jp_2429_;
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec(v_cls_2415_);
lean_dec_ref(v_rhs_2412_);
v_a_2526_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2511_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2511_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2534_; lean_object* v___x_2535_; 
lean_dec(v___x_2435_);
lean_dec_ref(v_P_2413_);
lean_dec_ref(v_rhs_2412_);
v_inheritedTraceOptions_2534_ = lean_ctor_get(v___y_2423_, 13);
lean_inc(v___y_2424_);
lean_inc_ref(v___y_2423_);
lean_inc(v___y_2422_);
lean_inc_ref(v___y_2421_);
lean_inc(v___y_2420_);
lean_inc_ref(v___y_2419_);
lean_inc(v___y_2418_);
lean_inc_ref(v_inheritedTraceOptions_2534_);
v___x_2535_ = lean_apply_9(v___f_2416_, v_inheritedTraceOptions_2534_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, lean_box(0));
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; uint8_t v___x_2537_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2536_);
lean_dec_ref(v___x_2535_);
v___x_2537_ = lean_unbox(v_a_2536_);
lean_dec(v_a_2536_);
if (v___x_2537_ == 0)
{
lean_dec(v_cls_2415_);
lean_dec_ref(v_lhs_2411_);
goto v___jp_2432_;
}
else
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2538_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2539_ = l_Lean_indentExpr(v_lhs_2411_);
v___x_2540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2538_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
v___x_2541_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2415_, v___x_2540_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_dec_ref(v___x_2541_);
goto v___jp_2432_;
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2541_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2541_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
lean_dec(v_cls_2415_);
lean_dec_ref(v_lhs_2411_);
v_a_2550_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___x_2535_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2535_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
v___jp_2426_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
return v___x_2428_;
}
v___jp_2429_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
return v___x_2431_;
}
v___jp_2432_:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
return v___x_2434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__8___boxed(lean_object* v_lhs_2558_, lean_object* v_rhs_2559_, lean_object* v_P_2560_, lean_object* v___x_2561_, lean_object* v_cls_2562_, lean_object* v___f_2563_, lean_object* v_____r_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
uint8_t v___x_119277__boxed_2573_; lean_object* v_res_2574_; 
v___x_119277__boxed_2573_ = lean_unbox(v___x_2561_);
v_res_2574_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__8(v_lhs_2558_, v_rhs_2559_, v_P_2560_, v___x_119277__boxed_2573_, v_cls_2562_, v___f_2563_, v_____r_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg(lean_object* v_x_2575_){
_start:
{
if (lean_obj_tag(v_x_2575_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
v_a_2577_ = lean_ctor_get(v_x_2575_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v_x_2575_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v_x_2575_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v_x_2575_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
lean_ctor_set_tag(v___x_2579_, 1);
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
v_a_2585_ = lean_ctor_get(v_x_2575_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v_x_2575_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v_x_2575_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v_x_2575_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
lean_ctor_set_tag(v___x_2587_, 0);
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg___boxed(lean_object* v_x_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg(v_x_2593_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4_spec__5(size_t v_sz_2596_, size_t v_i_2597_, lean_object* v_bs_2598_){
_start:
{
uint8_t v___x_2599_; 
v___x_2599_ = lean_usize_dec_lt(v_i_2597_, v_sz_2596_);
if (v___x_2599_ == 0)
{
return v_bs_2598_;
}
else
{
lean_object* v_v_2600_; lean_object* v_msg_2601_; lean_object* v___x_2602_; lean_object* v_bs_x27_2603_; size_t v___x_2604_; size_t v___x_2605_; lean_object* v___x_2606_; 
v_v_2600_ = lean_array_uget_borrowed(v_bs_2598_, v_i_2597_);
v_msg_2601_ = lean_ctor_get(v_v_2600_, 1);
lean_inc_ref(v_msg_2601_);
v___x_2602_ = lean_unsigned_to_nat(0u);
v_bs_x27_2603_ = lean_array_uset(v_bs_2598_, v_i_2597_, v___x_2602_);
v___x_2604_ = ((size_t)1ULL);
v___x_2605_ = lean_usize_add(v_i_2597_, v___x_2604_);
v___x_2606_ = lean_array_uset(v_bs_x27_2603_, v_i_2597_, v_msg_2601_);
v_i_2597_ = v___x_2605_;
v_bs_2598_ = v___x_2606_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_2608_, lean_object* v_i_2609_, lean_object* v_bs_2610_){
_start:
{
size_t v_sz_boxed_2611_; size_t v_i_boxed_2612_; lean_object* v_res_2613_; 
v_sz_boxed_2611_ = lean_unbox_usize(v_sz_2608_);
lean_dec(v_sz_2608_);
v_i_boxed_2612_ = lean_unbox_usize(v_i_2609_);
lean_dec(v_i_2609_);
v_res_2613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4_spec__5(v_sz_boxed_2611_, v_i_boxed_2612_, v_bs_2610_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(lean_object* v_oldTraces_2614_, lean_object* v_data_2615_, lean_object* v_ref_2616_, lean_object* v_msg_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_fileName_2623_; lean_object* v_fileMap_2624_; lean_object* v_options_2625_; lean_object* v_currRecDepth_2626_; lean_object* v_maxRecDepth_2627_; lean_object* v_ref_2628_; lean_object* v_currNamespace_2629_; lean_object* v_openDecls_2630_; lean_object* v_initHeartbeats_2631_; lean_object* v_maxHeartbeats_2632_; lean_object* v_quotContext_2633_; lean_object* v_currMacroScope_2634_; uint8_t v_diag_2635_; lean_object* v_cancelTk_x3f_2636_; uint8_t v_suppressElabErrors_2637_; lean_object* v_inheritedTraceOptions_2638_; lean_object* v___x_2639_; lean_object* v_traceState_2640_; lean_object* v_traces_2641_; lean_object* v_ref_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; size_t v_sz_2645_; size_t v___x_2646_; lean_object* v___x_2647_; lean_object* v_msg_2648_; lean_object* v___x_2649_; lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2688_; 
v_fileName_2623_ = lean_ctor_get(v___y_2620_, 0);
v_fileMap_2624_ = lean_ctor_get(v___y_2620_, 1);
v_options_2625_ = lean_ctor_get(v___y_2620_, 2);
v_currRecDepth_2626_ = lean_ctor_get(v___y_2620_, 3);
v_maxRecDepth_2627_ = lean_ctor_get(v___y_2620_, 4);
v_ref_2628_ = lean_ctor_get(v___y_2620_, 5);
v_currNamespace_2629_ = lean_ctor_get(v___y_2620_, 6);
v_openDecls_2630_ = lean_ctor_get(v___y_2620_, 7);
v_initHeartbeats_2631_ = lean_ctor_get(v___y_2620_, 8);
v_maxHeartbeats_2632_ = lean_ctor_get(v___y_2620_, 9);
v_quotContext_2633_ = lean_ctor_get(v___y_2620_, 10);
v_currMacroScope_2634_ = lean_ctor_get(v___y_2620_, 11);
v_diag_2635_ = lean_ctor_get_uint8(v___y_2620_, sizeof(void*)*14);
v_cancelTk_x3f_2636_ = lean_ctor_get(v___y_2620_, 12);
v_suppressElabErrors_2637_ = lean_ctor_get_uint8(v___y_2620_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2638_ = lean_ctor_get(v___y_2620_, 13);
v___x_2639_ = lean_st_ref_get(v___y_2621_);
v_traceState_2640_ = lean_ctor_get(v___x_2639_, 4);
lean_inc_ref(v_traceState_2640_);
lean_dec(v___x_2639_);
v_traces_2641_ = lean_ctor_get(v_traceState_2640_, 0);
lean_inc_ref(v_traces_2641_);
lean_dec_ref(v_traceState_2640_);
v_ref_2642_ = l_Lean_replaceRef(v_ref_2616_, v_ref_2628_);
lean_inc_ref(v_inheritedTraceOptions_2638_);
lean_inc(v_cancelTk_x3f_2636_);
lean_inc(v_currMacroScope_2634_);
lean_inc(v_quotContext_2633_);
lean_inc(v_maxHeartbeats_2632_);
lean_inc(v_initHeartbeats_2631_);
lean_inc(v_openDecls_2630_);
lean_inc(v_currNamespace_2629_);
lean_inc(v_maxRecDepth_2627_);
lean_inc(v_currRecDepth_2626_);
lean_inc_ref(v_options_2625_);
lean_inc_ref(v_fileMap_2624_);
lean_inc_ref(v_fileName_2623_);
v___x_2643_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2643_, 0, v_fileName_2623_);
lean_ctor_set(v___x_2643_, 1, v_fileMap_2624_);
lean_ctor_set(v___x_2643_, 2, v_options_2625_);
lean_ctor_set(v___x_2643_, 3, v_currRecDepth_2626_);
lean_ctor_set(v___x_2643_, 4, v_maxRecDepth_2627_);
lean_ctor_set(v___x_2643_, 5, v_ref_2642_);
lean_ctor_set(v___x_2643_, 6, v_currNamespace_2629_);
lean_ctor_set(v___x_2643_, 7, v_openDecls_2630_);
lean_ctor_set(v___x_2643_, 8, v_initHeartbeats_2631_);
lean_ctor_set(v___x_2643_, 9, v_maxHeartbeats_2632_);
lean_ctor_set(v___x_2643_, 10, v_quotContext_2633_);
lean_ctor_set(v___x_2643_, 11, v_currMacroScope_2634_);
lean_ctor_set(v___x_2643_, 12, v_cancelTk_x3f_2636_);
lean_ctor_set(v___x_2643_, 13, v_inheritedTraceOptions_2638_);
lean_ctor_set_uint8(v___x_2643_, sizeof(void*)*14, v_diag_2635_);
lean_ctor_set_uint8(v___x_2643_, sizeof(void*)*14 + 1, v_suppressElabErrors_2637_);
v___x_2644_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2641_);
lean_dec_ref(v_traces_2641_);
v_sz_2645_ = lean_array_size(v___x_2644_);
v___x_2646_ = ((size_t)0ULL);
v___x_2647_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4_spec__5(v_sz_2645_, v___x_2646_, v___x_2644_);
v_msg_2648_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2648_, 0, v_data_2615_);
lean_ctor_set(v_msg_2648_, 1, v_msg_2617_);
lean_ctor_set(v_msg_2648_, 2, v___x_2647_);
v___x_2649_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2648_, v___y_2618_, v___y_2619_, v___x_2643_, v___y_2621_);
lean_dec_ref(v___x_2643_);
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2652_ = v___x_2649_;
v_isShared_2653_ = v_isSharedCheck_2688_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2649_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2688_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2654_; lean_object* v_traceState_2655_; lean_object* v_env_2656_; lean_object* v_nextMacroScope_2657_; lean_object* v_ngen_2658_; lean_object* v_auxDeclNGen_2659_; lean_object* v_cache_2660_; lean_object* v_messages_2661_; lean_object* v_infoState_2662_; lean_object* v_snapshotTasks_2663_; lean_object* v_newDecls_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2687_; 
v___x_2654_ = lean_st_ref_take(v___y_2621_);
v_traceState_2655_ = lean_ctor_get(v___x_2654_, 4);
v_env_2656_ = lean_ctor_get(v___x_2654_, 0);
v_nextMacroScope_2657_ = lean_ctor_get(v___x_2654_, 1);
v_ngen_2658_ = lean_ctor_get(v___x_2654_, 2);
v_auxDeclNGen_2659_ = lean_ctor_get(v___x_2654_, 3);
v_cache_2660_ = lean_ctor_get(v___x_2654_, 5);
v_messages_2661_ = lean_ctor_get(v___x_2654_, 6);
v_infoState_2662_ = lean_ctor_get(v___x_2654_, 7);
v_snapshotTasks_2663_ = lean_ctor_get(v___x_2654_, 8);
v_newDecls_2664_ = lean_ctor_get(v___x_2654_, 9);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2666_ = v___x_2654_;
v_isShared_2667_ = v_isSharedCheck_2687_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_newDecls_2664_);
lean_inc(v_snapshotTasks_2663_);
lean_inc(v_infoState_2662_);
lean_inc(v_messages_2661_);
lean_inc(v_cache_2660_);
lean_inc(v_traceState_2655_);
lean_inc(v_auxDeclNGen_2659_);
lean_inc(v_ngen_2658_);
lean_inc(v_nextMacroScope_2657_);
lean_inc(v_env_2656_);
lean_dec(v___x_2654_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2687_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
uint64_t v_tid_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2685_; 
v_tid_2668_ = lean_ctor_get_uint64(v_traceState_2655_, sizeof(void*)*1);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_traceState_2655_);
if (v_isSharedCheck_2685_ == 0)
{
lean_object* v_unused_2686_; 
v_unused_2686_ = lean_ctor_get(v_traceState_2655_, 0);
lean_dec(v_unused_2686_);
v___x_2670_ = v_traceState_2655_;
v_isShared_2671_ = v_isSharedCheck_2685_;
goto v_resetjp_2669_;
}
else
{
lean_dec(v_traceState_2655_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2685_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2672_, 0, v_ref_2616_);
lean_ctor_set(v___x_2672_, 1, v_a_2650_);
v___x_2673_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2614_, v___x_2672_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v___x_2673_);
v___x_2675_ = v___x_2670_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2673_);
lean_ctor_set_uint64(v_reuseFailAlloc_2684_, sizeof(void*)*1, v_tid_2668_);
v___x_2675_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
lean_object* v___x_2677_; 
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 4, v___x_2675_);
v___x_2677_ = v___x_2666_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_env_2656_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v_nextMacroScope_2657_);
lean_ctor_set(v_reuseFailAlloc_2683_, 2, v_ngen_2658_);
lean_ctor_set(v_reuseFailAlloc_2683_, 3, v_auxDeclNGen_2659_);
lean_ctor_set(v_reuseFailAlloc_2683_, 4, v___x_2675_);
lean_ctor_set(v_reuseFailAlloc_2683_, 5, v_cache_2660_);
lean_ctor_set(v_reuseFailAlloc_2683_, 6, v_messages_2661_);
lean_ctor_set(v_reuseFailAlloc_2683_, 7, v_infoState_2662_);
lean_ctor_set(v_reuseFailAlloc_2683_, 8, v_snapshotTasks_2663_);
lean_ctor_set(v_reuseFailAlloc_2683_, 9, v_newDecls_2664_);
v___x_2677_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2681_; 
v___x_2678_ = lean_st_ref_set(v___y_2621_, v___x_2677_);
v___x_2679_ = lean_box(0);
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 0, v___x_2679_);
v___x_2681_ = v___x_2652_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg___boxed(lean_object* v_oldTraces_2689_, lean_object* v_data_2690_, lean_object* v_ref_2691_, lean_object* v_msg_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_oldTraces_2689_, v_data_2690_, v_ref_2691_, v_msg_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__6(lean_object* v_opts_2699_, lean_object* v_opt_2700_){
_start:
{
lean_object* v_name_2701_; lean_object* v_defValue_2702_; lean_object* v_map_2703_; lean_object* v___x_2704_; 
v_name_2701_ = lean_ctor_get(v_opt_2700_, 0);
v_defValue_2702_ = lean_ctor_get(v_opt_2700_, 1);
v_map_2703_ = lean_ctor_get(v_opts_2699_, 0);
v___x_2704_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2703_, v_name_2701_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_inc(v_defValue_2702_);
return v_defValue_2702_;
}
else
{
lean_object* v_val_2705_; 
v_val_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_val_2705_);
lean_dec_ref(v___x_2704_);
if (lean_obj_tag(v_val_2705_) == 3)
{
lean_object* v_v_2706_; 
v_v_2706_ = lean_ctor_get(v_val_2705_, 0);
lean_inc(v_v_2706_);
lean_dec_ref(v_val_2705_);
return v_v_2706_;
}
else
{
lean_dec(v_val_2705_);
lean_inc(v_defValue_2702_);
return v_defValue_2702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__6___boxed(lean_object* v_opts_2707_, lean_object* v_opt_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2707_, v_opt_2708_);
lean_dec_ref(v_opt_2708_);
lean_dec_ref(v_opts_2707_);
return v_res_2709_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__3(lean_object* v_e_2710_){
_start:
{
if (lean_obj_tag(v_e_2710_) == 0)
{
uint8_t v___x_2711_; 
v___x_2711_ = 2;
return v___x_2711_;
}
else
{
uint8_t v___x_2712_; 
v___x_2712_ = 0;
return v___x_2712_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__3___boxed(lean_object* v_e_2713_){
_start:
{
uint8_t v_res_2714_; lean_object* v_r_2715_; 
v_res_2714_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__3(v_e_2713_);
lean_dec_ref(v_e_2713_);
v_r_2715_ = lean_box(v_res_2714_);
return v_r_2715_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__0));
v___x_2718_ = l_Lean_stringToMessageData(v___x_2717_);
return v___x_2718_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2719_; double v___x_2720_; 
v___x_2719_ = lean_unsigned_to_nat(1000u);
v___x_2720_ = lean_float_of_nat(v___x_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(lean_object* v_cls_2721_, uint8_t v_collapsed_2722_, lean_object* v_tag_2723_, lean_object* v_opts_2724_, uint8_t v_clsEnabled_2725_, lean_object* v_oldTraces_2726_, lean_object* v_msg_2727_, lean_object* v_resStartStop_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_fst_2737_; lean_object* v_snd_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2837_; 
v_fst_2737_ = lean_ctor_get(v_resStartStop_2728_, 0);
v_snd_2738_ = lean_ctor_get(v_resStartStop_2728_, 1);
v_isSharedCheck_2837_ = !lean_is_exclusive(v_resStartStop_2728_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2740_ = v_resStartStop_2728_;
v_isShared_2741_ = v_isSharedCheck_2837_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_snd_2738_);
lean_inc(v_fst_2737_);
lean_dec(v_resStartStop_2728_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2837_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v_data_2745_; lean_object* v_fst_2756_; lean_object* v_snd_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2836_; 
v_fst_2756_ = lean_ctor_get(v_snd_2738_, 0);
v_snd_2757_ = lean_ctor_get(v_snd_2738_, 1);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_snd_2738_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2759_ = v_snd_2738_;
v_isShared_2760_ = v_isSharedCheck_2836_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_snd_2757_);
lean_inc(v_fst_2756_);
lean_dec(v_snd_2738_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2836_;
goto v_resetjp_2758_;
}
v___jp_2742_:
{
lean_object* v___x_2746_; 
lean_inc(v___y_2744_);
v___x_2746_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_oldTraces_2726_, v_data_2745_, v___y_2744_, v___y_2743_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v___x_2747_; 
lean_dec_ref(v___x_2746_);
v___x_2747_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg(v_fst_2737_);
return v___x_2747_;
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
lean_dec(v_fst_2737_);
v_a_2748_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2746_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2746_);
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
v_resetjp_2758_:
{
lean_object* v___x_2761_; uint8_t v___x_2762_; lean_object* v___y_2764_; lean_object* v_a_2765_; uint8_t v___y_2789_; double v___y_2821_; 
v___x_2761_ = l_Lean_trace_profiler;
v___x_2762_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(v_opts_2724_, v___x_2761_);
if (v___x_2762_ == 0)
{
v___y_2789_ = v___x_2762_;
goto v___jp_2788_;
}
else
{
lean_object* v___x_2826_; uint8_t v___x_2827_; 
v___x_2826_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2827_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(v_opts_2724_, v___x_2826_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; lean_object* v___x_2829_; double v___x_2830_; double v___x_2831_; double v___x_2832_; 
v___x_2828_ = l_Lean_trace_profiler_threshold;
v___x_2829_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2724_, v___x_2828_);
v___x_2830_ = lean_float_of_nat(v___x_2829_);
v___x_2831_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__2);
v___x_2832_ = lean_float_div(v___x_2830_, v___x_2831_);
v___y_2821_ = v___x_2832_;
goto v___jp_2820_;
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; double v___x_2835_; 
v___x_2833_ = l_Lean_trace_profiler_threshold;
v___x_2834_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2724_, v___x_2833_);
v___x_2835_ = lean_float_of_nat(v___x_2834_);
v___y_2821_ = v___x_2835_;
goto v___jp_2820_;
}
}
v___jp_2763_:
{
uint8_t v_result_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2771_; 
v_result_2766_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__3(v_fst_2737_);
v___x_2767_ = l_Lean_TraceResult_toEmoji(v_result_2766_);
v___x_2768_ = l_Lean_stringToMessageData(v___x_2767_);
v___x_2769_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10);
if (v_isShared_2760_ == 0)
{
lean_ctor_set_tag(v___x_2759_, 7);
lean_ctor_set(v___x_2759_, 1, v___x_2769_);
lean_ctor_set(v___x_2759_, 0, v___x_2768_);
v___x_2771_ = v___x_2759_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2768_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v___x_2769_);
v___x_2771_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
lean_object* v_m_2773_; 
if (v_isShared_2741_ == 0)
{
lean_ctor_set_tag(v___x_2740_, 7);
lean_ctor_set(v___x_2740_, 1, v_a_2765_);
lean_ctor_set(v___x_2740_, 0, v___x_2771_);
v_m_2773_ = v___x_2740_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v_a_2765_);
v_m_2773_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; double v___x_2776_; lean_object* v_data_2777_; 
v___x_2774_ = lean_box(v_result_2766_);
v___x_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
v___x_2776_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0);
lean_inc_ref(v_tag_2723_);
lean_inc_ref(v___x_2775_);
lean_inc(v_cls_2721_);
v_data_2777_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2777_, 0, v_cls_2721_);
lean_ctor_set(v_data_2777_, 1, v___x_2775_);
lean_ctor_set(v_data_2777_, 2, v_tag_2723_);
lean_ctor_set_float(v_data_2777_, sizeof(void*)*3, v___x_2776_);
lean_ctor_set_float(v_data_2777_, sizeof(void*)*3 + 8, v___x_2776_);
lean_ctor_set_uint8(v_data_2777_, sizeof(void*)*3 + 16, v_collapsed_2722_);
if (v___x_2762_ == 0)
{
lean_dec_ref(v___x_2775_);
lean_dec(v_snd_2757_);
lean_dec(v_fst_2756_);
lean_dec_ref(v_tag_2723_);
lean_dec(v_cls_2721_);
v___y_2743_ = v_m_2773_;
v___y_2744_ = v___y_2764_;
v_data_2745_ = v_data_2777_;
goto v___jp_2742_;
}
else
{
lean_object* v_data_2778_; double v___x_2779_; double v___x_2780_; 
lean_dec_ref(v_data_2777_);
v_data_2778_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2778_, 0, v_cls_2721_);
lean_ctor_set(v_data_2778_, 1, v___x_2775_);
lean_ctor_set(v_data_2778_, 2, v_tag_2723_);
v___x_2779_ = lean_unbox_float(v_fst_2756_);
lean_dec(v_fst_2756_);
lean_ctor_set_float(v_data_2778_, sizeof(void*)*3, v___x_2779_);
v___x_2780_ = lean_unbox_float(v_snd_2757_);
lean_dec(v_snd_2757_);
lean_ctor_set_float(v_data_2778_, sizeof(void*)*3 + 8, v___x_2780_);
lean_ctor_set_uint8(v_data_2778_, sizeof(void*)*3 + 16, v_collapsed_2722_);
v___y_2743_ = v_m_2773_;
v___y_2744_ = v___y_2764_;
v_data_2745_ = v_data_2778_;
goto v___jp_2742_;
}
}
}
}
v___jp_2783_:
{
lean_object* v_ref_2784_; lean_object* v___x_2785_; 
v_ref_2784_ = lean_ctor_get(v___y_2734_, 5);
lean_inc(v___y_2735_);
lean_inc_ref(v___y_2734_);
lean_inc(v___y_2733_);
lean_inc_ref(v___y_2732_);
lean_inc(v___y_2731_);
lean_inc_ref(v___y_2730_);
lean_inc(v___y_2729_);
lean_inc(v_fst_2737_);
v___x_2785_ = lean_apply_9(v_msg_2727_, v_fst_2737_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, lean_box(0));
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2786_);
lean_dec_ref(v___x_2785_);
v___y_2764_ = v_ref_2784_;
v_a_2765_ = v_a_2786_;
goto v___jp_2763_;
}
else
{
lean_object* v___x_2787_; 
lean_dec_ref(v___x_2785_);
v___x_2787_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__1);
v___y_2764_ = v_ref_2784_;
v_a_2765_ = v___x_2787_;
goto v___jp_2763_;
}
}
v___jp_2788_:
{
if (v_clsEnabled_2725_ == 0)
{
if (v___y_2789_ == 0)
{
lean_object* v___x_2790_; lean_object* v_traceState_2791_; lean_object* v_env_2792_; lean_object* v_nextMacroScope_2793_; lean_object* v_ngen_2794_; lean_object* v_auxDeclNGen_2795_; lean_object* v_cache_2796_; lean_object* v_messages_2797_; lean_object* v_infoState_2798_; lean_object* v_snapshotTasks_2799_; lean_object* v_newDecls_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2819_; 
lean_del_object(v___x_2759_);
lean_dec(v_snd_2757_);
lean_dec(v_fst_2756_);
lean_del_object(v___x_2740_);
lean_dec_ref(v_msg_2727_);
lean_dec_ref(v_tag_2723_);
lean_dec(v_cls_2721_);
v___x_2790_ = lean_st_ref_take(v___y_2735_);
v_traceState_2791_ = lean_ctor_get(v___x_2790_, 4);
v_env_2792_ = lean_ctor_get(v___x_2790_, 0);
v_nextMacroScope_2793_ = lean_ctor_get(v___x_2790_, 1);
v_ngen_2794_ = lean_ctor_get(v___x_2790_, 2);
v_auxDeclNGen_2795_ = lean_ctor_get(v___x_2790_, 3);
v_cache_2796_ = lean_ctor_get(v___x_2790_, 5);
v_messages_2797_ = lean_ctor_get(v___x_2790_, 6);
v_infoState_2798_ = lean_ctor_get(v___x_2790_, 7);
v_snapshotTasks_2799_ = lean_ctor_get(v___x_2790_, 8);
v_newDecls_2800_ = lean_ctor_get(v___x_2790_, 9);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2802_ = v___x_2790_;
v_isShared_2803_ = v_isSharedCheck_2819_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_newDecls_2800_);
lean_inc(v_snapshotTasks_2799_);
lean_inc(v_infoState_2798_);
lean_inc(v_messages_2797_);
lean_inc(v_cache_2796_);
lean_inc(v_traceState_2791_);
lean_inc(v_auxDeclNGen_2795_);
lean_inc(v_ngen_2794_);
lean_inc(v_nextMacroScope_2793_);
lean_inc(v_env_2792_);
lean_dec(v___x_2790_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2819_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
uint64_t v_tid_2804_; lean_object* v_traces_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2818_; 
v_tid_2804_ = lean_ctor_get_uint64(v_traceState_2791_, sizeof(void*)*1);
v_traces_2805_ = lean_ctor_get(v_traceState_2791_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v_traceState_2791_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2807_ = v_traceState_2791_;
v_isShared_2808_ = v_isSharedCheck_2818_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_traces_2805_);
lean_dec(v_traceState_2791_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2818_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2809_; lean_object* v___x_2811_; 
v___x_2809_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2726_, v_traces_2805_);
lean_dec_ref(v_traces_2805_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v___x_2809_);
v___x_2811_ = v___x_2807_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2809_);
lean_ctor_set_uint64(v_reuseFailAlloc_2817_, sizeof(void*)*1, v_tid_2804_);
v___x_2811_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
lean_object* v___x_2813_; 
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 4, v___x_2811_);
v___x_2813_ = v___x_2802_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_env_2792_);
lean_ctor_set(v_reuseFailAlloc_2816_, 1, v_nextMacroScope_2793_);
lean_ctor_set(v_reuseFailAlloc_2816_, 2, v_ngen_2794_);
lean_ctor_set(v_reuseFailAlloc_2816_, 3, v_auxDeclNGen_2795_);
lean_ctor_set(v_reuseFailAlloc_2816_, 4, v___x_2811_);
lean_ctor_set(v_reuseFailAlloc_2816_, 5, v_cache_2796_);
lean_ctor_set(v_reuseFailAlloc_2816_, 6, v_messages_2797_);
lean_ctor_set(v_reuseFailAlloc_2816_, 7, v_infoState_2798_);
lean_ctor_set(v_reuseFailAlloc_2816_, 8, v_snapshotTasks_2799_);
lean_ctor_set(v_reuseFailAlloc_2816_, 9, v_newDecls_2800_);
v___x_2813_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = lean_st_ref_set(v___y_2735_, v___x_2813_);
v___x_2815_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg(v_fst_2737_);
return v___x_2815_;
}
}
}
}
}
else
{
goto v___jp_2783_;
}
}
else
{
goto v___jp_2783_;
}
}
v___jp_2820_:
{
double v___x_2822_; double v___x_2823_; double v___x_2824_; uint8_t v___x_2825_; 
v___x_2822_ = lean_unbox_float(v_snd_2757_);
v___x_2823_ = lean_unbox_float(v_fst_2756_);
v___x_2824_ = lean_float_sub(v___x_2822_, v___x_2823_);
v___x_2825_ = lean_float_decLt(v___y_2821_, v___x_2824_);
v___y_2789_ = v___x_2825_;
goto v___jp_2788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___boxed(lean_object* v_cls_2838_, lean_object* v_collapsed_2839_, lean_object* v_tag_2840_, lean_object* v_opts_2841_, lean_object* v_clsEnabled_2842_, lean_object* v_oldTraces_2843_, lean_object* v_msg_2844_, lean_object* v_resStartStop_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
uint8_t v_collapsed_boxed_2854_; uint8_t v_clsEnabled_boxed_2855_; lean_object* v_res_2856_; 
v_collapsed_boxed_2854_ = lean_unbox(v_collapsed_2839_);
v_clsEnabled_boxed_2855_ = lean_unbox(v_clsEnabled_2842_);
v_res_2856_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(v_cls_2838_, v_collapsed_boxed_2854_, v_tag_2840_, v_opts_2841_, v_clsEnabled_boxed_2855_, v_oldTraces_2843_, v_msg_2844_, v_resStartStop_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v_opts_2841_);
return v_res_2856_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2(void){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1));
v___x_2861_ = l_Lean_stringToMessageData(v___x_2860_);
return v___x_2861_;
}
}
static double _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__4(void){
_start:
{
lean_object* v___x_2863_; double v___x_2864_; 
v___x_2863_ = lean_unsigned_to_nat(1000000000u);
v___x_2864_ = lean_float_of_nat(v___x_2863_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing(lean_object* v_P_2865_, lean_object* v_lhs_2866_, lean_object* v_rhs_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v_options_2896_; lean_object* v_inheritedTraceOptions_2897_; uint8_t v_hasTrace_2898_; lean_object* v_cls_2899_; lean_object* v___f_2900_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; uint8_t v_____do__lift_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; 
v_options_2896_ = lean_ctor_get(v_a_2873_, 2);
v_inheritedTraceOptions_2897_ = lean_ctor_get(v_a_2873_, 13);
v_hasTrace_2898_ = lean_ctor_get_uint8(v_options_2896_, sizeof(void*)*1);
v_cls_2899_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___f_2900_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__0));
if (v_hasTrace_2898_ == 0)
{
lean_object* v___x_3019_; lean_object* v_a_3020_; uint8_t v___x_3021_; 
v___x_3019_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2899_, v_inheritedTraceOptions_2897_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref(v___x_3019_);
v___x_3021_ = lean_unbox(v_a_3020_);
lean_dec(v_a_3020_);
v_____do__lift_2998_ = v___x_3021_;
v___y_2999_ = v_a_2868_;
v___y_3000_ = v_a_2869_;
v___y_3001_ = v_a_2870_;
v___y_3002_ = v_a_2871_;
v___y_3003_ = v_a_2872_;
v___y_3004_ = v_a_2873_;
v___y_3005_ = v_a_2874_;
goto v___jp_2997_;
}
else
{
lean_object* v___f_3022_; uint8_t v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; uint8_t v___x_3026_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v_a_3030_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v_a_3042_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v_a_3060_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v_a_3075_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; 
v___f_3022_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__3));
v___x_3023_ = 0;
v___x_3024_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1));
v___x_3025_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3026_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2897_, v_options_2896_, v___x_3025_);
if (v___x_3026_ == 0)
{
lean_object* v___x_3123_; uint8_t v___x_3124_; 
v___x_3123_ = l_Lean_trace_profiler;
v___x_3124_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(v_options_2896_, v___x_3123_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3125_; lean_object* v_a_3126_; uint8_t v___x_3127_; 
v___x_3125_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2899_, v_inheritedTraceOptions_2897_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_a_3126_);
lean_dec_ref(v___x_3125_);
v___x_3127_ = lean_unbox(v_a_3126_);
lean_dec(v_a_3126_);
v_____do__lift_2998_ = v___x_3127_;
v___y_2999_ = v_a_2868_;
v___y_3000_ = v_a_2869_;
v___y_3001_ = v_a_2870_;
v___y_3002_ = v_a_2871_;
v___y_3003_ = v_a_2872_;
v___y_3004_ = v_a_2873_;
v___y_3005_ = v_a_2874_;
goto v___jp_2997_;
}
else
{
goto v___jp_3090_;
}
}
else
{
goto v___jp_3090_;
}
v___jp_3027_:
{
lean_object* v___x_3031_; double v___x_3032_; double v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3031_ = lean_io_get_num_heartbeats();
v___x_3032_ = lean_float_of_nat(v___y_3028_);
v___x_3033_ = lean_float_of_nat(v___x_3031_);
v___x_3034_ = lean_box_float(v___x_3032_);
v___x_3035_ = lean_box_float(v___x_3033_);
v___x_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3034_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
v___x_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3037_, 0, v_a_3030_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
v___x_3038_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(v_cls_2899_, v___x_3023_, v___x_3024_, v_options_2896_, v___x_3026_, v___y_3029_, v___f_3022_, v___x_3037_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
return v___x_3038_;
}
v___jp_3039_:
{
lean_object* v___x_3043_; 
v___x_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3043_, 0, v_a_3042_);
v___y_3028_ = v___y_3040_;
v___y_3029_ = v___y_3041_;
v_a_3030_ = v___x_3043_;
goto v___jp_3027_;
}
v___jp_3044_:
{
if (lean_obj_tag(v___y_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
v_a_3048_ = lean_ctor_get(v___y_3047_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___y_3047_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___y_3047_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___y_3047_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
lean_ctor_set_tag(v___x_3050_, 1);
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
v___y_3028_ = v___y_3045_;
v___y_3029_ = v___y_3046_;
v_a_3030_ = v___x_3053_;
goto v___jp_3027_;
}
}
}
else
{
lean_object* v_a_3056_; 
v_a_3056_ = lean_ctor_get(v___y_3047_, 0);
lean_inc(v_a_3056_);
lean_dec_ref(v___y_3047_);
v___y_3040_ = v___y_3045_;
v___y_3041_ = v___y_3046_;
v_a_3042_ = v_a_3056_;
goto v___jp_3039_;
}
}
v___jp_3057_:
{
lean_object* v___x_3061_; double v___x_3062_; double v___x_3063_; double v___x_3064_; double v___x_3065_; double v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3061_ = lean_io_mono_nanos_now();
v___x_3062_ = lean_float_of_nat(v___y_3058_);
v___x_3063_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__4);
v___x_3064_ = lean_float_div(v___x_3062_, v___x_3063_);
v___x_3065_ = lean_float_of_nat(v___x_3061_);
v___x_3066_ = lean_float_div(v___x_3065_, v___x_3063_);
v___x_3067_ = lean_box_float(v___x_3064_);
v___x_3068_ = lean_box_float(v___x_3066_);
v___x_3069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3067_);
lean_ctor_set(v___x_3069_, 1, v___x_3068_);
v___x_3070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3070_, 0, v_a_3060_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(v_cls_2899_, v___x_3023_, v___x_3024_, v_options_2896_, v___x_3026_, v___y_3059_, v___f_3022_, v___x_3070_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
return v___x_3071_;
}
v___jp_3072_:
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3076_, 0, v_a_3075_);
v___y_3058_ = v___y_3073_;
v___y_3059_ = v___y_3074_;
v_a_3060_ = v___x_3076_;
goto v___jp_3057_;
}
v___jp_3077_:
{
if (lean_obj_tag(v___y_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
v_a_3081_ = lean_ctor_get(v___y_3080_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___y_3080_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___y_3080_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___y_3080_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
lean_ctor_set_tag(v___x_3083_, 1);
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
v___y_3058_ = v___y_3078_;
v___y_3059_ = v___y_3079_;
v_a_3060_ = v___x_3086_;
goto v___jp_3057_;
}
}
}
else
{
lean_object* v_a_3089_; 
v_a_3089_ = lean_ctor_get(v___y_3080_, 0);
lean_inc(v_a_3089_);
lean_dec_ref(v___y_3080_);
v___y_3073_ = v___y_3078_;
v___y_3074_ = v___y_3079_;
v_a_3075_ = v_a_3089_;
goto v___jp_3072_;
}
}
v___jp_3090_:
{
lean_object* v___x_3091_; lean_object* v_a_3092_; lean_object* v___x_3093_; uint8_t v___x_3094_; 
v___x_3091_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v_a_2874_);
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc(v_a_3092_);
lean_dec_ref(v___x_3091_);
v___x_3093_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3094_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(v_options_2896_, v___x_3093_);
if (v___x_3094_ == 0)
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v_a_3097_; uint8_t v___x_3098_; 
v___x_3095_ = lean_io_mono_nanos_now();
v___x_3096_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2899_, v_inheritedTraceOptions_2897_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_a_3097_);
lean_dec_ref(v___x_3096_);
v___x_3098_ = lean_unbox(v_a_3097_);
lean_dec(v_a_3097_);
if (v___x_3098_ == 0)
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = lean_box(0);
v___x_3100_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2866_, v_rhs_2867_, v___f_2900_, v_cls_2899_, v___x_3094_, v_P_2865_, v_hasTrace_2898_, v___x_3099_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
v___y_3078_ = v___x_3095_;
v___y_3079_ = v_a_3092_;
v___y_3080_ = v___x_3100_;
goto v___jp_3077_;
}
else
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3101_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2867_);
lean_inc_ref(v_lhs_2866_);
lean_inc_ref(v_P_2865_);
v___x_3102_ = l_Lean_mkAppB(v_P_2865_, v_lhs_2866_, v_rhs_2867_);
v___x_3103_ = l_Lean_indentExpr(v___x_3102_);
v___x_3104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3101_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
v___x_3105_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2899_, v___x_3104_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; lean_object* v___x_3107_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3106_);
lean_dec_ref(v___x_3105_);
v___x_3107_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2866_, v_rhs_2867_, v___f_2900_, v_cls_2899_, v___x_3094_, v_P_2865_, v_hasTrace_2898_, v_a_3106_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
v___y_3078_ = v___x_3095_;
v___y_3079_ = v_a_3092_;
v___y_3080_ = v___x_3107_;
goto v___jp_3077_;
}
else
{
lean_object* v_a_3108_; 
lean_dec_ref(v_rhs_2867_);
lean_dec_ref(v_lhs_2866_);
lean_dec_ref(v_P_2865_);
v_a_3108_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3108_);
lean_dec_ref(v___x_3105_);
v___y_3073_ = v___x_3095_;
v___y_3074_ = v_a_3092_;
v_a_3075_ = v_a_3108_;
goto v___jp_3072_;
}
}
}
else
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v_a_3111_; uint8_t v___x_3112_; 
v___x_3109_ = lean_io_get_num_heartbeats();
v___x_3110_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2899_, v_inheritedTraceOptions_2897_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_a_3111_);
lean_dec_ref(v___x_3110_);
v___x_3112_ = lean_unbox(v_a_3111_);
lean_dec(v_a_3111_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = lean_box(0);
v___x_3114_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__8(v_lhs_2866_, v_rhs_2867_, v_P_2865_, v___x_3094_, v_cls_2899_, v___f_2900_, v___x_3113_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
v___y_3045_ = v___x_3109_;
v___y_3046_ = v_a_3092_;
v___y_3047_ = v___x_3114_;
goto v___jp_3044_;
}
else
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3115_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2867_);
lean_inc_ref(v_lhs_2866_);
lean_inc_ref(v_P_2865_);
v___x_3116_ = l_Lean_mkAppB(v_P_2865_, v_lhs_2866_, v_rhs_2867_);
v___x_3117_ = l_Lean_indentExpr(v___x_3116_);
v___x_3118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3115_);
lean_ctor_set(v___x_3118_, 1, v___x_3117_);
v___x_3119_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2899_, v___x_3118_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v___x_3121_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3120_);
lean_dec_ref(v___x_3119_);
v___x_3121_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__8(v_lhs_2866_, v_rhs_2867_, v_P_2865_, v___x_3094_, v_cls_2899_, v___f_2900_, v_a_3120_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
v___y_3045_ = v___x_3109_;
v___y_3046_ = v_a_3092_;
v___y_3047_ = v___x_3121_;
goto v___jp_3044_;
}
else
{
lean_object* v_a_3122_; 
lean_dec_ref(v_rhs_2867_);
lean_dec_ref(v_lhs_2866_);
lean_dec_ref(v_P_2865_);
v_a_3122_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3122_);
lean_dec_ref(v___x_3119_);
v___y_3040_ = v___x_3109_;
v___y_3041_ = v_a_3092_;
v_a_3042_ = v_a_3122_;
goto v___jp_3039_;
}
}
}
}
}
v___jp_2876_:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
return v___x_2878_;
}
v___jp_2879_:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2880_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2880_);
return v___x_2881_;
}
v___jp_2882_:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2883_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
return v___x_2884_;
}
v___jp_2885_:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2892_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8);
v___x_2893_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__9));
v___x_2894_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2894_, 0, v___y_2887_);
lean_ctor_set(v___x_2894_, 1, v___x_2892_);
lean_ctor_set(v___x_2894_, 2, v___x_2893_);
v___x_2895_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg(v___y_2886_, v___x_2894_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
return v___x_2895_;
}
v___jp_2901_:
{
lean_object* v___x_2909_; 
lean_inc_ref(v_lhs_2866_);
v___x_2909_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_lhs_2866_);
if (lean_obj_tag(v___x_2909_) == 1)
{
lean_object* v_val_2910_; lean_object* v___x_2911_; 
v_val_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_val_2910_);
lean_dec_ref(v___x_2909_);
lean_inc_ref(v_rhs_2867_);
v___x_2911_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_rhs_2867_);
if (lean_obj_tag(v___x_2911_) == 1)
{
lean_object* v_val_2912_; uint8_t v___x_2913_; 
v_val_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_val_2912_);
lean_dec_ref(v___x_2911_);
v___x_2913_ = lean_expr_eqv(v_val_2910_, v_val_2912_);
if (v___x_2913_ == 0)
{
lean_object* v_inheritedTraceOptions_2914_; lean_object* v___x_2915_; lean_object* v_a_2916_; uint8_t v___x_2917_; 
lean_dec_ref(v_P_2865_);
v_inheritedTraceOptions_2914_ = lean_ctor_get(v___y_2907_, 13);
v___x_2915_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2899_, v_inheritedTraceOptions_2914_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2916_);
lean_dec_ref(v___x_2915_);
v___x_2917_ = lean_unbox(v_a_2916_);
lean_dec(v_a_2916_);
if (v___x_2917_ == 0)
{
lean_dec(v_val_2912_);
lean_dec(v_val_2910_);
lean_dec_ref(v_rhs_2867_);
lean_dec_ref(v_lhs_2866_);
goto v___jp_2882_;
}
else
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2918_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2);
v___x_2919_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2910_);
v___x_2920_ = l_Lean_MessageData_ofExpr(v___x_2919_);
v___x_2921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2918_);
lean_ctor_set(v___x_2921_, 1, v___x_2920_);
v___x_2922_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4);
v___x_2923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2921_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
v___x_2924_ = l_Lean_indentExpr(v_lhs_2866_);
v___x_2925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2923_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
v___x_2926_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6);
v___x_2927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2925_);
lean_ctor_set(v___x_2927_, 1, v___x_2926_);
v___x_2928_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2912_);
v___x_2929_ = l_Lean_MessageData_ofExpr(v___x_2928_);
v___x_2930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2927_);
lean_ctor_set(v___x_2930_, 1, v___x_2929_);
v___x_2931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
lean_ctor_set(v___x_2931_, 1, v___x_2922_);
v___x_2932_ = l_Lean_indentExpr(v_rhs_2867_);
v___x_2933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2931_);
lean_ctor_set(v___x_2933_, 1, v___x_2932_);
v___x_2934_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2899_, v___x_2933_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_dec_ref(v___x_2934_);
goto v___jp_2882_;
}
else
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2934_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2934_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
}
else
{
lean_object* v_options_2943_; lean_object* v_inheritedTraceOptions_2944_; uint8_t v_hasTrace_2945_; lean_object* v___x_2946_; lean_object* v___f_2947_; 
lean_dec(v_val_2912_);
v_options_2943_ = lean_ctor_get(v___y_2907_, 2);
v_inheritedTraceOptions_2944_ = lean_ctor_get(v___y_2907_, 13);
v_hasTrace_2945_ = lean_ctor_get_uint8(v_options_2943_, sizeof(void*)*1);
v___x_2946_ = lean_box(v___x_2913_);
lean_inc(v_val_2910_);
v___f_2947_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___boxed), 11, 5);
lean_closure_set(v___f_2947_, 0, v_val_2910_);
lean_closure_set(v___f_2947_, 1, v_lhs_2866_);
lean_closure_set(v___f_2947_, 2, v_rhs_2867_);
lean_closure_set(v___f_2947_, 3, v_P_2865_);
lean_closure_set(v___f_2947_, 4, v___x_2946_);
if (v_hasTrace_2945_ == 0)
{
v___y_2886_ = v___f_2947_;
v___y_2887_ = v_val_2910_;
v___y_2888_ = v___y_2905_;
v___y_2889_ = v___y_2906_;
v___y_2890_ = v___y_2907_;
v___y_2891_ = v___y_2908_;
goto v___jp_2885_;
}
else
{
lean_object* v___x_2948_; uint8_t v___x_2949_; 
v___x_2948_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_2949_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2944_, v_options_2943_, v___x_2948_);
if (v___x_2949_ == 0)
{
v___y_2886_ = v___f_2947_;
v___y_2887_ = v_val_2910_;
v___y_2888_ = v___y_2905_;
v___y_2889_ = v___y_2906_;
v___y_2890_ = v___y_2907_;
v___y_2891_ = v___y_2908_;
goto v___jp_2885_;
}
else
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2950_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11);
lean_inc(v_val_2910_);
v___x_2951_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2910_);
v___x_2952_ = l_Lean_MessageData_ofExpr(v___x_2951_);
v___x_2953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2950_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
v___x_2954_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13);
v___x_2955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2953_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
v___x_2956_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2899_, v___x_2955_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_dec_ref(v___x_2956_);
v___y_2886_ = v___f_2947_;
v___y_2887_ = v_val_2910_;
v___y_2888_ = v___y_2905_;
v___y_2889_ = v___y_2906_;
v___y_2890_ = v___y_2907_;
v___y_2891_ = v___y_2908_;
goto v___jp_2885_;
}
else
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
lean_dec_ref(v___f_2947_);
lean_dec(v_val_2910_);
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2956_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2956_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2965_; lean_object* v___x_2966_; lean_object* v_a_2967_; uint8_t v___x_2968_; 
lean_dec(v___x_2911_);
lean_dec(v_val_2910_);
lean_dec_ref(v_lhs_2866_);
lean_dec_ref(v_P_2865_);
v_inheritedTraceOptions_2965_ = lean_ctor_get(v___y_2907_, 13);
v___x_2966_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2899_, v_inheritedTraceOptions_2965_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2967_);
lean_dec_ref(v___x_2966_);
v___x_2968_ = lean_unbox(v_a_2967_);
lean_dec(v_a_2967_);
if (v___x_2968_ == 0)
{
lean_dec_ref(v_rhs_2867_);
goto v___jp_2879_;
}
else
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2969_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2970_ = l_Lean_indentExpr(v_rhs_2867_);
v___x_2971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2969_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2899_, v___x_2971_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_dec_ref(v___x_2972_);
goto v___jp_2879_;
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2972_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2972_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2981_; lean_object* v___x_2982_; lean_object* v_a_2983_; uint8_t v___x_2984_; 
lean_dec(v___x_2909_);
lean_dec_ref(v_rhs_2867_);
lean_dec_ref(v_P_2865_);
v_inheritedTraceOptions_2981_ = lean_ctor_get(v___y_2907_, 13);
v___x_2982_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2899_, v_inheritedTraceOptions_2981_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref(v___x_2982_);
v___x_2984_ = lean_unbox(v_a_2983_);
lean_dec(v_a_2983_);
if (v___x_2984_ == 0)
{
lean_dec_ref(v_lhs_2866_);
goto v___jp_2876_;
}
else
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2985_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2986_ = l_Lean_indentExpr(v_lhs_2866_);
v___x_2987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2985_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
v___x_2988_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2899_, v___x_2987_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_dec_ref(v___x_2988_);
goto v___jp_2876_;
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2988_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2988_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
}
v___jp_2997_:
{
if (v_____do__lift_2998_ == 0)
{
v___y_2902_ = v___y_2999_;
v___y_2903_ = v___y_3000_;
v___y_2904_ = v___y_3001_;
v___y_2905_ = v___y_3002_;
v___y_2906_ = v___y_3003_;
v___y_2907_ = v___y_3004_;
v___y_2908_ = v___y_3005_;
goto v___jp_2901_;
}
else
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3006_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2867_);
lean_inc_ref(v_lhs_2866_);
lean_inc_ref(v_P_2865_);
v___x_3007_ = l_Lean_mkAppB(v_P_2865_, v_lhs_2866_, v_rhs_2867_);
v___x_3008_ = l_Lean_indentExpr(v___x_3007_);
v___x_3009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3006_);
lean_ctor_set(v___x_3009_, 1, v___x_3008_);
v___x_3010_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2899_, v___x_3009_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_dec_ref(v___x_3010_);
v___y_2902_ = v___y_2999_;
v___y_2903_ = v___y_3000_;
v___y_2904_ = v___y_3001_;
v___y_2905_ = v___y_3002_;
v___y_2906_ = v___y_3003_;
v___y_2907_ = v___y_3004_;
v___y_2908_ = v___y_3005_;
goto v___jp_2901_;
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_dec_ref(v_rhs_2867_);
lean_dec_ref(v_lhs_2866_);
lean_dec_ref(v_P_2865_);
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_3010_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_3010_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___boxed(lean_object* v_P_3128_, lean_object* v_lhs_3129_, lean_object* v_rhs_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing(v_P_3128_, v_lhs_3129_, v_rhs_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_);
lean_dec(v_a_3137_);
lean_dec_ref(v_a_3136_);
lean_dec(v_a_3135_);
lean_dec_ref(v_a_3134_);
lean_dec(v_a_3133_);
lean_dec_ref(v_a_3132_);
lean_dec(v_a_3131_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0(lean_object* v_cls_3140_, lean_object* v_msg_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___x_3150_; 
v___x_3150_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3140_, v_msg_3141_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object* v_cls_3151_, lean_object* v_msg_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0(v_cls_3151_, v_msg_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5(lean_object* v_00_u03b1_3162_, lean_object* v_x_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg(v_x_3163_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___boxed(lean_object* v_00_u03b1_3173_, lean_object* v_x_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_00_u03b1_3173_, v_x_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v___y_3175_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4(lean_object* v_oldTraces_3184_, lean_object* v_data_3185_, lean_object* v_ref_3186_, lean_object* v_msg_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v___x_3196_; 
v___x_3196_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_oldTraces_3184_, v_data_3185_, v_ref_3186_, v_msg_3187_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___boxed(lean_object* v_oldTraces_3197_, lean_object* v_data_3198_, lean_object* v_ref_3199_, lean_object* v_msg_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4(v_oldTraces_3197_, v_data_3198_, v_ref_3199_, v_msg_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
return v_res_3209_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__6(void){
_start:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__5));
v___x_3220_ = l_Lean_stringToMessageData(v___x_3219_);
return v___x_3220_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__7(void){
_start:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = l_Lean_checkEmoji;
v___x_3222_ = l_Lean_stringToMessageData(v___x_3221_);
return v___x_3222_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8(void){
_start:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3223_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__7);
v___x_3224_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__6);
v___x_3225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
lean_ctor_set(v___x_3225_, 1, v___x_3223_);
return v___x_3225_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__10(void){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__9));
v___x_3228_ = l_Lean_stringToMessageData(v___x_3227_);
return v___x_3228_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__11(void){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__10);
v___x_3230_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8);
v___x_3231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
lean_ctor_set(v___x_3231_, 1, v___x_3229_);
return v___x_3231_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__13(void){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__12));
v___x_3234_ = l_Lean_stringToMessageData(v___x_3233_);
return v___x_3234_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__14(void){
_start:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3235_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__13);
v___x_3236_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8);
v___x_3237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3236_);
lean_ctor_set(v___x_3237_, 1, v___x_3235_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost(lean_object* v_e_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3238_, v_a_3243_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3354_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3250_ = v___x_3247_;
v_isShared_3251_ = v_isSharedCheck_3354_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3247_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3354_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3257_; uint8_t v___x_3258_; 
v___x_3257_ = l_Lean_Expr_cleanupAnnotations(v_a_3248_);
v___x_3258_ = l_Lean_Expr_isApp(v___x_3257_);
if (v___x_3258_ == 0)
{
lean_dec_ref(v___x_3257_);
goto v___jp_3252_;
}
else
{
lean_object* v_arg_3259_; lean_object* v___x_3260_; uint8_t v___x_3261_; 
v_arg_3259_ = lean_ctor_get(v___x_3257_, 1);
lean_inc_ref(v_arg_3259_);
v___x_3260_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3257_);
v___x_3261_ = l_Lean_Expr_isApp(v___x_3260_);
if (v___x_3261_ == 0)
{
lean_dec_ref(v___x_3260_);
lean_dec_ref(v_arg_3259_);
goto v___jp_3252_;
}
else
{
lean_object* v_arg_3262_; lean_object* v___x_3263_; uint8_t v___x_3264_; 
v_arg_3262_ = lean_ctor_get(v___x_3260_, 1);
lean_inc_ref(v_arg_3262_);
v___x_3263_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3260_);
v___x_3264_ = l_Lean_Expr_isApp(v___x_3263_);
if (v___x_3264_ == 0)
{
lean_dec_ref(v___x_3263_);
lean_dec_ref(v_arg_3262_);
lean_dec_ref(v_arg_3259_);
goto v___jp_3252_;
}
else
{
lean_object* v_arg_3265_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___x_3290_; lean_object* v___x_3291_; uint8_t v___x_3292_; 
v_arg_3265_ = lean_ctor_get(v___x_3263_, 1);
lean_inc_ref(v_arg_3265_);
v___x_3290_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3263_);
v___x_3291_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__1));
v___x_3292_ = l_Lean_Expr_isConstOf(v___x_3290_, v___x_3291_);
if (v___x_3292_ == 0)
{
uint8_t v___x_3293_; 
v___x_3293_ = l_Lean_Expr_isApp(v___x_3290_);
if (v___x_3293_ == 0)
{
lean_dec_ref(v___x_3290_);
lean_dec_ref(v_arg_3265_);
lean_dec_ref(v_arg_3262_);
lean_dec_ref(v_arg_3259_);
goto v___jp_3252_;
}
else
{
lean_object* v_arg_3294_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___x_3319_; lean_object* v___x_3320_; uint8_t v___x_3321_; 
v_arg_3294_ = lean_ctor_get(v___x_3290_, 1);
lean_inc_ref(v_arg_3294_);
v___x_3319_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3290_);
v___x_3320_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__4));
v___x_3321_ = l_Lean_Expr_isConstOf(v___x_3319_, v___x_3320_);
lean_dec_ref(v___x_3319_);
if (v___x_3321_ == 0)
{
lean_dec_ref(v_arg_3294_);
lean_dec_ref(v_arg_3265_);
lean_dec_ref(v_arg_3262_);
lean_dec_ref(v_arg_3259_);
goto v___jp_3252_;
}
else
{
lean_object* v_options_3322_; uint8_t v_hasTrace_3323_; 
lean_del_object(v___x_3250_);
v_options_3322_ = lean_ctor_get(v_a_3244_, 2);
v_hasTrace_3323_ = lean_ctor_get_uint8(v_options_3322_, sizeof(void*)*1);
if (v_hasTrace_3323_ == 0)
{
v___y_3296_ = v_a_3239_;
v___y_3297_ = v_a_3240_;
v___y_3298_ = v_a_3241_;
v___y_3299_ = v_a_3242_;
v___y_3300_ = v_a_3243_;
v___y_3301_ = v_a_3244_;
v___y_3302_ = v_a_3245_;
goto v___jp_3295_;
}
else
{
lean_object* v_inheritedTraceOptions_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; uint8_t v___x_3327_; 
v_inheritedTraceOptions_3324_ = lean_ctor_get(v_a_3244_, 13);
v___x_3325_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3326_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3327_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3324_, v_options_3322_, v___x_3326_);
if (v___x_3327_ == 0)
{
v___y_3296_ = v_a_3239_;
v___y_3297_ = v_a_3240_;
v___y_3298_ = v_a_3241_;
v___y_3299_ = v_a_3242_;
v___y_3300_ = v_a_3243_;
v___y_3301_ = v_a_3244_;
v___y_3302_ = v_a_3245_;
goto v___jp_3295_;
}
else
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3328_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__11);
v___x_3329_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3325_, v___x_3328_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_dec_ref(v___x_3329_);
v___y_3296_ = v_a_3239_;
v___y_3297_ = v_a_3240_;
v___y_3298_ = v_a_3241_;
v___y_3299_ = v_a_3242_;
v___y_3300_ = v_a_3243_;
v___y_3301_ = v_a_3244_;
v___y_3302_ = v_a_3245_;
goto v___jp_3295_;
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
lean_dec_ref(v_arg_3294_);
lean_dec_ref(v_arg_3265_);
lean_dec_ref(v_arg_3262_);
lean_dec_ref(v_arg_3259_);
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3329_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3329_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
}
}
v___jp_3295_:
{
lean_object* v___x_3303_; 
lean_inc_ref(v_arg_3294_);
v___x_3303_ = l_Lean_Meta_getDecLevel(v_arg_3294_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_a_3304_);
lean_dec_ref(v___x_3303_);
v___x_3305_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__4));
v___x_3306_ = lean_box(0);
v___x_3307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3307_, 0, v_a_3304_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
v___x_3308_ = l_Lean_Expr_const___override(v___x_3305_, v___x_3307_);
v___x_3309_ = l_Lean_mkAppB(v___x_3308_, v_arg_3294_, v_arg_3265_);
v___x_3310_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing(v___x_3309_, v_arg_3262_, v_arg_3259_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
return v___x_3310_;
}
else
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
lean_dec_ref(v_arg_3294_);
lean_dec_ref(v_arg_3265_);
lean_dec_ref(v_arg_3262_);
lean_dec_ref(v_arg_3259_);
v_a_3311_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3313_ = v___x_3303_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3303_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3311_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
}
}
}
else
{
lean_object* v_options_3338_; uint8_t v_hasTrace_3339_; 
lean_dec_ref(v___x_3290_);
lean_del_object(v___x_3250_);
v_options_3338_ = lean_ctor_get(v_a_3244_, 2);
v_hasTrace_3339_ = lean_ctor_get_uint8(v_options_3338_, sizeof(void*)*1);
if (v_hasTrace_3339_ == 0)
{
v___y_3267_ = v_a_3239_;
v___y_3268_ = v_a_3240_;
v___y_3269_ = v_a_3241_;
v___y_3270_ = v_a_3242_;
v___y_3271_ = v_a_3243_;
v___y_3272_ = v_a_3244_;
v___y_3273_ = v_a_3245_;
goto v___jp_3266_;
}
else
{
lean_object* v_inheritedTraceOptions_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; uint8_t v___x_3343_; 
v_inheritedTraceOptions_3340_ = lean_ctor_get(v_a_3244_, 13);
v___x_3341_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3342_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3343_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3340_, v_options_3338_, v___x_3342_);
if (v___x_3343_ == 0)
{
v___y_3267_ = v_a_3239_;
v___y_3268_ = v_a_3240_;
v___y_3269_ = v_a_3241_;
v___y_3270_ = v_a_3242_;
v___y_3271_ = v_a_3243_;
v___y_3272_ = v_a_3244_;
v___y_3273_ = v_a_3245_;
goto v___jp_3266_;
}
else
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3344_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__14, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__14_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__14);
v___x_3345_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3341_, v___x_3344_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_dec_ref(v___x_3345_);
v___y_3267_ = v_a_3239_;
v___y_3268_ = v_a_3240_;
v___y_3269_ = v_a_3241_;
v___y_3270_ = v_a_3242_;
v___y_3271_ = v_a_3243_;
v___y_3272_ = v_a_3244_;
v___y_3273_ = v_a_3245_;
goto v___jp_3266_;
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
lean_dec_ref(v_arg_3265_);
lean_dec_ref(v_arg_3262_);
lean_dec_ref(v_arg_3259_);
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3345_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3345_);
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
v___jp_3266_:
{
lean_object* v___x_3274_; 
lean_inc_ref(v_arg_3265_);
v___x_3274_ = l_Lean_Meta_getLevel(v_arg_3265_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref(v___x_3274_);
v___x_3276_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__1));
v___x_3277_ = lean_box(0);
v___x_3278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3278_, 0, v_a_3275_);
lean_ctor_set(v___x_3278_, 1, v___x_3277_);
v___x_3279_ = l_Lean_Expr_const___override(v___x_3276_, v___x_3278_);
v___x_3280_ = l_Lean_Expr_app___override(v___x_3279_, v_arg_3265_);
v___x_3281_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing(v___x_3280_, v_arg_3262_, v_arg_3259_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
return v___x_3281_;
}
else
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
lean_dec_ref(v_arg_3265_);
lean_dec_ref(v_arg_3262_);
lean_dec_ref(v_arg_3259_);
v_a_3282_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3284_ = v___x_3274_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3274_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3282_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
}
}
}
v___jp_3252_:
{
lean_object* v___x_3253_; lean_object* v___x_3255_; 
v___x_3253_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 0, v___x_3253_);
v___x_3255_ = v___x_3250_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3253_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
else
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3362_; 
v_a_3355_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3357_ = v___x_3247_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3247_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3360_; 
if (v_isShared_3358_ == 0)
{
v___x_3360_ = v___x_3357_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3355_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___boxed(lean_object* v_e_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost(v_e_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
lean_dec(v_a_3370_);
lean_dec_ref(v_a_3369_);
lean_dec(v_a_3368_);
lean_dec_ref(v_a_3367_);
lean_dec(v_a_3366_);
lean_dec_ref(v_a_3365_);
lean_dec(v_a_3364_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__0(lean_object* v_x_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3382_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3382_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__0___boxed(lean_object* v_x_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__0(v_x_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v_x_3384_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1(lean_object* v_x_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3405_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1___closed__0));
v___x_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3405_);
return v___x_3406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1___boxed(lean_object* v_x_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1(v_x_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v_x_3407_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__2(lean_object* v_e_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3426_, 0, v_e_3417_);
v___x_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__2___boxed(lean_object* v_e_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__2(v_e_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__3(lean_object* v_x_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3447_ = lean_box(0);
v___x_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3447_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__3___boxed(lean_object* v_x_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__3(v_x_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec_ref(v_x_3449_);
return v_res_3458_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__5(void){
_start:
{
lean_object* v___x_3465_; 
v___x_3465_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3465_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6(void){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3466_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__5);
v___x_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
return v___x_3467_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__7(void){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3468_ = lean_unsigned_to_nat(0u);
v___x_3469_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6);
v___x_3470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
lean_ctor_set(v___x_3470_, 1, v___x_3468_);
return v___x_3470_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__8(void){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3471_ = lean_unsigned_to_nat(32u);
v___x_3472_ = lean_mk_empty_array_with_capacity(v___x_3471_);
v___x_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3472_);
return v___x_3473_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__9(void){
_start:
{
size_t v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3474_ = ((size_t)5ULL);
v___x_3475_ = lean_unsigned_to_nat(0u);
v___x_3476_ = lean_unsigned_to_nat(32u);
v___x_3477_ = lean_mk_empty_array_with_capacity(v___x_3476_);
v___x_3478_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__8);
v___x_3479_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3479_, 0, v___x_3478_);
lean_ctor_set(v___x_3479_, 1, v___x_3477_);
lean_ctor_set(v___x_3479_, 2, v___x_3475_);
lean_ctor_set(v___x_3479_, 3, v___x_3475_);
lean_ctor_set_usize(v___x_3479_, 4, v___x_3474_);
return v___x_3479_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__10(void){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3480_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__9);
v___x_3481_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6);
v___x_3482_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3481_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
lean_ctor_set(v___x_3482_, 2, v___x_3481_);
lean_ctor_set(v___x_3482_, 3, v___x_3480_);
return v___x_3482_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11(void){
_start:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3483_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__10);
v___x_3484_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__7);
v___x_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
lean_ctor_set(v___x_3485_, 1, v___x_3483_);
return v___x_3485_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__12(void){
_start:
{
uint8_t v___x_3486_; lean_object* v___f_3487_; lean_object* v___f_3488_; lean_object* v___f_3489_; lean_object* v___x_3490_; lean_object* v___f_3491_; lean_object* v___x_3492_; 
v___x_3486_ = 1;
v___f_3487_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__4));
v___f_3488_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__3));
v___f_3489_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__2));
v___x_3490_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___boxed), 9, 0);
v___f_3491_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__1));
v___x_3492_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3492_, 0, v___f_3491_);
lean_ctor_set(v___x_3492_, 1, v___x_3490_);
lean_ctor_set(v___x_3492_, 2, v___f_3489_);
lean_ctor_set(v___x_3492_, 3, v___f_3488_);
lean_ctor_set(v___x_3492_, 4, v___f_3487_);
lean_ctor_set_uint8(v___x_3492_, sizeof(void*)*5, v___x_3486_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget(lean_object* v_mvarId_3493_, lean_object* v_maxSteps_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_){
_start:
{
lean_object* v___x_3500_; 
v___x_3500_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_3498_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v___x_3502_; lean_object* v_maxDischargeDepth_3503_; uint8_t v_contextual_3504_; uint8_t v_memoize_3505_; uint8_t v_singlePass_3506_; uint8_t v_zeta_3507_; uint8_t v_beta_3508_; uint8_t v_eta_3509_; uint8_t v_etaStruct_3510_; uint8_t v_iota_3511_; uint8_t v_proj_3512_; uint8_t v_decide_3513_; uint8_t v_arith_3514_; uint8_t v_autoUnfold_3515_; uint8_t v_dsimp_3516_; uint8_t v_failIfUnchanged_3517_; uint8_t v_ground_3518_; uint8_t v_unfoldPartialApp_3519_; uint8_t v_zetaDelta_3520_; uint8_t v_index_3521_; uint8_t v_implicitDefEqProofs_3522_; uint8_t v_zetaUnused_3523_; uint8_t v_catchRuntime_3524_; uint8_t v_zetaHave_3525_; uint8_t v_letToHave_3526_; uint8_t v_congrConsts_3527_; uint8_t v_bitVecOfNat_3528_; uint8_t v_warnExponents_3529_; uint8_t v_suggestions_3530_; lean_object* v_maxSuggestions_3531_; uint8_t v_locals_3532_; uint8_t v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref(v___x_3500_);
v___x_3502_ = l_Lean_Meta_Simp_neutralConfig;
v_maxDischargeDepth_3503_ = lean_ctor_get(v___x_3502_, 1);
v_contextual_3504_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3);
v_memoize_3505_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 1);
v_singlePass_3506_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 2);
v_zeta_3507_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 3);
v_beta_3508_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 4);
v_eta_3509_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 5);
v_etaStruct_3510_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 6);
v_iota_3511_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 7);
v_proj_3512_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 8);
v_decide_3513_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 9);
v_arith_3514_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 10);
v_autoUnfold_3515_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 11);
v_dsimp_3516_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 12);
v_failIfUnchanged_3517_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 13);
v_ground_3518_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_3519_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 15);
v_zetaDelta_3520_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 16);
v_index_3521_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_3522_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 18);
v_zetaUnused_3523_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 19);
v_catchRuntime_3524_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 20);
v_zetaHave_3525_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 21);
v_letToHave_3526_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 22);
v_congrConsts_3527_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 23);
v_bitVecOfNat_3528_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 24);
v_warnExponents_3529_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 25);
v_suggestions_3530_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 26);
v_maxSuggestions_3531_ = lean_ctor_get(v___x_3502_, 2);
v_locals_3532_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*3 + 27);
v___x_3533_ = 1;
lean_inc(v_maxSuggestions_3531_);
lean_inc(v_maxDischargeDepth_3503_);
v___x_3534_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_3534_, 0, v_maxSteps_3494_);
lean_ctor_set(v___x_3534_, 1, v_maxDischargeDepth_3503_);
lean_ctor_set(v___x_3534_, 2, v_maxSuggestions_3531_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3, v_contextual_3504_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 1, v_memoize_3505_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 2, v_singlePass_3506_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 3, v_zeta_3507_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 4, v_beta_3508_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 5, v_eta_3509_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 6, v_etaStruct_3510_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 7, v_iota_3511_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 8, v_proj_3512_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 9, v_decide_3513_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 10, v_arith_3514_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 11, v_autoUnfold_3515_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 12, v_dsimp_3516_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 13, v_failIfUnchanged_3517_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 14, v_ground_3518_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 15, v_unfoldPartialApp_3519_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 16, v_zetaDelta_3520_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 17, v_index_3521_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_3522_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 19, v_zetaUnused_3523_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 20, v_catchRuntime_3524_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 21, v_zetaHave_3525_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 22, v_letToHave_3526_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 23, v_congrConsts_3527_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 24, v_bitVecOfNat_3528_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 25, v_warnExponents_3529_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 26, v_suggestions_3530_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 27, v_locals_3532_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 28, v___x_3533_);
v___x_3535_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__0));
v___x_3536_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_3534_, v___x_3535_, v_a_3501_, v_a_3495_, v_a_3497_, v_a_3498_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3538_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3537_);
lean_dec_ref(v___x_3536_);
lean_inc(v_mvarId_3493_);
v___x_3538_ = l_Lean_MVarId_getType(v_mvarId_3493_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3539_; lean_object* v___x_3540_; lean_object* v_a_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_a_3539_);
lean_dec_ref(v___x_3538_);
v___x_3540_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(v_a_3539_, v_a_3496_);
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc_n(v_a_3541_, 2);
lean_dec_ref(v___x_3540_);
v___x_3542_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11);
v___x_3543_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__12);
v___x_3544_ = l_Lean_Meta_Simp_main(v_a_3541_, v_a_3537_, v___x_3542_, v___x_3543_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; lean_object* v_fst_3546_; lean_object* v___x_3547_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
lean_inc(v_a_3545_);
lean_dec_ref(v___x_3544_);
v_fst_3546_ = lean_ctor_get(v_a_3545_, 0);
lean_inc(v_fst_3546_);
lean_dec(v_a_3545_);
v___x_3547_ = l_Lean_Meta_applySimpResultToTarget(v_mvarId_3493_, v_a_3541_, v_fst_3546_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_);
lean_dec(v_a_3541_);
return v___x_3547_;
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
lean_dec(v_a_3541_);
lean_dec(v_mvarId_3493_);
v_a_3548_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3544_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3544_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
lean_dec(v_a_3537_);
lean_dec(v_mvarId_3493_);
v_a_3556_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3538_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3538_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
else
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3571_; 
lean_dec(v_mvarId_3493_);
v_a_3564_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3566_ = v___x_3536_;
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3536_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_a_3564_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
}
else
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
lean_dec(v_maxSteps_3494_);
lean_dec(v_mvarId_3493_);
v_a_3572_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___x_3500_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3500_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3572_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___boxed(lean_object* v_mvarId_3580_, lean_object* v_maxSteps_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget(v_mvarId_3580_, v_maxSteps_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_);
lean_dec(v_a_3585_);
lean_dec_ref(v_a_3584_);
lean_dec(v_a_3583_);
lean_dec_ref(v_a_3582_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg(lean_object* v_mvarId_3588_, lean_object* v_x_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v___x_3595_; 
v___x_3595_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3588_, v_x_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3603_; 
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3598_ = v___x_3595_;
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3595_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
else
{
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
v_a_3604_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3606_ = v___x_3595_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3595_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_a_3604_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg___boxed(lean_object* v_mvarId_3612_, lean_object* v_x_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg(v_mvarId_3612_, v_x_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0(lean_object* v_00_u03b1_3620_, lean_object* v_mvarId_3621_, lean_object* v_x_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg(v_mvarId_3621_, v_x_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___boxed(lean_object* v_00_u03b1_3629_, lean_object* v_mvarId_3630_, lean_object* v_x_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0(v_00_u03b1_3629_, v_mvarId_3630_, v_x_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___lam__4(lean_object* v_maxSteps_3638_, lean_object* v_fvarId_3639_, lean_object* v___f_3640_, lean_object* v___f_3641_, lean_object* v___f_3642_, lean_object* v___f_3643_, lean_object* v_goal_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v___x_3650_; 
v___x_3650_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_3648_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v___x_3652_; lean_object* v_maxDischargeDepth_3653_; uint8_t v_contextual_3654_; uint8_t v_memoize_3655_; uint8_t v_singlePass_3656_; uint8_t v_zeta_3657_; uint8_t v_beta_3658_; uint8_t v_eta_3659_; uint8_t v_etaStruct_3660_; uint8_t v_iota_3661_; uint8_t v_proj_3662_; uint8_t v_decide_3663_; uint8_t v_arith_3664_; uint8_t v_autoUnfold_3665_; uint8_t v_dsimp_3666_; uint8_t v_failIfUnchanged_3667_; uint8_t v_ground_3668_; uint8_t v_unfoldPartialApp_3669_; uint8_t v_zetaDelta_3670_; uint8_t v_index_3671_; uint8_t v_implicitDefEqProofs_3672_; uint8_t v_zetaUnused_3673_; uint8_t v_catchRuntime_3674_; uint8_t v_zetaHave_3675_; uint8_t v_letToHave_3676_; uint8_t v_congrConsts_3677_; uint8_t v_bitVecOfNat_3678_; uint8_t v_warnExponents_3679_; uint8_t v_suggestions_3680_; lean_object* v_maxSuggestions_3681_; uint8_t v_locals_3682_; uint8_t v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_a_3651_);
lean_dec_ref(v___x_3650_);
v___x_3652_ = l_Lean_Meta_Simp_neutralConfig;
v_maxDischargeDepth_3653_ = lean_ctor_get(v___x_3652_, 1);
v_contextual_3654_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3);
v_memoize_3655_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 1);
v_singlePass_3656_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 2);
v_zeta_3657_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 3);
v_beta_3658_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 4);
v_eta_3659_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 5);
v_etaStruct_3660_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 6);
v_iota_3661_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 7);
v_proj_3662_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 8);
v_decide_3663_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 9);
v_arith_3664_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 10);
v_autoUnfold_3665_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 11);
v_dsimp_3666_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 12);
v_failIfUnchanged_3667_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 13);
v_ground_3668_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_3669_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 15);
v_zetaDelta_3670_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 16);
v_index_3671_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_3672_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 18);
v_zetaUnused_3673_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 19);
v_catchRuntime_3674_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 20);
v_zetaHave_3675_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 21);
v_letToHave_3676_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 22);
v_congrConsts_3677_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 23);
v_bitVecOfNat_3678_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 24);
v_warnExponents_3679_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 25);
v_suggestions_3680_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 26);
v_maxSuggestions_3681_ = lean_ctor_get(v___x_3652_, 2);
v_locals_3682_ = lean_ctor_get_uint8(v___x_3652_, sizeof(void*)*3 + 27);
v___x_3683_ = 1;
lean_inc(v_maxSuggestions_3681_);
lean_inc(v_maxDischargeDepth_3653_);
v___x_3684_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_3684_, 0, v_maxSteps_3638_);
lean_ctor_set(v___x_3684_, 1, v_maxDischargeDepth_3653_);
lean_ctor_set(v___x_3684_, 2, v_maxSuggestions_3681_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3, v_contextual_3654_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 1, v_memoize_3655_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 2, v_singlePass_3656_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 3, v_zeta_3657_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 4, v_beta_3658_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 5, v_eta_3659_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 6, v_etaStruct_3660_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 7, v_iota_3661_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 8, v_proj_3662_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 9, v_decide_3663_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 10, v_arith_3664_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 11, v_autoUnfold_3665_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 12, v_dsimp_3666_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 13, v_failIfUnchanged_3667_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 14, v_ground_3668_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 15, v_unfoldPartialApp_3669_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 16, v_zetaDelta_3670_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 17, v_index_3671_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_3672_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 19, v_zetaUnused_3673_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 20, v_catchRuntime_3674_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 21, v_zetaHave_3675_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 22, v_letToHave_3676_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 23, v_congrConsts_3677_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 24, v_bitVecOfNat_3678_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 25, v_warnExponents_3679_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 26, v_suggestions_3680_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 27, v_locals_3682_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 28, v___x_3683_);
v___x_3685_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__0));
v___x_3686_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_3684_, v___x_3685_, v_a_3651_, v___y_3645_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v___x_3688_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_a_3687_);
lean_dec_ref(v___x_3686_);
lean_inc(v_fvarId_3639_);
v___x_3688_ = l_Lean_FVarId_getType___redArg(v_fvarId_3639_, v___y_3645_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_a_3689_; lean_object* v___x_3690_; lean_object* v_a_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
lean_inc(v_a_3689_);
lean_dec_ref(v___x_3688_);
v___x_3690_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(v_a_3689_, v___y_3646_);
v_a_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc(v_a_3691_);
lean_dec_ref(v___x_3690_);
v___x_3692_ = lean_unsigned_to_nat(32u);
v___x_3693_ = lean_mk_empty_array_with_capacity(v___x_3692_);
lean_dec_ref(v___x_3693_);
v___x_3694_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11);
v___x_3695_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___boxed), 9, 0);
v___x_3696_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3696_, 0, v___f_3640_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
lean_ctor_set(v___x_3696_, 2, v___f_3641_);
lean_ctor_set(v___x_3696_, 3, v___f_3642_);
lean_ctor_set(v___x_3696_, 4, v___f_3643_);
lean_ctor_set_uint8(v___x_3696_, sizeof(void*)*5, v___x_3683_);
v___x_3697_ = l_Lean_Meta_Simp_main(v_a_3691_, v_a_3687_, v___x_3694_, v___x_3696_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v_a_3698_; lean_object* v_fst_3699_; uint8_t v___x_3700_; lean_object* v___x_3701_; 
v_a_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc(v_a_3698_);
lean_dec_ref(v___x_3697_);
v_fst_3699_ = lean_ctor_get(v_a_3698_, 0);
lean_inc(v_fst_3699_);
lean_dec(v_a_3698_);
v___x_3700_ = 0;
v___x_3701_ = l_Lean_Meta_applySimpResultToLocalDecl(v_goal_3644_, v_fvarId_3639_, v_fst_3699_, v___x_3700_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3722_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3704_ = v___x_3701_;
v_isShared_3705_ = v_isSharedCheck_3722_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_a_3702_);
lean_dec(v___x_3701_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3722_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
if (lean_obj_tag(v_a_3702_) == 0)
{
lean_object* v___x_3706_; lean_object* v___x_3708_; 
v___x_3706_ = lean_box(0);
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 0, v___x_3706_);
v___x_3708_ = v___x_3704_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3706_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
else
{
lean_object* v_val_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3721_; 
v_val_3710_ = lean_ctor_get(v_a_3702_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v_a_3702_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3712_ = v_a_3702_;
v_isShared_3713_ = v_isSharedCheck_3721_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_val_3710_);
lean_dec(v_a_3702_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3721_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v_snd_3714_; lean_object* v___x_3716_; 
v_snd_3714_ = lean_ctor_get(v_val_3710_, 1);
lean_inc(v_snd_3714_);
lean_dec(v_val_3710_);
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 0, v_snd_3714_);
v___x_3716_ = v___x_3712_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_snd_3714_);
v___x_3716_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
lean_object* v___x_3718_; 
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 0, v___x_3716_);
v___x_3718_ = v___x_3704_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
}
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
v_a_3723_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3701_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3701_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
lean_dec(v_goal_3644_);
lean_dec(v_fvarId_3639_);
v_a_3731_ = lean_ctor_get(v___x_3697_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3697_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3697_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
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
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
lean_dec(v_a_3687_);
lean_dec(v_goal_3644_);
lean_dec_ref(v___f_3643_);
lean_dec_ref(v___f_3642_);
lean_dec_ref(v___f_3641_);
lean_dec_ref(v___f_3640_);
lean_dec(v_fvarId_3639_);
v_a_3739_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3688_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3688_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
lean_dec(v_goal_3644_);
lean_dec_ref(v___f_3643_);
lean_dec_ref(v___f_3642_);
lean_dec_ref(v___f_3641_);
lean_dec_ref(v___f_3640_);
lean_dec(v_fvarId_3639_);
v_a_3747_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3686_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3686_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_dec(v_goal_3644_);
lean_dec_ref(v___f_3643_);
lean_dec_ref(v___f_3642_);
lean_dec_ref(v___f_3641_);
lean_dec_ref(v___f_3640_);
lean_dec(v_fvarId_3639_);
lean_dec(v_maxSteps_3638_);
v_a_3755_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3650_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3650_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___lam__4___boxed(lean_object* v_maxSteps_3763_, lean_object* v_fvarId_3764_, lean_object* v___f_3765_, lean_object* v___f_3766_, lean_object* v___f_3767_, lean_object* v___f_3768_, lean_object* v_goal_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___lam__4(v_maxSteps_3763_, v_fvarId_3764_, v___f_3765_, v___f_3766_, v___f_3767_, v___f_3768_, v_goal_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta(lean_object* v_goal_3776_, lean_object* v_fvarId_3777_, lean_object* v_maxSteps_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_){
_start:
{
lean_object* v___f_3784_; lean_object* v___f_3785_; lean_object* v___f_3786_; lean_object* v___f_3787_; lean_object* v___f_3788_; lean_object* v___x_3789_; 
v___f_3784_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__4));
v___f_3785_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__3));
v___f_3786_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__2));
v___f_3787_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__1));
lean_inc(v_goal_3776_);
v___f_3788_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___lam__4___boxed), 12, 7);
lean_closure_set(v___f_3788_, 0, v_maxSteps_3778_);
lean_closure_set(v___f_3788_, 1, v_fvarId_3777_);
lean_closure_set(v___f_3788_, 2, v___f_3787_);
lean_closure_set(v___f_3788_, 3, v___f_3786_);
lean_closure_set(v___f_3788_, 4, v___f_3785_);
lean_closure_set(v___f_3788_, 5, v___f_3784_);
lean_closure_set(v___f_3788_, 6, v_goal_3776_);
v___x_3789_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg(v_goal_3776_, v___f_3788_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___boxed(lean_object* v_goal_3790_, lean_object* v_fvarId_3791_, lean_object* v_maxSteps_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_){
_start:
{
lean_object* v_res_3798_; 
v_res_3798_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta(v_goal_3790_, v_fvarId_3791_, v_maxSteps_3792_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_);
lean_dec(v_a_3796_);
lean_dec_ref(v_a_3795_);
lean_dec(v_a_3794_);
lean_dec_ref(v_a_3793_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0(lean_object* v_x_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v___x_3807_; 
lean_inc(v___y_3801_);
lean_inc_ref(v___y_3800_);
v___x_3807_ = lean_apply_7(v_x_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, lean_box(0));
return v___x_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0___boxed(lean_object* v_x_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0(v_x_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(lean_object* v_mvarId_3817_, lean_object* v_x_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v___f_3826_; lean_object* v___x_3827_; 
lean_inc(v___y_3820_);
lean_inc_ref(v___y_3819_);
v___f_3826_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3826_, 0, v_x_3818_);
lean_closure_set(v___f_3826_, 1, v___y_3819_);
lean_closure_set(v___f_3826_, 2, v___y_3820_);
v___x_3827_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3817_, v___f_3826_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_);
if (lean_obj_tag(v___x_3827_) == 0)
{
return v___x_3827_;
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3827_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3827_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___boxed(lean_object* v_mvarId_3836_, lean_object* v_x_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(v_mvarId_3836_, v_x_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4(lean_object* v_00_u03b1_3846_, lean_object* v_mvarId_3847_, lean_object* v_x_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_){
_start:
{
lean_object* v___x_3856_; 
v___x_3856_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(v_mvarId_3847_, v_x_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
return v___x_3856_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___boxed(lean_object* v_00_u03b1_3857_, lean_object* v_mvarId_3858_, lean_object* v_x_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4(v_00_u03b1_3857_, v_mvarId_3858_, v_x_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
return v_res_3867_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(lean_object* v_a_3868_, lean_object* v_x_3869_){
_start:
{
if (lean_obj_tag(v_x_3869_) == 0)
{
uint8_t v___x_3870_; 
v___x_3870_ = 0;
return v___x_3870_;
}
else
{
lean_object* v_key_3871_; lean_object* v_tail_3872_; uint8_t v___x_3873_; 
v_key_3871_ = lean_ctor_get(v_x_3869_, 0);
v_tail_3872_ = lean_ctor_get(v_x_3869_, 2);
v___x_3873_ = l_Lean_instBEqFVarId_beq(v_key_3871_, v_a_3868_);
if (v___x_3873_ == 0)
{
v_x_3869_ = v_tail_3872_;
goto _start;
}
else
{
return v___x_3873_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg___boxed(lean_object* v_a_3875_, lean_object* v_x_3876_){
_start:
{
uint8_t v_res_3877_; lean_object* v_r_3878_; 
v_res_3877_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_3875_, v_x_3876_);
lean_dec(v_x_3876_);
lean_dec(v_a_3875_);
v_r_3878_ = lean_box(v_res_3877_);
return v_r_3878_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(lean_object* v_x_3879_, lean_object* v_x_3880_){
_start:
{
if (lean_obj_tag(v_x_3880_) == 0)
{
return v_x_3879_;
}
else
{
lean_object* v_key_3881_; lean_object* v_value_3882_; lean_object* v_tail_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3906_; 
v_key_3881_ = lean_ctor_get(v_x_3880_, 0);
v_value_3882_ = lean_ctor_get(v_x_3880_, 1);
v_tail_3883_ = lean_ctor_get(v_x_3880_, 2);
v_isSharedCheck_3906_ = !lean_is_exclusive(v_x_3880_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3885_ = v_x_3880_;
v_isShared_3886_ = v_isSharedCheck_3906_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_tail_3883_);
lean_inc(v_value_3882_);
lean_inc(v_key_3881_);
lean_dec(v_x_3880_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3906_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3887_; uint64_t v___x_3888_; uint64_t v___x_3889_; uint64_t v___x_3890_; uint64_t v_fold_3891_; uint64_t v___x_3892_; uint64_t v___x_3893_; uint64_t v___x_3894_; size_t v___x_3895_; size_t v___x_3896_; size_t v___x_3897_; size_t v___x_3898_; size_t v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3902_; 
v___x_3887_ = lean_array_get_size(v_x_3879_);
v___x_3888_ = l_Lean_instHashableFVarId_hash(v_key_3881_);
v___x_3889_ = 32ULL;
v___x_3890_ = lean_uint64_shift_right(v___x_3888_, v___x_3889_);
v_fold_3891_ = lean_uint64_xor(v___x_3888_, v___x_3890_);
v___x_3892_ = 16ULL;
v___x_3893_ = lean_uint64_shift_right(v_fold_3891_, v___x_3892_);
v___x_3894_ = lean_uint64_xor(v_fold_3891_, v___x_3893_);
v___x_3895_ = lean_uint64_to_usize(v___x_3894_);
v___x_3896_ = lean_usize_of_nat(v___x_3887_);
v___x_3897_ = ((size_t)1ULL);
v___x_3898_ = lean_usize_sub(v___x_3896_, v___x_3897_);
v___x_3899_ = lean_usize_land(v___x_3895_, v___x_3898_);
v___x_3900_ = lean_array_uget_borrowed(v_x_3879_, v___x_3899_);
lean_inc(v___x_3900_);
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 2, v___x_3900_);
v___x_3902_ = v___x_3885_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_key_3881_);
lean_ctor_set(v_reuseFailAlloc_3905_, 1, v_value_3882_);
lean_ctor_set(v_reuseFailAlloc_3905_, 2, v___x_3900_);
v___x_3902_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
lean_object* v___x_3903_; 
v___x_3903_ = lean_array_uset(v_x_3879_, v___x_3899_, v___x_3902_);
v_x_3879_ = v___x_3903_;
v_x_3880_ = v_tail_3883_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(lean_object* v_i_3907_, lean_object* v_source_3908_, lean_object* v_target_3909_){
_start:
{
lean_object* v___x_3910_; uint8_t v___x_3911_; 
v___x_3910_ = lean_array_get_size(v_source_3908_);
v___x_3911_ = lean_nat_dec_lt(v_i_3907_, v___x_3910_);
if (v___x_3911_ == 0)
{
lean_dec_ref(v_source_3908_);
lean_dec(v_i_3907_);
return v_target_3909_;
}
else
{
lean_object* v_es_3912_; lean_object* v___x_3913_; lean_object* v_source_3914_; lean_object* v_target_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
v_es_3912_ = lean_array_fget(v_source_3908_, v_i_3907_);
v___x_3913_ = lean_box(0);
v_source_3914_ = lean_array_fset(v_source_3908_, v_i_3907_, v___x_3913_);
v_target_3915_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(v_target_3909_, v_es_3912_);
v___x_3916_ = lean_unsigned_to_nat(1u);
v___x_3917_ = lean_nat_add(v_i_3907_, v___x_3916_);
lean_dec(v_i_3907_);
v_i_3907_ = v___x_3917_;
v_source_3908_ = v_source_3914_;
v_target_3909_ = v_target_3915_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(lean_object* v_data_3919_){
_start:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v_nbuckets_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3920_ = lean_array_get_size(v_data_3919_);
v___x_3921_ = lean_unsigned_to_nat(2u);
v_nbuckets_3922_ = lean_nat_mul(v___x_3920_, v___x_3921_);
v___x_3923_ = lean_unsigned_to_nat(0u);
v___x_3924_ = lean_box(0);
v___x_3925_ = lean_mk_array(v_nbuckets_3922_, v___x_3924_);
v___x_3926_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(v___x_3923_, v_data_3919_, v___x_3925_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object* v_m_3927_, lean_object* v_a_3928_, lean_object* v_b_3929_){
_start:
{
lean_object* v_size_3930_; lean_object* v_buckets_3931_; lean_object* v___x_3932_; uint64_t v___x_3933_; uint64_t v___x_3934_; uint64_t v___x_3935_; uint64_t v_fold_3936_; uint64_t v___x_3937_; uint64_t v___x_3938_; uint64_t v___x_3939_; size_t v___x_3940_; size_t v___x_3941_; size_t v___x_3942_; size_t v___x_3943_; size_t v___x_3944_; lean_object* v_bkt_3945_; uint8_t v___x_3946_; 
v_size_3930_ = lean_ctor_get(v_m_3927_, 0);
v_buckets_3931_ = lean_ctor_get(v_m_3927_, 1);
v___x_3932_ = lean_array_get_size(v_buckets_3931_);
v___x_3933_ = l_Lean_instHashableFVarId_hash(v_a_3928_);
v___x_3934_ = 32ULL;
v___x_3935_ = lean_uint64_shift_right(v___x_3933_, v___x_3934_);
v_fold_3936_ = lean_uint64_xor(v___x_3933_, v___x_3935_);
v___x_3937_ = 16ULL;
v___x_3938_ = lean_uint64_shift_right(v_fold_3936_, v___x_3937_);
v___x_3939_ = lean_uint64_xor(v_fold_3936_, v___x_3938_);
v___x_3940_ = lean_uint64_to_usize(v___x_3939_);
v___x_3941_ = lean_usize_of_nat(v___x_3932_);
v___x_3942_ = ((size_t)1ULL);
v___x_3943_ = lean_usize_sub(v___x_3941_, v___x_3942_);
v___x_3944_ = lean_usize_land(v___x_3940_, v___x_3943_);
v_bkt_3945_ = lean_array_uget_borrowed(v_buckets_3931_, v___x_3944_);
v___x_3946_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_3928_, v_bkt_3945_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3967_; 
lean_inc_ref(v_buckets_3931_);
lean_inc(v_size_3930_);
v_isSharedCheck_3967_ = !lean_is_exclusive(v_m_3927_);
if (v_isSharedCheck_3967_ == 0)
{
lean_object* v_unused_3968_; lean_object* v_unused_3969_; 
v_unused_3968_ = lean_ctor_get(v_m_3927_, 1);
lean_dec(v_unused_3968_);
v_unused_3969_ = lean_ctor_get(v_m_3927_, 0);
lean_dec(v_unused_3969_);
v___x_3948_ = v_m_3927_;
v_isShared_3949_ = v_isSharedCheck_3967_;
goto v_resetjp_3947_;
}
else
{
lean_dec(v_m_3927_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3967_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3950_; lean_object* v_size_x27_3951_; lean_object* v___x_3952_; lean_object* v_buckets_x27_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; uint8_t v___x_3959_; 
v___x_3950_ = lean_unsigned_to_nat(1u);
v_size_x27_3951_ = lean_nat_add(v_size_3930_, v___x_3950_);
lean_dec(v_size_3930_);
lean_inc(v_bkt_3945_);
v___x_3952_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3952_, 0, v_a_3928_);
lean_ctor_set(v___x_3952_, 1, v_b_3929_);
lean_ctor_set(v___x_3952_, 2, v_bkt_3945_);
v_buckets_x27_3953_ = lean_array_uset(v_buckets_3931_, v___x_3944_, v___x_3952_);
v___x_3954_ = lean_unsigned_to_nat(4u);
v___x_3955_ = lean_nat_mul(v_size_x27_3951_, v___x_3954_);
v___x_3956_ = lean_unsigned_to_nat(3u);
v___x_3957_ = lean_nat_div(v___x_3955_, v___x_3956_);
lean_dec(v___x_3955_);
v___x_3958_ = lean_array_get_size(v_buckets_x27_3953_);
v___x_3959_ = lean_nat_dec_le(v___x_3957_, v___x_3958_);
lean_dec(v___x_3957_);
if (v___x_3959_ == 0)
{
lean_object* v_val_3960_; lean_object* v___x_3962_; 
v_val_3960_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(v_buckets_x27_3953_);
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 1, v_val_3960_);
lean_ctor_set(v___x_3948_, 0, v_size_x27_3951_);
v___x_3962_ = v___x_3948_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_size_x27_3951_);
lean_ctor_set(v_reuseFailAlloc_3963_, 1, v_val_3960_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
else
{
lean_object* v___x_3965_; 
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 1, v_buckets_x27_3953_);
lean_ctor_set(v___x_3948_, 0, v_size_x27_3951_);
v___x_3965_ = v___x_3948_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_size_x27_3951_);
lean_ctor_set(v_reuseFailAlloc_3966_, 1, v_buckets_x27_3953_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
else
{
lean_dec(v_b_3929_);
lean_dec(v_a_3928_);
return v_m_3927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(lean_object* v_as_3970_, size_t v_i_3971_, size_t v_stop_3972_, lean_object* v_b_3973_, lean_object* v___y_3974_){
_start:
{
uint8_t v___x_3976_; 
v___x_3976_ = lean_usize_dec_eq(v_i_3971_, v_stop_3972_);
if (v___x_3976_ == 0)
{
lean_object* v___x_3977_; lean_object* v_rewriteCache_3978_; lean_object* v_acNfCache_3979_; lean_object* v_typeAnalysis_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3994_; 
v___x_3977_ = lean_st_ref_take(v___y_3974_);
v_rewriteCache_3978_ = lean_ctor_get(v___x_3977_, 0);
v_acNfCache_3979_ = lean_ctor_get(v___x_3977_, 1);
v_typeAnalysis_3980_ = lean_ctor_get(v___x_3977_, 2);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3982_ = v___x_3977_;
v_isShared_3983_ = v_isSharedCheck_3994_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_typeAnalysis_3980_);
lean_inc(v_acNfCache_3979_);
lean_inc(v_rewriteCache_3978_);
lean_dec(v___x_3977_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3994_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3988_; 
v___x_3984_ = lean_array_uget_borrowed(v_as_3970_, v_i_3971_);
v___x_3985_ = lean_box(0);
lean_inc(v___x_3984_);
v___x_3986_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1___redArg(v_acNfCache_3979_, v___x_3984_, v___x_3985_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 1, v___x_3986_);
v___x_3988_ = v___x_3982_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_rewriteCache_3978_);
lean_ctor_set(v_reuseFailAlloc_3993_, 1, v___x_3986_);
lean_ctor_set(v_reuseFailAlloc_3993_, 2, v_typeAnalysis_3980_);
v___x_3988_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
lean_object* v___x_3989_; size_t v___x_3990_; size_t v___x_3991_; 
v___x_3989_ = lean_st_ref_set(v___y_3974_, v___x_3988_);
v___x_3990_ = ((size_t)1ULL);
v___x_3991_ = lean_usize_add(v_i_3971_, v___x_3990_);
v_i_3971_ = v___x_3991_;
v_b_3973_ = v___x_3985_;
goto _start;
}
}
}
else
{
lean_object* v___x_3995_; 
v___x_3995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3995_, 0, v_b_3973_);
return v___x_3995_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg___boxed(lean_object* v_as_3996_, lean_object* v_i_3997_, lean_object* v_stop_3998_, lean_object* v_b_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_){
_start:
{
size_t v_i_boxed_4002_; size_t v_stop_boxed_4003_; lean_object* v_res_4004_; 
v_i_boxed_4002_ = lean_unbox_usize(v_i_3997_);
lean_dec(v_i_3997_);
v_stop_boxed_4003_ = lean_unbox_usize(v_stop_3998_);
lean_dec(v_stop_3998_);
v_res_4004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(v_as_3996_, v_i_boxed_4002_, v_stop_boxed_4003_, v_b_3999_, v___y_4000_);
lean_dec(v___y_4000_);
lean_dec_ref(v_as_3996_);
return v_res_4004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__0(lean_object* v___x_4005_, size_t v___x_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v___x_4014_; 
v___x_4014_ = l_Lean_Meta_getPropHyps(v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4033_; 
v_a_4015_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4033_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4033_ == 0)
{
v___x_4017_ = v___x_4014_;
v_isShared_4018_ = v_isSharedCheck_4033_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_4014_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4033_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; uint8_t v___x_4021_; 
v___x_4019_ = lean_array_get_size(v_a_4015_);
v___x_4020_ = lean_box(0);
v___x_4021_ = lean_nat_dec_lt(v___x_4005_, v___x_4019_);
if (v___x_4021_ == 0)
{
lean_object* v___x_4023_; 
lean_dec(v_a_4015_);
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 0, v___x_4020_);
v___x_4023_ = v___x_4017_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v___x_4020_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
return v___x_4023_;
}
}
else
{
uint8_t v___x_4025_; 
v___x_4025_ = lean_nat_dec_le(v___x_4019_, v___x_4019_);
if (v___x_4025_ == 0)
{
if (v___x_4021_ == 0)
{
lean_object* v___x_4027_; 
lean_dec(v_a_4015_);
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 0, v___x_4020_);
v___x_4027_ = v___x_4017_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v___x_4020_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
else
{
size_t v___x_4029_; lean_object* v___x_4030_; 
lean_del_object(v___x_4017_);
v___x_4029_ = lean_usize_of_nat(v___x_4019_);
v___x_4030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(v_a_4015_, v___x_4006_, v___x_4029_, v___x_4020_, v___y_4008_);
lean_dec(v_a_4015_);
return v___x_4030_;
}
}
else
{
size_t v___x_4031_; lean_object* v___x_4032_; 
lean_del_object(v___x_4017_);
v___x_4031_ = lean_usize_of_nat(v___x_4019_);
v___x_4032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(v_a_4015_, v___x_4006_, v___x_4031_, v___x_4020_, v___y_4008_);
lean_dec(v_a_4015_);
return v___x_4032_;
}
}
}
}
else
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4041_; 
v_a_4034_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4036_ = v___x_4014_;
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___x_4014_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4039_; 
if (v_isShared_4037_ == 0)
{
v___x_4039_ = v___x_4036_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4034_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__0___boxed(lean_object* v___x_4042_, lean_object* v___x_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_){
_start:
{
size_t v___x_8305__boxed_4051_; lean_object* v_res_4052_; 
v___x_8305__boxed_4051_ = lean_unbox_usize(v___x_4043_);
lean_dec(v___x_4043_);
v_res_4052_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__0(v___x_4042_, v___x_8305__boxed_4051_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_);
lean_dec(v___y_4049_);
lean_dec_ref(v___y_4048_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
lean_dec(v___x_4042_);
return v_res_4052_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object* v_m_4053_, lean_object* v_a_4054_){
_start:
{
lean_object* v_buckets_4055_; lean_object* v___x_4056_; uint64_t v___x_4057_; uint64_t v___x_4058_; uint64_t v___x_4059_; uint64_t v_fold_4060_; uint64_t v___x_4061_; uint64_t v___x_4062_; uint64_t v___x_4063_; size_t v___x_4064_; size_t v___x_4065_; size_t v___x_4066_; size_t v___x_4067_; size_t v___x_4068_; lean_object* v___x_4069_; uint8_t v___x_4070_; 
v_buckets_4055_ = lean_ctor_get(v_m_4053_, 1);
v___x_4056_ = lean_array_get_size(v_buckets_4055_);
v___x_4057_ = l_Lean_instHashableFVarId_hash(v_a_4054_);
v___x_4058_ = 32ULL;
v___x_4059_ = lean_uint64_shift_right(v___x_4057_, v___x_4058_);
v_fold_4060_ = lean_uint64_xor(v___x_4057_, v___x_4059_);
v___x_4061_ = 16ULL;
v___x_4062_ = lean_uint64_shift_right(v_fold_4060_, v___x_4061_);
v___x_4063_ = lean_uint64_xor(v_fold_4060_, v___x_4062_);
v___x_4064_ = lean_uint64_to_usize(v___x_4063_);
v___x_4065_ = lean_usize_of_nat(v___x_4056_);
v___x_4066_ = ((size_t)1ULL);
v___x_4067_ = lean_usize_sub(v___x_4065_, v___x_4066_);
v___x_4068_ = lean_usize_land(v___x_4064_, v___x_4067_);
v___x_4069_ = lean_array_uget_borrowed(v_buckets_4055_, v___x_4068_);
v___x_4070_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_4054_, v___x_4069_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object* v_m_4071_, lean_object* v_a_4072_){
_start:
{
uint8_t v_res_4073_; lean_object* v_r_4074_; 
v_res_4073_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg(v_m_4071_, v_a_4072_);
lean_dec(v_a_4072_);
lean_dec_ref(v_m_4071_);
v_r_4074_ = lean_box(v_res_4073_);
return v_r_4074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(lean_object* v_as_4075_, size_t v_i_4076_, size_t v_stop_4077_, lean_object* v_b_4078_, lean_object* v___y_4079_){
_start:
{
lean_object* v_a_4082_; uint8_t v___x_4086_; 
v___x_4086_ = lean_usize_dec_eq(v_i_4076_, v_stop_4077_);
if (v___x_4086_ == 0)
{
lean_object* v___x_4087_; lean_object* v_acNfCache_4088_; lean_object* v___x_4089_; uint8_t v___x_4090_; 
v___x_4087_ = lean_st_ref_get(v___y_4079_);
v_acNfCache_4088_ = lean_ctor_get(v___x_4087_, 1);
lean_inc_ref(v_acNfCache_4088_);
lean_dec(v___x_4087_);
v___x_4089_ = lean_array_uget_borrowed(v_as_4075_, v_i_4076_);
v___x_4090_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg(v_acNfCache_4088_, v___x_4089_);
lean_dec_ref(v_acNfCache_4088_);
if (v___x_4090_ == 0)
{
lean_object* v___x_4091_; 
lean_inc(v___x_4089_);
v___x_4091_ = lean_array_push(v_b_4078_, v___x_4089_);
v_a_4082_ = v___x_4091_;
goto v___jp_4081_;
}
else
{
v_a_4082_ = v_b_4078_;
goto v___jp_4081_;
}
}
else
{
lean_object* v___x_4092_; 
v___x_4092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4092_, 0, v_b_4078_);
return v___x_4092_;
}
v___jp_4081_:
{
size_t v___x_4083_; size_t v___x_4084_; 
v___x_4083_ = ((size_t)1ULL);
v___x_4084_ = lean_usize_add(v_i_4076_, v___x_4083_);
v_i_4076_ = v___x_4084_;
v_b_4078_ = v_a_4082_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg___boxed(lean_object* v_as_4093_, lean_object* v_i_4094_, lean_object* v_stop_4095_, lean_object* v_b_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
size_t v_i_boxed_4099_; size_t v_stop_boxed_4100_; lean_object* v_res_4101_; 
v_i_boxed_4099_ = lean_unbox_usize(v_i_4094_);
lean_dec(v_i_4094_);
v_stop_boxed_4100_ = lean_unbox_usize(v_stop_4095_);
lean_dec(v_stop_4095_);
v_res_4101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(v_as_4093_, v_i_boxed_4099_, v_stop_boxed_4100_, v_b_4096_, v___y_4097_);
lean_dec(v___y_4097_);
lean_dec_ref(v_as_4093_);
return v_res_4101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object* v_as_4102_, size_t v_sz_4103_, size_t v_i_4104_, lean_object* v_b_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
uint8_t v___x_4112_; 
v___x_4112_ = lean_usize_dec_lt(v_i_4104_, v_sz_4103_);
if (v___x_4112_ == 0)
{
lean_object* v___x_4113_; 
v___x_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4113_, 0, v_b_4105_);
return v___x_4113_;
}
else
{
lean_object* v_maxSteps_4114_; lean_object* v_a_4115_; lean_object* v___x_4116_; 
v_maxSteps_4114_ = lean_ctor_get(v___y_4106_, 1);
v_a_4115_ = lean_array_uget_borrowed(v_as_4102_, v_i_4104_);
lean_inc(v_maxSteps_4114_);
lean_inc(v_a_4115_);
lean_inc(v_b_4105_);
v___x_4116_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta(v_b_4105_, v_a_4115_, v_maxSteps_4114_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_object* v_a_4117_; lean_object* v_a_4119_; 
v_a_4117_ = lean_ctor_get(v___x_4116_, 0);
lean_inc(v_a_4117_);
lean_dec_ref(v___x_4116_);
if (lean_obj_tag(v_a_4117_) == 1)
{
lean_object* v_val_4123_; 
lean_dec(v_b_4105_);
v_val_4123_ = lean_ctor_get(v_a_4117_, 0);
lean_inc(v_val_4123_);
lean_dec_ref(v_a_4117_);
v_a_4119_ = v_val_4123_;
goto v___jp_4118_;
}
else
{
lean_dec(v_a_4117_);
v_a_4119_ = v_b_4105_;
goto v___jp_4118_;
}
v___jp_4118_:
{
size_t v___x_4120_; size_t v___x_4121_; 
v___x_4120_ = ((size_t)1ULL);
v___x_4121_ = lean_usize_add(v_i_4104_, v___x_4120_);
v_i_4104_ = v___x_4121_;
v_b_4105_ = v_a_4119_;
goto _start;
}
}
else
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
lean_dec(v_b_4105_);
v_a_4124_ = lean_ctor_get(v___x_4116_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4126_ = v___x_4116_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v___x_4116_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4124_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object* v_as_4132_, lean_object* v_sz_4133_, lean_object* v_i_4134_, lean_object* v_b_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_){
_start:
{
size_t v_sz_boxed_4142_; size_t v_i_boxed_4143_; lean_object* v_res_4144_; 
v_sz_boxed_4142_ = lean_unbox_usize(v_sz_4133_);
lean_dec(v_sz_4133_);
v_i_boxed_4143_ = lean_unbox_usize(v_i_4134_);
lean_dec(v_i_4134_);
v_res_4144_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg(v_as_4132_, v_sz_boxed_4142_, v_i_boxed_4143_, v_b_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec_ref(v_as_4132_);
return v_res_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1(lean_object* v_goal_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
lean_object* v___x_4160_; 
v___x_4160_ = l_Lean_Meta_getPropHyps(v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4161_; lean_object* v___x_4162_; lean_object* v_a_4164_; lean_object* v___y_4197_; lean_object* v___x_4207_; lean_object* v___x_4208_; uint8_t v___x_4209_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4161_);
lean_dec_ref(v___x_4160_);
v___x_4162_ = lean_unsigned_to_nat(0u);
v___x_4207_ = lean_array_get_size(v_a_4161_);
v___x_4208_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__1));
v___x_4209_ = lean_nat_dec_lt(v___x_4162_, v___x_4207_);
if (v___x_4209_ == 0)
{
lean_dec(v_a_4161_);
v_a_4164_ = v___x_4208_;
goto v___jp_4163_;
}
else
{
uint8_t v___x_4210_; 
v___x_4210_ = lean_nat_dec_le(v___x_4207_, v___x_4207_);
if (v___x_4210_ == 0)
{
if (v___x_4209_ == 0)
{
lean_dec(v_a_4161_);
v_a_4164_ = v___x_4208_;
goto v___jp_4163_;
}
else
{
size_t v___x_4211_; size_t v___x_4212_; lean_object* v___x_4213_; 
v___x_4211_ = ((size_t)0ULL);
v___x_4212_ = lean_usize_of_nat(v___x_4207_);
v___x_4213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(v_a_4161_, v___x_4211_, v___x_4212_, v___x_4208_, v___y_4154_);
lean_dec(v_a_4161_);
v___y_4197_ = v___x_4213_;
goto v___jp_4196_;
}
}
else
{
size_t v___x_4214_; size_t v___x_4215_; lean_object* v___x_4216_; 
v___x_4214_ = ((size_t)0ULL);
v___x_4215_ = lean_usize_of_nat(v___x_4207_);
v___x_4216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(v_a_4161_, v___x_4214_, v___x_4215_, v___x_4208_, v___y_4154_);
lean_dec(v_a_4161_);
v___y_4197_ = v___x_4216_;
goto v___jp_4196_;
}
}
v___jp_4163_:
{
size_t v_sz_4165_; size_t v___x_4166_; lean_object* v___x_4167_; 
v_sz_4165_ = lean_array_size(v_a_4164_);
v___x_4166_ = ((size_t)0ULL);
v___x_4167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg(v_a_4164_, v_sz_4165_, v___x_4166_, v_goal_4152_, v___y_4153_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
lean_dec_ref(v_a_4164_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_object* v_a_4168_; lean_object* v___f_4169_; lean_object* v___x_4170_; 
v_a_4168_ = lean_ctor_get(v___x_4167_, 0);
lean_inc_n(v_a_4168_, 2);
lean_dec_ref(v___x_4167_);
v___f_4169_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__0));
v___x_4170_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(v_a_4168_, v___f_4169_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4178_; 
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4178_ == 0)
{
lean_object* v_unused_4179_; 
v_unused_4179_ = lean_ctor_get(v___x_4170_, 0);
lean_dec(v_unused_4179_);
v___x_4172_ = v___x_4170_;
v_isShared_4173_ = v_isSharedCheck_4178_;
goto v_resetjp_4171_;
}
else
{
lean_dec(v___x_4170_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4178_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4174_; lean_object* v___x_4176_; 
v___x_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4174_, 0, v_a_4168_);
if (v_isShared_4173_ == 0)
{
lean_ctor_set(v___x_4172_, 0, v___x_4174_);
v___x_4176_ = v___x_4172_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v___x_4174_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
return v___x_4176_;
}
}
}
else
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4187_; 
lean_dec(v_a_4168_);
v_a_4180_ = lean_ctor_get(v___x_4170_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4182_ = v___x_4170_;
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4170_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4185_; 
if (v_isShared_4183_ == 0)
{
v___x_4185_ = v___x_4182_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_a_4180_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
return v___x_4185_;
}
}
}
}
else
{
lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4195_; 
v_a_4188_ = lean_ctor_get(v___x_4167_, 0);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4190_ = v___x_4167_;
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_dec(v___x_4167_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___x_4193_; 
if (v_isShared_4191_ == 0)
{
v___x_4193_ = v___x_4190_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_a_4188_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
}
}
v___jp_4196_:
{
if (lean_obj_tag(v___y_4197_) == 0)
{
lean_object* v_a_4198_; 
v_a_4198_ = lean_ctor_get(v___y_4197_, 0);
lean_inc(v_a_4198_);
lean_dec_ref(v___y_4197_);
v_a_4164_ = v_a_4198_;
goto v___jp_4163_;
}
else
{
lean_object* v_a_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4206_; 
lean_dec(v_goal_4152_);
v_a_4199_ = lean_ctor_get(v___y_4197_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___y_4197_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4201_ = v___y_4197_;
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_a_4199_);
lean_dec(v___y_4197_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___x_4204_; 
if (v_isShared_4202_ == 0)
{
v___x_4204_ = v___x_4201_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_a_4199_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
}
}
}
else
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
lean_dec(v_goal_4152_);
v_a_4217_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4219_ = v___x_4160_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4160_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4222_; 
if (v_isShared_4220_ == 0)
{
v___x_4222_ = v___x_4219_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_a_4217_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___boxed(lean_object* v_goal_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v_res_4233_; 
v_res_4233_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1(v_goal_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__2(lean_object* v_goal_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_){
_start:
{
lean_object* v___f_4242_; lean_object* v___x_4243_; 
lean_inc(v_goal_4234_);
v___f_4242_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___boxed), 8, 1);
lean_closure_set(v___f_4242_, 0, v_goal_4234_);
v___x_4243_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(v_goal_4234_, v___f_4242_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_);
return v___x_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__2___boxed(lean_object* v_goal_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__2(v_goal_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
lean_dec(v___y_4250_);
lean_dec_ref(v___y_4249_);
lean_dec(v___y_4248_);
lean_dec_ref(v___y_4247_);
lean_dec(v___y_4246_);
lean_dec_ref(v___y_4245_);
return v_res_4252_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0(lean_object* v_00_u03b2_4261_, lean_object* v_m_4262_, lean_object* v_a_4263_){
_start:
{
uint8_t v___x_4264_; 
v___x_4264_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg(v_m_4262_, v_a_4263_);
return v___x_4264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___boxed(lean_object* v_00_u03b2_4265_, lean_object* v_m_4266_, lean_object* v_a_4267_){
_start:
{
uint8_t v_res_4268_; lean_object* v_r_4269_; 
v_res_4268_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0(v_00_u03b2_4265_, v_m_4266_, v_a_4267_);
lean_dec(v_a_4267_);
lean_dec_ref(v_m_4266_);
v_r_4269_ = lean_box(v_res_4268_);
return v_r_4269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1(lean_object* v_00_u03b2_4270_, lean_object* v_m_4271_, lean_object* v_a_4272_, lean_object* v_b_4273_){
_start:
{
lean_object* v___x_4274_; 
v___x_4274_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1___redArg(v_m_4271_, v_a_4272_, v_b_4273_);
return v___x_4274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2(lean_object* v_as_4275_, size_t v_sz_4276_, size_t v_i_4277_, lean_object* v_b_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_){
_start:
{
lean_object* v___x_4286_; 
v___x_4286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg(v_as_4275_, v_sz_4276_, v_i_4277_, v_b_4278_, v___y_4279_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
return v___x_4286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object* v_as_4287_, lean_object* v_sz_4288_, lean_object* v_i_4289_, lean_object* v_b_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
size_t v_sz_boxed_4298_; size_t v_i_boxed_4299_; lean_object* v_res_4300_; 
v_sz_boxed_4298_ = lean_unbox_usize(v_sz_4288_);
lean_dec(v_sz_4288_);
v_i_boxed_4299_ = lean_unbox_usize(v_i_4289_);
lean_dec(v_i_4289_);
v_res_4300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2(v_as_4287_, v_sz_boxed_4298_, v_i_boxed_4299_, v_b_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec_ref(v_as_4287_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3(lean_object* v_as_4301_, size_t v_i_4302_, size_t v_stop_4303_, lean_object* v_b_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v___x_4312_; 
v___x_4312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(v_as_4301_, v_i_4302_, v_stop_4303_, v_b_4304_, v___y_4306_);
return v___x_4312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___boxed(lean_object* v_as_4313_, lean_object* v_i_4314_, lean_object* v_stop_4315_, lean_object* v_b_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_){
_start:
{
size_t v_i_boxed_4324_; size_t v_stop_boxed_4325_; lean_object* v_res_4326_; 
v_i_boxed_4324_ = lean_unbox_usize(v_i_4314_);
lean_dec(v_i_4314_);
v_stop_boxed_4325_ = lean_unbox_usize(v_stop_4315_);
lean_dec(v_stop_4315_);
v_res_4326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3(v_as_4313_, v_i_boxed_4324_, v_stop_boxed_4325_, v_b_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
lean_dec(v___y_4320_);
lean_dec_ref(v___y_4319_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
lean_dec_ref(v_as_4313_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5(lean_object* v_as_4327_, size_t v_i_4328_, size_t v_stop_4329_, lean_object* v_b_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_){
_start:
{
lean_object* v___x_4338_; 
v___x_4338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(v_as_4327_, v_i_4328_, v_stop_4329_, v_b_4330_, v___y_4332_);
return v___x_4338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___boxed(lean_object* v_as_4339_, lean_object* v_i_4340_, lean_object* v_stop_4341_, lean_object* v_b_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
size_t v_i_boxed_4350_; size_t v_stop_boxed_4351_; lean_object* v_res_4352_; 
v_i_boxed_4350_ = lean_unbox_usize(v_i_4340_);
lean_dec(v_i_4340_);
v_stop_boxed_4351_ = lean_unbox_usize(v_stop_4341_);
lean_dec(v_stop_4341_);
v_res_4352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5(v_as_4339_, v_i_boxed_4350_, v_stop_boxed_4351_, v_b_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec_ref(v_as_4339_);
return v_res_4352_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0(lean_object* v_00_u03b2_4353_, lean_object* v_a_4354_, lean_object* v_x_4355_){
_start:
{
uint8_t v___x_4356_; 
v___x_4356_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_4354_, v_x_4355_);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4357_, lean_object* v_a_4358_, lean_object* v_x_4359_){
_start:
{
uint8_t v_res_4360_; lean_object* v_r_4361_; 
v_res_4360_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0(v_00_u03b2_4357_, v_a_4358_, v_x_4359_);
lean_dec(v_x_4359_);
lean_dec(v_a_4358_);
v_r_4361_ = lean_box(v_res_4360_);
return v_r_4361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2(lean_object* v_00_u03b2_4362_, lean_object* v_data_4363_){
_start:
{
lean_object* v___x_4364_; 
v___x_4364_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(v_data_4363_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4365_, lean_object* v_i_4366_, lean_object* v_source_4367_, lean_object* v_target_4368_){
_start:
{
lean_object* v___x_4369_; 
v___x_4369_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(v_i_4366_, v_source_4367_, v_target_4368_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4370_, lean_object* v_x_4371_, lean_object* v_x_4372_){
_start:
{
lean_object* v___x_4373_; 
v___x_4373_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(v_x_4371_, v_x_4372_);
return v___x_4373_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_AC_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_AC_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_AC_Main(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_AC_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC(builtin);
}
#ifdef __cplusplus
}
#endif
