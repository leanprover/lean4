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
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* v_ref_825_; lean_object* v___x_826_; lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_872_; 
v_ref_825_ = lean_ctor_get(v___y_822_, 5);
v___x_826_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_818_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_872_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_872_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_872_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v_traceState_832_; lean_object* v_env_833_; lean_object* v_nextMacroScope_834_; lean_object* v_ngen_835_; lean_object* v_auxDeclNGen_836_; lean_object* v_cache_837_; lean_object* v_messages_838_; lean_object* v_infoState_839_; lean_object* v_snapshotTasks_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_871_; 
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
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_871_ == 0)
{
v___x_842_ = v___x_831_;
v_isShared_843_ = v_isSharedCheck_871_;
goto v_resetjp_841_;
}
else
{
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
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_871_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
uint64_t v_tid_844_; lean_object* v_traces_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_870_; 
v_tid_844_ = lean_ctor_get_uint64(v_traceState_832_, sizeof(void*)*1);
v_traces_845_ = lean_ctor_get(v_traceState_832_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v_traceState_832_);
if (v_isSharedCheck_870_ == 0)
{
v___x_847_ = v_traceState_832_;
v_isShared_848_ = v_isSharedCheck_870_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_traces_845_);
lean_dec(v_traceState_832_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_870_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; double v___x_850_; uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_849_ = lean_box(0);
v___x_850_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0);
v___x_851_ = 0;
v___x_852_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1));
v___x_853_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_853_, 0, v_cls_817_);
lean_ctor_set(v___x_853_, 1, v___x_849_);
lean_ctor_set(v___x_853_, 2, v___x_852_);
lean_ctor_set_float(v___x_853_, sizeof(void*)*3, v___x_850_);
lean_ctor_set_float(v___x_853_, sizeof(void*)*3 + 8, v___x_850_);
lean_ctor_set_uint8(v___x_853_, sizeof(void*)*3 + 16, v___x_851_);
v___x_854_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__2));
v___x_855_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v_a_827_);
lean_ctor_set(v___x_855_, 2, v___x_854_);
lean_inc(v_ref_825_);
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v_ref_825_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = l_Lean_PersistentArray_push___redArg(v_traces_845_, v___x_856_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_857_);
v___x_859_ = v___x_847_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_857_);
lean_ctor_set_uint64(v_reuseFailAlloc_869_, sizeof(void*)*1, v_tid_844_);
v___x_859_ = v_reuseFailAlloc_869_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_861_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 4, v___x_859_);
v___x_861_ = v___x_842_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_env_833_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_nextMacroScope_834_);
lean_ctor_set(v_reuseFailAlloc_868_, 2, v_ngen_835_);
lean_ctor_set(v_reuseFailAlloc_868_, 3, v_auxDeclNGen_836_);
lean_ctor_set(v_reuseFailAlloc_868_, 4, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_868_, 5, v_cache_837_);
lean_ctor_set(v_reuseFailAlloc_868_, 6, v_messages_838_);
lean_ctor_set(v_reuseFailAlloc_868_, 7, v_infoState_839_);
lean_ctor_set(v_reuseFailAlloc_868_, 8, v_snapshotTasks_840_);
v___x_861_ = v_reuseFailAlloc_868_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_862_ = lean_st_ref_set(v___y_823_, v___x_861_);
v___x_863_ = lean_box(0);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___y_819_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_864_);
v___x_866_ = v___x_829_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___boxed(lean_object* v_cls_873_, lean_object* v_msg_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0(v_cls_873_, v_msg_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
return v_res_881_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6(void){
_start:
{
lean_object* v_cls_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_cls_892_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_893_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_894_ = l_Lean_Name_append(v___x_893_, v_cls_892_);
return v___x_894_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__8(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__7));
v___x_897_ = l_Lean_stringToMessageData(v___x_896_);
return v___x_897_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__9));
v___x_900_ = l_Lean_stringToMessageData(v___x_899_);
return v___x_900_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__12(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__11));
v___x_903_ = l_Lean_stringToMessageData(v___x_902_);
return v___x_903_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__14(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__13));
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go(lean_object* v_op_907_, lean_object* v_coeff_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
if (lean_obj_tag(v_a_909_) == 5)
{
lean_object* v_fn_916_; 
v_fn_916_ = lean_ctor_get(v_a_909_, 0);
if (lean_obj_tag(v_fn_916_) == 5)
{
lean_object* v_arg_917_; lean_object* v_fn_918_; lean_object* v_arg_919_; uint8_t v___x_920_; 
v_arg_917_ = lean_ctor_get(v_a_909_, 1);
v_fn_918_ = lean_ctor_get(v_fn_916_, 0);
v_arg_919_ = lean_ctor_get(v_fn_916_, 1);
lean_inc_ref(v_fn_918_);
v___x_920_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind___redArg(v_fn_918_);
if (v___x_920_ == 0)
{
lean_object* v_options_921_; uint8_t v_hasTrace_922_; 
v_options_921_ = lean_ctor_get(v_a_913_, 2);
v_hasTrace_922_ = lean_ctor_get_uint8(v_options_921_, sizeof(void*)*1);
if (v_hasTrace_922_ == 0)
{
lean_object* v___x_923_; 
lean_dec_ref(v_op_907_);
v___x_923_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_908_, v_a_909_, v_a_910_);
return v___x_923_;
}
else
{
lean_object* v_inheritedTraceOptions_924_; lean_object* v_cls_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v_inheritedTraceOptions_924_ = lean_ctor_get(v_a_913_, 13);
v_cls_925_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_926_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_927_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_924_, v_options_921_, v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; 
lean_dec_ref(v_op_907_);
v___x_928_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_908_, v_a_909_, v_a_910_);
return v___x_928_;
}
else
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_929_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__8, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__8_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__8);
lean_inc_ref(v_fn_918_);
v___x_930_ = l_Lean_MessageData_ofExpr(v_fn_918_);
v___x_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
lean_inc_ref(v_arg_919_);
v___x_934_ = l_Lean_MessageData_ofExpr(v_arg_919_);
v___x_935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_932_);
lean_inc_ref(v_arg_917_);
v___x_937_ = l_Lean_MessageData_ofExpr(v_arg_917_);
v___x_938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__12, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__12_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__12);
v___x_940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_938_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_op_907_);
v___x_942_ = l_Lean_MessageData_ofExpr(v___x_941_);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_940_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__14, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__14_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__14);
v___x_945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_943_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0(v_cls_925_, v___x_945_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v_snd_948_; lean_object* v___x_949_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref(v___x_946_);
v_snd_948_ = lean_ctor_get(v_a_947_, 1);
lean_inc(v_snd_948_);
lean_dec(v_a_947_);
v___x_949_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_908_, v_a_909_, v_snd_948_);
return v___x_949_;
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref(v_a_909_);
lean_dec_ref(v_coeff_908_);
v_a_950_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_946_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_946_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
}
else
{
lean_object* v___x_958_; 
lean_inc_ref(v_arg_919_);
lean_inc_ref(v_arg_917_);
lean_dec_ref(v_a_909_);
lean_inc_ref(v_op_907_);
v___x_958_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go(v_op_907_, v_coeff_908_, v_arg_919_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v_fst_960_; lean_object* v_snd_961_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref(v___x_958_);
v_fst_960_ = lean_ctor_get(v_a_959_, 0);
lean_inc(v_fst_960_);
v_snd_961_ = lean_ctor_get(v_a_959_, 1);
lean_inc(v_snd_961_);
lean_dec(v_a_959_);
v_coeff_908_ = v_fst_960_;
v_a_909_ = v_arg_917_;
v_a_910_ = v_snd_961_;
goto _start;
}
else
{
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_op_907_);
return v___x_958_;
}
}
}
else
{
lean_object* v___x_963_; 
lean_dec_ref(v_op_907_);
v___x_963_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_908_, v_a_909_, v_a_910_);
return v___x_963_;
}
}
else
{
lean_object* v___x_964_; 
lean_dec_ref(v_op_907_);
v___x_964_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_908_, v_a_909_, v_a_910_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___boxed(lean_object* v_op_965_, lean_object* v_coeff_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go(v_op_965_, v_coeff_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
return v_res_974_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_box(0);
v___x_976_ = lean_unsigned_to_nat(16u);
v___x_977_ = lean_mk_array(v___x_976_, v___x_975_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set(v___x_980_, 1, v___x_978_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(lean_object* v_op_981_, lean_object* v_e_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_990_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go(v_op_981_, v___x_989_, v_e_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___boxed(lean_object* v_op_991_, lean_object* v_e_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(v_op_991_, v_e_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0(lean_object* v_commonCnt_1000_, lean_object* v_a_1001_, lean_object* v_x_1002_){
_start:
{
if (lean_obj_tag(v_x_1002_) == 0)
{
lean_dec(v_a_1001_);
return v_x_1002_;
}
else
{
lean_object* v_key_1003_; lean_object* v_value_1004_; lean_object* v_tail_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1018_; 
v_key_1003_ = lean_ctor_get(v_x_1002_, 0);
v_value_1004_ = lean_ctor_get(v_x_1002_, 1);
v_tail_1005_ = lean_ctor_get(v_x_1002_, 2);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_x_1002_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1007_ = v_x_1002_;
v_isShared_1008_ = v_isSharedCheck_1018_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_tail_1005_);
lean_inc(v_value_1004_);
lean_inc(v_key_1003_);
lean_dec(v_x_1002_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1018_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
uint8_t v___x_1009_; 
v___x_1009_ = lean_nat_dec_eq(v_key_1003_, v_a_1001_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1000_, v_a_1001_, v_tail_1005_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 2, v___x_1010_);
v___x_1012_ = v___x_1007_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_key_1003_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_value_1004_);
lean_ctor_set(v_reuseFailAlloc_1013_, 2, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
lean_dec(v_key_1003_);
v___x_1014_ = lean_nat_sub(v_value_1004_, v_commonCnt_1000_);
lean_dec(v_value_1004_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 1, v___x_1014_);
lean_ctor_set(v___x_1007_, 0, v_a_1001_);
v___x_1016_ = v___x_1007_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1001_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v_tail_1005_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0___boxed(lean_object* v_commonCnt_1019_, lean_object* v_a_1020_, lean_object* v_x_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1019_, v_a_1020_, v_x_1021_);
lean_dec(v_commonCnt_1019_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0(lean_object* v_commonCnt_1023_, lean_object* v_m_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_size_1026_; lean_object* v_buckets_1027_; lean_object* v___x_1028_; uint64_t v___x_1029_; uint64_t v___x_1030_; uint64_t v___x_1031_; uint64_t v_fold_1032_; uint64_t v___x_1033_; uint64_t v___x_1034_; uint64_t v___x_1035_; size_t v___x_1036_; size_t v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; lean_object* v_bucket_1041_; uint8_t v___x_1042_; 
v_size_1026_ = lean_ctor_get(v_m_1024_, 0);
v_buckets_1027_ = lean_ctor_get(v_m_1024_, 1);
v___x_1028_ = lean_array_get_size(v_buckets_1027_);
v___x_1029_ = lean_uint64_of_nat(v_a_1025_);
v___x_1030_ = 32ULL;
v___x_1031_ = lean_uint64_shift_right(v___x_1029_, v___x_1030_);
v_fold_1032_ = lean_uint64_xor(v___x_1029_, v___x_1031_);
v___x_1033_ = 16ULL;
v___x_1034_ = lean_uint64_shift_right(v_fold_1032_, v___x_1033_);
v___x_1035_ = lean_uint64_xor(v_fold_1032_, v___x_1034_);
v___x_1036_ = lean_uint64_to_usize(v___x_1035_);
v___x_1037_ = lean_usize_of_nat(v___x_1028_);
v___x_1038_ = ((size_t)1ULL);
v___x_1039_ = lean_usize_sub(v___x_1037_, v___x_1038_);
v___x_1040_ = lean_usize_land(v___x_1036_, v___x_1039_);
v_bucket_1041_ = lean_array_uget_borrowed(v_buckets_1027_, v___x_1040_);
v___x_1042_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1025_, v_bucket_1041_);
if (v___x_1042_ == 0)
{
lean_dec(v_a_1025_);
return v_m_1024_;
}
else
{
lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1053_; 
lean_inc(v_bucket_1041_);
lean_inc_ref(v_buckets_1027_);
lean_inc(v_size_1026_);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_m_1024_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; lean_object* v_unused_1055_; 
v_unused_1054_ = lean_ctor_get(v_m_1024_, 1);
lean_dec(v_unused_1054_);
v_unused_1055_ = lean_ctor_get(v_m_1024_, 0);
lean_dec(v_unused_1055_);
v___x_1044_ = v_m_1024_;
v_isShared_1045_ = v_isSharedCheck_1053_;
goto v_resetjp_1043_;
}
else
{
lean_dec(v_m_1024_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1053_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v_buckets_1047_; lean_object* v_bucket_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1046_ = lean_box(0);
v_buckets_1047_ = lean_array_uset(v_buckets_1027_, v___x_1040_, v___x_1046_);
v_bucket_1048_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1023_, v_a_1025_, v_bucket_1041_);
v___x_1049_ = lean_array_uset(v_buckets_1047_, v___x_1040_, v_bucket_1048_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 1, v___x_1049_);
v___x_1051_ = v___x_1044_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_size_1026_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v___x_1049_);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0___boxed(lean_object* v_commonCnt_1056_, lean_object* v_m_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0(v_commonCnt_1056_, v_m_1057_, v_a_1058_);
lean_dec(v_commonCnt_1056_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__1_spec__2(lean_object* v_x_1060_, lean_object* v_x_1061_){
_start:
{
if (lean_obj_tag(v_x_1061_) == 0)
{
return v_x_1060_;
}
else
{
lean_object* v_key_1062_; lean_object* v_value_1063_; lean_object* v_tail_1064_; lean_object* v___x_1065_; 
v_key_1062_ = lean_ctor_get(v_x_1061_, 0);
lean_inc(v_key_1062_);
v_value_1063_ = lean_ctor_get(v_x_1061_, 1);
lean_inc(v_value_1063_);
v_tail_1064_ = lean_ctor_get(v_x_1061_, 2);
lean_inc(v_tail_1064_);
lean_dec_ref(v_x_1061_);
v___x_1065_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0(v_value_1063_, v_x_1060_, v_key_1062_);
lean_dec(v_value_1063_);
v_x_1060_ = v___x_1065_;
v_x_1061_ = v_tail_1064_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__1(lean_object* v_x_1067_, lean_object* v_x_1068_){
_start:
{
if (lean_obj_tag(v_x_1068_) == 0)
{
return v_x_1067_;
}
else
{
lean_object* v_key_1069_; lean_object* v_value_1070_; lean_object* v_tail_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v_key_1069_ = lean_ctor_get(v_x_1068_, 0);
lean_inc(v_key_1069_);
v_value_1070_ = lean_ctor_get(v_x_1068_, 1);
lean_inc(v_value_1070_);
v_tail_1071_ = lean_ctor_get(v_x_1068_, 2);
lean_inc(v_tail_1071_);
lean_dec_ref(v_x_1068_);
v___x_1072_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0(v_value_1070_, v_x_1067_, v_key_1069_);
lean_dec(v_value_1070_);
v___x_1073_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__1_spec__2(v___x_1072_, v_tail_1071_);
return v___x_1073_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(lean_object* v_as_1074_, size_t v_i_1075_, size_t v_stop_1076_, lean_object* v_b_1077_){
_start:
{
uint8_t v___x_1078_; 
v___x_1078_ = lean_usize_dec_eq(v_i_1075_, v_stop_1076_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1080_; size_t v___x_1081_; size_t v___x_1082_; 
v___x_1079_ = lean_array_uget_borrowed(v_as_1074_, v_i_1075_);
lean_inc(v___x_1079_);
v___x_1080_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__1(v_b_1077_, v___x_1079_);
v___x_1081_ = ((size_t)1ULL);
v___x_1082_ = lean_usize_add(v_i_1075_, v___x_1081_);
v_i_1075_ = v___x_1082_;
v_b_1077_ = v___x_1080_;
goto _start;
}
else
{
return v_b_1077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2___boxed(lean_object* v_as_1084_, lean_object* v_i_1085_, lean_object* v_stop_1086_, lean_object* v_b_1087_){
_start:
{
size_t v_i_boxed_1088_; size_t v_stop_boxed_1089_; lean_object* v_res_1090_; 
v_i_boxed_1088_ = lean_unbox_usize(v_i_1085_);
lean_dec(v_i_1085_);
v_stop_boxed_1089_ = lean_unbox_usize(v_stop_1086_);
lean_dec(v_stop_1086_);
v_res_1090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(v_as_1084_, v_i_boxed_1088_, v_stop_boxed_1089_, v_b_1087_);
lean_dec_ref(v_as_1084_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(lean_object* v_a_1091_, lean_object* v_x_1092_){
_start:
{
if (lean_obj_tag(v_x_1092_) == 0)
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_box(0);
return v___x_1093_;
}
else
{
lean_object* v_key_1094_; lean_object* v_value_1095_; lean_object* v_tail_1096_; uint8_t v___x_1097_; 
v_key_1094_ = lean_ctor_get(v_x_1092_, 0);
v_value_1095_ = lean_ctor_get(v_x_1092_, 1);
v_tail_1096_ = lean_ctor_get(v_x_1092_, 2);
v___x_1097_ = lean_nat_dec_eq(v_key_1094_, v_a_1091_);
if (v___x_1097_ == 0)
{
v_x_1092_ = v_tail_1096_;
goto _start;
}
else
{
lean_object* v___x_1099_; 
lean_inc(v_value_1095_);
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v_value_1095_);
return v___x_1099_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg___boxed(lean_object* v_a_1100_, lean_object* v_x_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1100_, v_x_1101_);
lean_dec(v_x_1101_);
lean_dec(v_a_1100_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg(lean_object* v_m_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_buckets_1105_; lean_object* v___x_1106_; uint64_t v___x_1107_; uint64_t v___x_1108_; uint64_t v___x_1109_; uint64_t v_fold_1110_; uint64_t v___x_1111_; uint64_t v___x_1112_; uint64_t v___x_1113_; size_t v___x_1114_; size_t v___x_1115_; size_t v___x_1116_; size_t v___x_1117_; size_t v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v_buckets_1105_ = lean_ctor_get(v_m_1103_, 1);
v___x_1106_ = lean_array_get_size(v_buckets_1105_);
v___x_1107_ = lean_uint64_of_nat(v_a_1104_);
v___x_1108_ = 32ULL;
v___x_1109_ = lean_uint64_shift_right(v___x_1107_, v___x_1108_);
v_fold_1110_ = lean_uint64_xor(v___x_1107_, v___x_1109_);
v___x_1111_ = 16ULL;
v___x_1112_ = lean_uint64_shift_right(v_fold_1110_, v___x_1111_);
v___x_1113_ = lean_uint64_xor(v_fold_1110_, v___x_1112_);
v___x_1114_ = lean_uint64_to_usize(v___x_1113_);
v___x_1115_ = lean_usize_of_nat(v___x_1106_);
v___x_1116_ = ((size_t)1ULL);
v___x_1117_ = lean_usize_sub(v___x_1115_, v___x_1116_);
v___x_1118_ = lean_usize_land(v___x_1114_, v___x_1117_);
v___x_1119_ = lean_array_uget_borrowed(v_buckets_1105_, v___x_1118_);
v___x_1120_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1104_, v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg___boxed(lean_object* v_m_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1121_, v_a_1122_);
lean_dec(v_a_1122_);
lean_dec_ref(v_m_1121_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(lean_object* v_a_1124_, lean_object* v_b_1125_, lean_object* v_x_1126_){
_start:
{
if (lean_obj_tag(v_x_1126_) == 0)
{
lean_dec(v_b_1125_);
lean_dec(v_a_1124_);
return v_x_1126_;
}
else
{
lean_object* v_key_1127_; lean_object* v_value_1128_; lean_object* v_tail_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1141_; 
v_key_1127_ = lean_ctor_get(v_x_1126_, 0);
v_value_1128_ = lean_ctor_get(v_x_1126_, 1);
v_tail_1129_ = lean_ctor_get(v_x_1126_, 2);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_x_1126_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1131_ = v_x_1126_;
v_isShared_1132_ = v_isSharedCheck_1141_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_tail_1129_);
lean_inc(v_value_1128_);
lean_inc(v_key_1127_);
lean_dec(v_x_1126_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1141_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
uint8_t v___x_1133_; 
v___x_1133_ = lean_nat_dec_eq(v_key_1127_, v_a_1124_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1134_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1124_, v_b_1125_, v_tail_1129_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 2, v___x_1134_);
v___x_1136_ = v___x_1131_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_key_1127_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_value_1128_);
lean_ctor_set(v_reuseFailAlloc_1137_, 2, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
else
{
lean_object* v___x_1139_; 
lean_dec(v_value_1128_);
lean_dec(v_key_1127_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 1, v_b_1125_);
lean_ctor_set(v___x_1131_, 0, v_a_1124_);
v___x_1139_ = v___x_1131_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1124_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_b_1125_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v_tail_1129_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3___redArg(lean_object* v_m_1142_, lean_object* v_a_1143_, lean_object* v_b_1144_){
_start:
{
lean_object* v_size_1145_; lean_object* v_buckets_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1189_; 
v_size_1145_ = lean_ctor_get(v_m_1142_, 0);
v_buckets_1146_ = lean_ctor_get(v_m_1142_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_m_1142_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1148_ = v_m_1142_;
v_isShared_1149_ = v_isSharedCheck_1189_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_buckets_1146_);
lean_inc(v_size_1145_);
lean_dec(v_m_1142_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1189_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; uint64_t v___x_1151_; uint64_t v___x_1152_; uint64_t v___x_1153_; uint64_t v_fold_1154_; uint64_t v___x_1155_; uint64_t v___x_1156_; uint64_t v___x_1157_; size_t v___x_1158_; size_t v___x_1159_; size_t v___x_1160_; size_t v___x_1161_; size_t v___x_1162_; lean_object* v_bkt_1163_; uint8_t v___x_1164_; 
v___x_1150_ = lean_array_get_size(v_buckets_1146_);
v___x_1151_ = lean_uint64_of_nat(v_a_1143_);
v___x_1152_ = 32ULL;
v___x_1153_ = lean_uint64_shift_right(v___x_1151_, v___x_1152_);
v_fold_1154_ = lean_uint64_xor(v___x_1151_, v___x_1153_);
v___x_1155_ = 16ULL;
v___x_1156_ = lean_uint64_shift_right(v_fold_1154_, v___x_1155_);
v___x_1157_ = lean_uint64_xor(v_fold_1154_, v___x_1156_);
v___x_1158_ = lean_uint64_to_usize(v___x_1157_);
v___x_1159_ = lean_usize_of_nat(v___x_1150_);
v___x_1160_ = ((size_t)1ULL);
v___x_1161_ = lean_usize_sub(v___x_1159_, v___x_1160_);
v___x_1162_ = lean_usize_land(v___x_1158_, v___x_1161_);
v_bkt_1163_ = lean_array_uget_borrowed(v_buckets_1146_, v___x_1162_);
v___x_1164_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1143_, v_bkt_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v_size_x27_1166_; lean_object* v___x_1167_; lean_object* v_buckets_x27_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1165_ = lean_unsigned_to_nat(1u);
v_size_x27_1166_ = lean_nat_add(v_size_1145_, v___x_1165_);
lean_dec(v_size_1145_);
lean_inc(v_bkt_1163_);
v___x_1167_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1167_, 0, v_a_1143_);
lean_ctor_set(v___x_1167_, 1, v_b_1144_);
lean_ctor_set(v___x_1167_, 2, v_bkt_1163_);
v_buckets_x27_1168_ = lean_array_uset(v_buckets_1146_, v___x_1162_, v___x_1167_);
v___x_1169_ = lean_unsigned_to_nat(4u);
v___x_1170_ = lean_nat_mul(v_size_x27_1166_, v___x_1169_);
v___x_1171_ = lean_unsigned_to_nat(3u);
v___x_1172_ = lean_nat_div(v___x_1170_, v___x_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_array_get_size(v_buckets_x27_1168_);
v___x_1174_ = lean_nat_dec_le(v___x_1172_, v___x_1173_);
lean_dec(v___x_1172_);
if (v___x_1174_ == 0)
{
lean_object* v_val_1175_; lean_object* v___x_1177_; 
v_val_1175_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_1168_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v_val_1175_);
lean_ctor_set(v___x_1148_, 0, v_size_x27_1166_);
v___x_1177_ = v___x_1148_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_size_x27_1166_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_val_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
else
{
lean_object* v___x_1180_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v_buckets_x27_1168_);
lean_ctor_set(v___x_1148_, 0, v_size_x27_1166_);
v___x_1180_ = v___x_1148_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_size_x27_1166_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_buckets_x27_1168_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
else
{
lean_object* v___x_1182_; lean_object* v_buckets_x27_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
lean_inc(v_bkt_1163_);
v___x_1182_ = lean_box(0);
v_buckets_x27_1183_ = lean_array_uset(v_buckets_1146_, v___x_1162_, v___x_1182_);
v___x_1184_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1143_, v_b_1144_, v_bkt_1163_);
v___x_1185_ = lean_array_uset(v_buckets_x27_1183_, v___x_1162_, v___x_1184_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v___x_1185_);
v___x_1187_ = v___x_1148_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_size_1145_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__5(lean_object* v_snd_1190_, lean_object* v_x_1191_, lean_object* v_x_1192_){
_start:
{
if (lean_obj_tag(v_x_1192_) == 0)
{
return v_x_1191_;
}
else
{
lean_object* v_key_1193_; lean_object* v_value_1194_; lean_object* v_tail_1195_; lean_object* v___y_1197_; lean_object* v___x_1200_; 
v_key_1193_ = lean_ctor_get(v_x_1192_, 0);
lean_inc(v_key_1193_);
v_value_1194_ = lean_ctor_get(v_x_1192_, 1);
lean_inc(v_value_1194_);
v_tail_1195_ = lean_ctor_get(v_x_1192_, 2);
lean_inc(v_tail_1195_);
lean_dec_ref(v_x_1192_);
v___x_1200_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg(v_snd_1190_, v_key_1193_);
if (lean_obj_tag(v___x_1200_) == 1)
{
lean_object* v_val_1201_; uint8_t v___x_1202_; 
v_val_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_val_1201_);
lean_dec_ref(v___x_1200_);
v___x_1202_ = lean_nat_dec_le(v_value_1194_, v_val_1201_);
if (v___x_1202_ == 0)
{
lean_dec(v_value_1194_);
v___y_1197_ = v_val_1201_;
goto v___jp_1196_;
}
else
{
lean_dec(v_val_1201_);
v___y_1197_ = v_value_1194_;
goto v___jp_1196_;
}
}
else
{
lean_dec(v___x_1200_);
lean_dec(v_value_1194_);
lean_dec(v_key_1193_);
v_x_1192_ = v_tail_1195_;
goto _start;
}
v___jp_1196_:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3___redArg(v_x_1191_, v_key_1193_, v___y_1197_);
v_x_1191_ = v___x_1198_;
v_x_1192_ = v_tail_1195_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__5___boxed(lean_object* v_snd_1204_, lean_object* v_x_1205_, lean_object* v_x_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__5(v_snd_1204_, v_x_1205_, v_x_1206_);
lean_dec_ref(v_snd_1204_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6(lean_object* v_snd_1208_, lean_object* v_as_1209_, size_t v_i_1210_, size_t v_stop_1211_, lean_object* v_b_1212_){
_start:
{
uint8_t v___x_1213_; 
v___x_1213_ = lean_usize_dec_eq(v_i_1210_, v_stop_1211_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; lean_object* v___x_1215_; size_t v___x_1216_; size_t v___x_1217_; 
v___x_1214_ = lean_array_uget_borrowed(v_as_1209_, v_i_1210_);
lean_inc(v___x_1214_);
v___x_1215_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__5(v_snd_1208_, v_b_1212_, v___x_1214_);
v___x_1216_ = ((size_t)1ULL);
v___x_1217_ = lean_usize_add(v_i_1210_, v___x_1216_);
v_i_1210_ = v___x_1217_;
v_b_1212_ = v___x_1215_;
goto _start;
}
else
{
return v_b_1212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6___boxed(lean_object* v_snd_1219_, lean_object* v_as_1220_, lean_object* v_i_1221_, lean_object* v_stop_1222_, lean_object* v_b_1223_){
_start:
{
size_t v_i_boxed_1224_; size_t v_stop_boxed_1225_; lean_object* v_res_1226_; 
v_i_boxed_1224_ = lean_unbox_usize(v_i_1221_);
lean_dec(v_i_1221_);
v_stop_boxed_1225_ = lean_unbox_usize(v_stop_1222_);
lean_dec(v_stop_1222_);
v_res_1226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6(v_snd_1219_, v_as_1220_, v_i_boxed_1224_, v_stop_boxed_1225_, v_b_1223_);
lean_dec_ref(v_as_1220_);
lean_dec_ref(v_snd_1219_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(lean_object* v_x_1227_, lean_object* v_y_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v___y_1232_; lean_object* v_fst_1233_; lean_object* v_snd_1234_; lean_object* v_size_1238_; lean_object* v_buckets_1239_; lean_object* v_size_1240_; lean_object* v_buckets_1241_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1248_; lean_object* v_buckets_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v_buckets_1266_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v_fst_1283_; lean_object* v_buckets_1284_; lean_object* v_snd_1285_; uint8_t v___x_1298_; 
v_size_1238_ = lean_ctor_get(v_y_1228_, 0);
lean_inc(v_size_1238_);
v_buckets_1239_ = lean_ctor_get(v_y_1228_, 1);
v_size_1240_ = lean_ctor_get(v_x_1227_, 0);
lean_inc(v_size_1240_);
v_buckets_1241_ = lean_ctor_get(v_x_1227_, 1);
v___x_1298_ = lean_nat_dec_lt(v_size_1238_, v_size_1240_);
if (v___x_1298_ == 0)
{
lean_inc_ref(v_buckets_1241_);
v_fst_1283_ = v_x_1227_;
v_buckets_1284_ = v_buckets_1241_;
v_snd_1285_ = v_y_1228_;
goto v___jp_1282_;
}
else
{
lean_inc_ref(v_buckets_1239_);
v_fst_1283_ = v_y_1228_;
v_buckets_1284_ = v_buckets_1239_;
v_snd_1285_ = v_x_1227_;
goto v___jp_1282_;
}
v___jp_1231_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1235_, 0, v___y_1232_);
lean_ctor_set(v___x_1235_, 1, v_fst_1233_);
lean_ctor_set(v___x_1235_, 2, v_snd_1234_);
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
lean_ctor_set(v___x_1236_, 1, v_a_1229_);
v___x_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
return v___x_1237_;
}
v___jp_1242_:
{
uint8_t v___x_1246_; 
v___x_1246_ = lean_nat_dec_lt(v_size_1238_, v_size_1240_);
lean_dec(v_size_1240_);
lean_dec(v_size_1238_);
if (v___x_1246_ == 0)
{
v___y_1232_ = v___y_1243_;
v_fst_1233_ = v___y_1244_;
v_snd_1234_ = v___y_1245_;
goto v___jp_1231_;
}
else
{
v___y_1232_ = v___y_1243_;
v_fst_1233_ = v___y_1245_;
v_snd_1234_ = v___y_1244_;
goto v___jp_1231_;
}
}
v___jp_1247_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1252_ = lean_unsigned_to_nat(0u);
v___x_1253_ = lean_array_get_size(v_buckets_1249_);
v___x_1254_ = lean_nat_dec_lt(v___x_1252_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_dec_ref(v_buckets_1249_);
v___y_1243_ = v___y_1248_;
v___y_1244_ = v___y_1251_;
v___y_1245_ = v___y_1250_;
goto v___jp_1242_;
}
else
{
uint8_t v___x_1255_; 
v___x_1255_ = lean_nat_dec_le(v___x_1253_, v___x_1253_);
if (v___x_1255_ == 0)
{
if (v___x_1254_ == 0)
{
lean_dec_ref(v_buckets_1249_);
v___y_1243_ = v___y_1248_;
v___y_1244_ = v___y_1251_;
v___y_1245_ = v___y_1250_;
goto v___jp_1242_;
}
else
{
size_t v___x_1256_; size_t v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = ((size_t)0ULL);
v___x_1257_ = lean_usize_of_nat(v___x_1253_);
v___x_1258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1249_, v___x_1256_, v___x_1257_, v___y_1250_);
lean_dec_ref(v_buckets_1249_);
v___y_1243_ = v___y_1248_;
v___y_1244_ = v___y_1251_;
v___y_1245_ = v___x_1258_;
goto v___jp_1242_;
}
}
else
{
size_t v___x_1259_; size_t v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = ((size_t)0ULL);
v___x_1260_ = lean_usize_of_nat(v___x_1253_);
v___x_1261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1249_, v___x_1259_, v___x_1260_, v___y_1250_);
lean_dec_ref(v_buckets_1249_);
v___y_1243_ = v___y_1248_;
v___y_1244_ = v___y_1251_;
v___y_1245_ = v___x_1261_;
goto v___jp_1242_;
}
}
}
v___jp_1262_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = lean_array_get_size(v_buckets_1266_);
v___x_1269_ = lean_nat_dec_lt(v___x_1267_, v___x_1268_);
if (v___x_1269_ == 0)
{
v___y_1248_ = v___y_1265_;
v_buckets_1249_ = v_buckets_1266_;
v___y_1250_ = v___y_1264_;
v___y_1251_ = v___y_1263_;
goto v___jp_1247_;
}
else
{
uint8_t v___x_1270_; 
v___x_1270_ = lean_nat_dec_le(v___x_1268_, v___x_1268_);
if (v___x_1270_ == 0)
{
if (v___x_1269_ == 0)
{
v___y_1248_ = v___y_1265_;
v_buckets_1249_ = v_buckets_1266_;
v___y_1250_ = v___y_1264_;
v___y_1251_ = v___y_1263_;
goto v___jp_1247_;
}
else
{
size_t v___x_1271_; size_t v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = ((size_t)0ULL);
v___x_1272_ = lean_usize_of_nat(v___x_1268_);
v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1266_, v___x_1271_, v___x_1272_, v___y_1263_);
v___y_1248_ = v___y_1265_;
v_buckets_1249_ = v_buckets_1266_;
v___y_1250_ = v___y_1264_;
v___y_1251_ = v___x_1273_;
goto v___jp_1247_;
}
}
else
{
size_t v___x_1274_; size_t v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = ((size_t)0ULL);
v___x_1275_ = lean_usize_of_nat(v___x_1268_);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1266_, v___x_1274_, v___x_1275_, v___y_1263_);
v___y_1248_ = v___y_1265_;
v_buckets_1249_ = v_buckets_1266_;
v___y_1250_ = v___y_1264_;
v___y_1251_ = v___x_1276_;
goto v___jp_1247_;
}
}
}
v___jp_1277_:
{
lean_object* v_buckets_1281_; 
v_buckets_1281_ = lean_ctor_get(v___y_1280_, 1);
lean_inc_ref(v_buckets_1281_);
v___y_1263_ = v___y_1278_;
v___y_1264_ = v___y_1279_;
v___y_1265_ = v___y_1280_;
v_buckets_1266_ = v_buckets_1281_;
goto v___jp_1262_;
}
v___jp_1282_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1286_ = lean_unsigned_to_nat(0u);
v___x_1287_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1288_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1289_ = lean_array_get_size(v_buckets_1284_);
v___x_1290_ = lean_nat_dec_lt(v___x_1286_, v___x_1289_);
if (v___x_1290_ == 0)
{
lean_dec_ref(v_buckets_1284_);
v___y_1263_ = v_fst_1283_;
v___y_1264_ = v_snd_1285_;
v___y_1265_ = v___x_1288_;
v_buckets_1266_ = v___x_1287_;
goto v___jp_1262_;
}
else
{
uint8_t v___x_1291_; 
v___x_1291_ = lean_nat_dec_le(v___x_1289_, v___x_1289_);
if (v___x_1291_ == 0)
{
if (v___x_1290_ == 0)
{
lean_dec_ref(v_buckets_1284_);
v___y_1263_ = v_fst_1283_;
v___y_1264_ = v_snd_1285_;
v___y_1265_ = v___x_1288_;
v_buckets_1266_ = v___x_1287_;
goto v___jp_1262_;
}
else
{
size_t v___x_1292_; size_t v___x_1293_; lean_object* v___x_1294_; 
v___x_1292_ = ((size_t)0ULL);
v___x_1293_ = lean_usize_of_nat(v___x_1289_);
v___x_1294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6(v_snd_1285_, v_buckets_1284_, v___x_1292_, v___x_1293_, v___x_1288_);
lean_dec_ref(v_buckets_1284_);
v___y_1278_ = v_fst_1283_;
v___y_1279_ = v_snd_1285_;
v___y_1280_ = v___x_1294_;
goto v___jp_1277_;
}
}
else
{
size_t v___x_1295_; size_t v___x_1296_; lean_object* v___x_1297_; 
v___x_1295_ = ((size_t)0ULL);
v___x_1296_ = lean_usize_of_nat(v___x_1289_);
v___x_1297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6(v_snd_1285_, v_buckets_1284_, v___x_1295_, v___x_1296_, v___x_1288_);
lean_dec_ref(v_buckets_1284_);
v___y_1278_ = v_fst_1283_;
v___y_1279_ = v_snd_1285_;
v___y_1280_ = v___x_1297_;
goto v___jp_1277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg___boxed(lean_object* v_x_1299_, lean_object* v_y_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(v_x_1299_, v_y_1300_, v_a_1301_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute(lean_object* v_x_1304_, lean_object* v_y_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(v_x_1304_, v_y_1305_, v_a_1306_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___boxed(lean_object* v_x_1313_, lean_object* v_y_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute(v_x_1313_, v_y_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3(lean_object* v_00_u03b2_1322_, lean_object* v_m_1323_, lean_object* v_a_1324_, lean_object* v_b_1325_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3___redArg(v_m_1323_, v_a_1324_, v_b_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4(lean_object* v_00_u03b2_1327_, lean_object* v_m_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1328_, v_a_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___boxed(lean_object* v_00_u03b2_1331_, lean_object* v_m_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4(v_00_u03b2_1331_, v_m_1332_, v_a_1333_);
lean_dec(v_a_1333_);
lean_dec_ref(v_m_1332_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5(lean_object* v_00_u03b2_1335_, lean_object* v_a_1336_, lean_object* v_b_1337_, lean_object* v_x_1338_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1336_, v_b_1337_, v_x_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7(lean_object* v_00_u03b2_1340_, lean_object* v_a_1341_, lean_object* v_x_1342_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1341_, v_x_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1344_, lean_object* v_a_1345_, lean_object* v_x_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7(v_00_u03b2_1344_, v_a_1345_, v_x_1346_);
lean_dec(v_x_1346_);
lean_dec(v_a_1345_);
return v_res_1347_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(lean_object* v_x1_1348_, lean_object* v_x2_1349_){
_start:
{
lean_object* v_fst_1350_; lean_object* v_fst_1351_; uint8_t v___x_1352_; 
v_fst_1350_ = lean_ctor_get(v_x1_1348_, 0);
v_fst_1351_ = lean_ctor_get(v_x2_1349_, 0);
v___x_1352_ = lean_nat_dec_lt(v_fst_1350_, v_fst_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed(lean_object* v_x1_1353_, lean_object* v_x2_1354_){
_start:
{
uint8_t v_res_1355_; lean_object* v_r_1356_; 
v_res_1355_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v_x1_1353_, v_x2_1354_);
lean_dec_ref(v_x2_1354_);
lean_dec_ref(v_x1_1353_);
v_r_1356_ = lean_box(v_res_1355_);
return v_r_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(lean_object* v_as_1358_, lean_object* v_lo_1359_, lean_object* v_hi_1360_){
_start:
{
uint8_t v___x_1361_; 
v___x_1361_ = lean_nat_dec_lt(v_lo_1359_, v_hi_1360_);
if (v___x_1361_ == 0)
{
lean_dec(v_lo_1359_);
return v_as_1358_;
}
else
{
lean_object* v___f_1362_; lean_object* v___x_1363_; lean_object* v_fst_1364_; lean_object* v_snd_1365_; uint8_t v___x_1366_; 
v___f_1362_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___closed__0));
lean_inc(v_lo_1359_);
v___x_1363_ = l_Array_qpartition___redArg(v_as_1358_, v___f_1362_, v_lo_1359_, v_hi_1360_);
v_fst_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_fst_1364_);
v_snd_1365_ = lean_ctor_get(v___x_1363_, 1);
lean_inc(v_snd_1365_);
lean_dec_ref(v___x_1363_);
v___x_1366_ = lean_nat_dec_le(v_hi_1360_, v_fst_1364_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1367_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_snd_1365_, v_lo_1359_, v_fst_1364_);
v___x_1368_ = lean_unsigned_to_nat(1u);
v___x_1369_ = lean_nat_add(v_fst_1364_, v___x_1368_);
lean_dec(v_fst_1364_);
v_as_1358_ = v___x_1367_;
v_lo_1359_ = v___x_1369_;
goto _start;
}
else
{
lean_dec(v_fst_1364_);
lean_dec(v_lo_1359_);
return v_snd_1365_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___boxed(lean_object* v_as_1371_, lean_object* v_lo_1372_, lean_object* v_hi_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_as_1371_, v_lo_1372_, v_hi_1373_);
lean_dec(v_hi_1373_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg(lean_object* v_upperBound_1375_, lean_object* v___x_1376_, lean_object* v_op_1377_, lean_object* v_a_1378_, lean_object* v_b_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v___y_1383_; uint8_t v___x_1387_; 
v___x_1387_ = lean_nat_dec_lt(v_a_1378_, v_upperBound_1375_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec(v_a_1378_);
lean_dec_ref(v_op_1377_);
lean_dec_ref(v___x_1376_);
v___x_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1388_, 0, v_b_1379_);
lean_ctor_set(v___x_1388_, 1, v___y_1380_);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
else
{
if (lean_obj_tag(v_b_1379_) == 0)
{
lean_object* v___x_1390_; 
lean_inc_ref(v___x_1376_);
v___x_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1376_);
v___y_1383_ = v___x_1390_;
goto v___jp_1382_;
}
else
{
lean_object* v_val_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1400_; 
v_val_1391_ = lean_ctor_get(v_b_1379_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_b_1379_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1393_ = v_b_1379_;
v_isShared_1394_ = v_isSharedCheck_1400_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_val_1391_);
lean_dec(v_b_1379_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1400_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
lean_inc_ref(v_op_1377_);
v___x_1395_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_op_1377_);
lean_inc_ref(v___x_1376_);
v___x_1396_ = l_Lean_mkAppB(v___x_1395_, v_val_1391_, v___x_1376_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1396_);
v___x_1398_ = v___x_1393_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
v___y_1383_ = v___x_1398_;
goto v___jp_1382_;
}
}
}
}
v___jp_1382_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_unsigned_to_nat(1u);
v___x_1385_ = lean_nat_add(v_a_1378_, v___x_1384_);
lean_dec(v_a_1378_);
v_a_1378_ = v___x_1385_;
v_b_1379_ = v___y_1383_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg___boxed(lean_object* v_upperBound_1401_, lean_object* v___x_1402_, lean_object* v_op_1403_, lean_object* v_a_1404_, lean_object* v_b_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1401_, v___x_1402_, v_op_1403_, v_a_1404_, v_b_1405_, v___y_1406_);
lean_dec(v_upperBound_1401_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__1(lean_object* v_op_1409_, lean_object* v_as_1410_, size_t v_sz_1411_, size_t v_i_1412_, lean_object* v_b_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
uint8_t v___x_1420_; 
v___x_1420_ = lean_usize_dec_lt(v_i_1412_, v_sz_1411_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_dec_ref(v_op_1409_);
v___x_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1421_, 0, v_b_1413_);
lean_ctor_set(v___x_1421_, 1, v___y_1414_);
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
return v___x_1422_;
}
else
{
lean_object* v_a_1423_; lean_object* v_fst_1424_; lean_object* v_snd_1425_; lean_object* v_varToExpr_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v_a_1423_ = lean_array_uget_borrowed(v_as_1410_, v_i_1412_);
v_fst_1424_ = lean_ctor_get(v_a_1423_, 0);
v_snd_1425_ = lean_ctor_get(v_a_1423_, 1);
v_varToExpr_1426_ = lean_ctor_get(v___y_1414_, 2);
v___x_1427_ = l_Lean_instInhabitedExpr;
v___x_1428_ = lean_unsigned_to_nat(0u);
v___x_1429_ = lean_array_get(v___x_1427_, v_varToExpr_1426_, v_fst_1424_);
lean_inc_ref(v_op_1409_);
v___x_1430_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_snd_1425_, v___x_1429_, v_op_1409_, v___x_1428_, v_b_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v_fst_1432_; lean_object* v_snd_1433_; size_t v___x_1434_; size_t v___x_1435_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref(v___x_1430_);
v_fst_1432_ = lean_ctor_get(v_a_1431_, 0);
lean_inc(v_fst_1432_);
v_snd_1433_ = lean_ctor_get(v_a_1431_, 1);
lean_inc(v_snd_1433_);
lean_dec(v_a_1431_);
v___x_1434_ = ((size_t)1ULL);
v___x_1435_ = lean_usize_add(v_i_1412_, v___x_1434_);
v_i_1412_ = v___x_1435_;
v_b_1413_ = v_fst_1432_;
v___y_1414_ = v_snd_1433_;
goto _start;
}
else
{
lean_dec_ref(v_op_1409_);
return v___x_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__1___boxed(lean_object* v_op_1437_, lean_object* v_as_1438_, lean_object* v_sz_1439_, lean_object* v_i_1440_, lean_object* v_b_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
size_t v_sz_boxed_1448_; size_t v_i_boxed_1449_; lean_object* v_res_1450_; 
v_sz_boxed_1448_ = lean_unbox_usize(v_sz_1439_);
lean_dec(v_sz_1439_);
v_i_boxed_1449_ = lean_unbox_usize(v_i_1440_);
lean_dec(v_i_1440_);
v_res_1450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1437_, v_as_1438_, v_sz_boxed_1448_, v_i_boxed_1449_, v_b_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec_ref(v_as_1438_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__3(lean_object* v_x_1451_, lean_object* v_x_1452_){
_start:
{
if (lean_obj_tag(v_x_1452_) == 0)
{
return v_x_1451_;
}
else
{
lean_object* v_key_1453_; lean_object* v_value_1454_; lean_object* v_tail_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v_key_1453_ = lean_ctor_get(v_x_1452_, 0);
v_value_1454_ = lean_ctor_get(v_x_1452_, 1);
v_tail_1455_ = lean_ctor_get(v_x_1452_, 2);
lean_inc(v_value_1454_);
lean_inc(v_key_1453_);
v___x_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1456_, 0, v_key_1453_);
lean_ctor_set(v___x_1456_, 1, v_value_1454_);
v___x_1457_ = lean_array_push(v_x_1451_, v___x_1456_);
v_x_1451_ = v___x_1457_;
v_x_1452_ = v_tail_1455_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__3___boxed(lean_object* v_x_1459_, lean_object* v_x_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__3(v_x_1459_, v_x_1460_);
lean_dec(v_x_1460_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4(lean_object* v_as_1462_, size_t v_i_1463_, size_t v_stop_1464_, lean_object* v_b_1465_){
_start:
{
uint8_t v___x_1466_; 
v___x_1466_ = lean_usize_dec_eq(v_i_1463_, v_stop_1464_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1468_; size_t v___x_1469_; size_t v___x_1470_; 
v___x_1467_ = lean_array_uget_borrowed(v_as_1462_, v_i_1463_);
v___x_1468_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__3(v_b_1465_, v___x_1467_);
v___x_1469_ = ((size_t)1ULL);
v___x_1470_ = lean_usize_add(v_i_1463_, v___x_1469_);
v_i_1463_ = v___x_1470_;
v_b_1465_ = v___x_1468_;
goto _start;
}
else
{
return v_b_1465_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4___boxed(lean_object* v_as_1472_, lean_object* v_i_1473_, lean_object* v_stop_1474_, lean_object* v_b_1475_){
_start:
{
size_t v_i_boxed_1476_; size_t v_stop_boxed_1477_; lean_object* v_res_1478_; 
v_i_boxed_1476_ = lean_unbox_usize(v_i_1473_);
lean_dec(v_i_1473_);
v_stop_boxed_1477_ = lean_unbox_usize(v_stop_1474_);
lean_dec(v_stop_1474_);
v_res_1478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4(v_as_1472_, v_i_boxed_1476_, v_stop_boxed_1477_, v_b_1475_);
lean_dec_ref(v_as_1472_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(lean_object* v_coeff_1479_, lean_object* v_op_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v___y_1488_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1506_; lean_object* v_size_1513_; lean_object* v_buckets_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; 
v_size_1513_ = lean_ctor_get(v_coeff_1479_, 0);
v_buckets_1514_ = lean_ctor_get(v_coeff_1479_, 1);
v___x_1515_ = lean_mk_empty_array_with_capacity(v_size_1513_);
v___x_1516_ = lean_unsigned_to_nat(0u);
v___x_1517_ = lean_array_get_size(v_buckets_1514_);
v___x_1518_ = lean_nat_dec_lt(v___x_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
v___y_1506_ = v___x_1515_;
goto v___jp_1505_;
}
else
{
uint8_t v___x_1519_; 
v___x_1519_ = lean_nat_dec_le(v___x_1517_, v___x_1517_);
if (v___x_1519_ == 0)
{
if (v___x_1518_ == 0)
{
v___y_1506_ = v___x_1515_;
goto v___jp_1505_;
}
else
{
size_t v___x_1520_; size_t v___x_1521_; lean_object* v___x_1522_; 
v___x_1520_ = ((size_t)0ULL);
v___x_1521_ = lean_usize_of_nat(v___x_1517_);
v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4(v_buckets_1514_, v___x_1520_, v___x_1521_, v___x_1515_);
v___y_1506_ = v___x_1522_;
goto v___jp_1505_;
}
}
else
{
size_t v___x_1523_; size_t v___x_1524_; lean_object* v___x_1525_; 
v___x_1523_ = ((size_t)0ULL);
v___x_1524_ = lean_usize_of_nat(v___x_1517_);
v___x_1525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4(v_buckets_1514_, v___x_1523_, v___x_1524_, v___x_1515_);
v___y_1506_ = v___x_1525_;
goto v___jp_1505_;
}
}
v___jp_1487_:
{
lean_object* v_acc_1489_; size_t v_sz_1490_; size_t v___x_1491_; lean_object* v___x_1492_; 
v_acc_1489_ = lean_box(0);
v_sz_1490_ = lean_array_size(v___y_1488_);
v___x_1491_ = ((size_t)0ULL);
v___x_1492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1480_, v___y_1488_, v_sz_1490_, v___x_1491_, v_acc_1489_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
lean_dec_ref(v___y_1488_);
return v___x_1492_;
}
v___jp_1493_:
{
lean_object* v___x_1498_; 
lean_dec(v___y_1496_);
v___x_1498_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v___y_1494_, v___y_1495_, v___y_1497_);
lean_dec(v___y_1497_);
v___y_1488_ = v___x_1498_;
goto v___jp_1487_;
}
v___jp_1499_:
{
uint8_t v___x_1504_; 
v___x_1504_ = lean_nat_dec_le(v___y_1503_, v___y_1501_);
if (v___x_1504_ == 0)
{
lean_dec(v___y_1501_);
lean_inc(v___y_1503_);
v___y_1494_ = v___y_1500_;
v___y_1495_ = v___y_1503_;
v___y_1496_ = v___y_1502_;
v___y_1497_ = v___y_1503_;
goto v___jp_1493_;
}
else
{
v___y_1494_ = v___y_1500_;
v___y_1495_ = v___y_1503_;
v___y_1496_ = v___y_1502_;
v___y_1497_ = v___y_1501_;
goto v___jp_1493_;
}
}
v___jp_1505_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
v___x_1507_ = lean_array_get_size(v___y_1506_);
v___x_1508_ = lean_unsigned_to_nat(0u);
v___x_1509_ = lean_nat_dec_eq(v___x_1507_, v___x_1508_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1510_ = lean_unsigned_to_nat(1u);
v___x_1511_ = lean_nat_sub(v___x_1507_, v___x_1510_);
v___x_1512_ = lean_nat_dec_le(v___x_1508_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_inc(v___x_1511_);
v___y_1500_ = v___y_1506_;
v___y_1501_ = v___x_1511_;
v___y_1502_ = v___x_1507_;
v___y_1503_ = v___x_1511_;
goto v___jp_1499_;
}
else
{
v___y_1500_ = v___y_1506_;
v___y_1501_ = v___x_1511_;
v___y_1502_ = v___x_1507_;
v___y_1503_ = v___x_1508_;
goto v___jp_1499_;
}
}
else
{
v___y_1488_ = v___y_1506_;
goto v___jp_1487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr___boxed(lean_object* v_coeff_1526_, lean_object* v_op_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_coeff_1526_, v_op_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
lean_dec_ref(v_coeff_1526_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0(lean_object* v_upperBound_1535_, lean_object* v___x_1536_, lean_object* v_op_1537_, lean_object* v_inst_1538_, lean_object* v_R_1539_, lean_object* v_a_1540_, lean_object* v_b_1541_, lean_object* v_c_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1535_, v___x_1536_, v_op_1537_, v_a_1540_, v_b_1541_, v___y_1543_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___boxed(lean_object* v_upperBound_1550_, lean_object* v___x_1551_, lean_object* v_op_1552_, lean_object* v_inst_1553_, lean_object* v_R_1554_, lean_object* v_a_1555_, lean_object* v_b_1556_, lean_object* v_c_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0(v_upperBound_1550_, v___x_1551_, v_op_1552_, v_inst_1553_, v_R_1554_, v_a_1555_, v_b_1556_, v_c_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v_upperBound_1550_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2(lean_object* v_n_1565_, lean_object* v_as_1566_, lean_object* v_lo_1567_, lean_object* v_hi_1568_, lean_object* v_w_1569_, lean_object* v_hlo_1570_, lean_object* v_hhi_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_as_1566_, v_lo_1567_, v_hi_1568_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___boxed(lean_object* v_n_1573_, lean_object* v_as_1574_, lean_object* v_lo_1575_, lean_object* v_hi_1576_, lean_object* v_w_1577_, lean_object* v_hlo_1578_, lean_object* v_hhi_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2(v_n_1573_, v_as_1574_, v_lo_1575_, v_hi_1576_, v_w_1577_, v_hlo_1578_, v_hhi_1579_);
lean_dec(v_hi_1576_);
lean_dec(v_n_1573_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(lean_object* v_e_1581_, lean_object* v___y_1582_){
_start:
{
uint8_t v___x_1584_; 
v___x_1584_ = l_Lean_Expr_hasMVar(v_e_1581_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v_e_1581_);
return v___x_1585_;
}
else
{
lean_object* v___x_1586_; lean_object* v_mctx_1587_; lean_object* v___x_1588_; lean_object* v_fst_1589_; lean_object* v_snd_1590_; lean_object* v___x_1591_; lean_object* v_cache_1592_; lean_object* v_zetaDeltaFVarIds_1593_; lean_object* v_postponed_1594_; lean_object* v_diag_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1604_; 
v___x_1586_ = lean_st_ref_get(v___y_1582_);
v_mctx_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc_ref(v_mctx_1587_);
lean_dec(v___x_1586_);
v___x_1588_ = l_Lean_instantiateMVarsCore(v_mctx_1587_, v_e_1581_);
v_fst_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_fst_1589_);
v_snd_1590_ = lean_ctor_get(v___x_1588_, 1);
lean_inc(v_snd_1590_);
lean_dec_ref(v___x_1588_);
v___x_1591_ = lean_st_ref_take(v___y_1582_);
v_cache_1592_ = lean_ctor_get(v___x_1591_, 1);
v_zetaDeltaFVarIds_1593_ = lean_ctor_get(v___x_1591_, 2);
v_postponed_1594_ = lean_ctor_get(v___x_1591_, 3);
v_diag_1595_ = lean_ctor_get(v___x_1591_, 4);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1604_ == 0)
{
lean_object* v_unused_1605_; 
v_unused_1605_ = lean_ctor_get(v___x_1591_, 0);
lean_dec(v_unused_1605_);
v___x_1597_ = v___x_1591_;
v_isShared_1598_ = v_isSharedCheck_1604_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_diag_1595_);
lean_inc(v_postponed_1594_);
lean_inc(v_zetaDeltaFVarIds_1593_);
lean_inc(v_cache_1592_);
lean_dec(v___x_1591_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1604_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v_snd_1590_);
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_snd_1590_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_cache_1592_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_zetaDeltaFVarIds_1593_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v_postponed_1594_);
lean_ctor_set(v_reuseFailAlloc_1603_, 4, v_diag_1595_);
v___x_1600_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = lean_st_ref_set(v___y_1582_, v___x_1600_);
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v_fst_1589_);
return v___x_1602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg___boxed(lean_object* v_e_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1606_, v___y_1607_);
lean_dec(v___y_1607_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0(lean_object* v_e_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1610_, v___y_1612_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___boxed(lean_object* v_e_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0(v_e_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC(lean_object* v_x_1624_, lean_object* v_y_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Meta_mkEq(v_x_1624_, v_y_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1654_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1654_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1654_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
lean_ctor_set_tag(v___x_1634_, 1);
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
uint8_t v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1638_ = 0;
v___x_1639_ = lean_box(0);
v___x_1640_ = l_Lean_Meta_mkFreshExprMVar(v___x_1637_, v___x_1638_, v___x_1639_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref(v___x_1640_);
v___x_1642_ = l_Lean_Expr_mvarId_x21(v_a_1641_);
v___x_1643_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v___x_1642_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v___x_1644_; 
lean_dec_ref(v___x_1643_);
v___x_1644_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(v_a_1641_, v_a_1627_);
return v___x_1644_;
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_dec(v_a_1641_);
v_a_1645_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1643_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1643_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
else
{
return v___x_1640_;
}
}
}
}
else
{
return v___x_1631_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC___boxed(lean_object* v_x_1655_, lean_object* v_y_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC(v_x_1655_, v_y_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
lean_dec(v_a_1660_);
lean_dec_ref(v_a_1659_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
return v_res_1662_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = lean_unsigned_to_nat(32u);
v___x_1664_ = lean_mk_empty_array_with_capacity(v___x_1663_);
v___x_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
return v___x_1665_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1666_ = ((size_t)5ULL);
v___x_1667_ = lean_unsigned_to_nat(0u);
v___x_1668_ = lean_unsigned_to_nat(32u);
v___x_1669_ = lean_mk_empty_array_with_capacity(v___x_1668_);
v___x_1670_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0);
v___x_1671_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v___x_1669_);
lean_ctor_set(v___x_1671_, 2, v___x_1667_);
lean_ctor_set(v___x_1671_, 3, v___x_1667_);
lean_ctor_set_usize(v___x_1671_, 4, v___x_1666_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1674_; lean_object* v_traceState_1675_; lean_object* v_traces_1676_; lean_object* v___x_1677_; lean_object* v_traceState_1678_; lean_object* v_env_1679_; lean_object* v_nextMacroScope_1680_; lean_object* v_ngen_1681_; lean_object* v_auxDeclNGen_1682_; lean_object* v_cache_1683_; lean_object* v_messages_1684_; lean_object* v_infoState_1685_; lean_object* v_snapshotTasks_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1705_; 
v___x_1674_ = lean_st_ref_get(v___y_1672_);
v_traceState_1675_ = lean_ctor_get(v___x_1674_, 4);
lean_inc_ref(v_traceState_1675_);
lean_dec(v___x_1674_);
v_traces_1676_ = lean_ctor_get(v_traceState_1675_, 0);
lean_inc_ref(v_traces_1676_);
lean_dec_ref(v_traceState_1675_);
v___x_1677_ = lean_st_ref_take(v___y_1672_);
v_traceState_1678_ = lean_ctor_get(v___x_1677_, 4);
v_env_1679_ = lean_ctor_get(v___x_1677_, 0);
v_nextMacroScope_1680_ = lean_ctor_get(v___x_1677_, 1);
v_ngen_1681_ = lean_ctor_get(v___x_1677_, 2);
v_auxDeclNGen_1682_ = lean_ctor_get(v___x_1677_, 3);
v_cache_1683_ = lean_ctor_get(v___x_1677_, 5);
v_messages_1684_ = lean_ctor_get(v___x_1677_, 6);
v_infoState_1685_ = lean_ctor_get(v___x_1677_, 7);
v_snapshotTasks_1686_ = lean_ctor_get(v___x_1677_, 8);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1688_ = v___x_1677_;
v_isShared_1689_ = v_isSharedCheck_1705_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_snapshotTasks_1686_);
lean_inc(v_infoState_1685_);
lean_inc(v_messages_1684_);
lean_inc(v_cache_1683_);
lean_inc(v_traceState_1678_);
lean_inc(v_auxDeclNGen_1682_);
lean_inc(v_ngen_1681_);
lean_inc(v_nextMacroScope_1680_);
lean_inc(v_env_1679_);
lean_dec(v___x_1677_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1705_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
uint64_t v_tid_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1703_; 
v_tid_1690_ = lean_ctor_get_uint64(v_traceState_1678_, sizeof(void*)*1);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_traceState_1678_);
if (v_isSharedCheck_1703_ == 0)
{
lean_object* v_unused_1704_; 
v_unused_1704_ = lean_ctor_get(v_traceState_1678_, 0);
lean_dec(v_unused_1704_);
v___x_1692_ = v_traceState_1678_;
v_isShared_1693_ = v_isSharedCheck_1703_;
goto v_resetjp_1691_;
}
else
{
lean_dec(v_traceState_1678_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1703_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1694_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1694_);
v___x_1696_ = v___x_1692_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1694_);
lean_ctor_set_uint64(v_reuseFailAlloc_1702_, sizeof(void*)*1, v_tid_1690_);
v___x_1696_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1698_; 
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 4, v___x_1696_);
v___x_1698_ = v___x_1688_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_env_1679_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_nextMacroScope_1680_);
lean_ctor_set(v_reuseFailAlloc_1701_, 2, v_ngen_1681_);
lean_ctor_set(v_reuseFailAlloc_1701_, 3, v_auxDeclNGen_1682_);
lean_ctor_set(v_reuseFailAlloc_1701_, 4, v___x_1696_);
lean_ctor_set(v_reuseFailAlloc_1701_, 5, v_cache_1683_);
lean_ctor_set(v_reuseFailAlloc_1701_, 6, v_messages_1684_);
lean_ctor_set(v_reuseFailAlloc_1701_, 7, v_infoState_1685_);
lean_ctor_set(v_reuseFailAlloc_1701_, 8, v_snapshotTasks_1686_);
v___x_1698_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = lean_st_ref_set(v___y_1672_, v___x_1698_);
v___x_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1700_, 0, v_traces_1676_);
return v___x_1700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___boxed(lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1706_);
lean_dec(v___y_1706_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1(lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1715_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1(v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
return v_res_1726_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(lean_object* v_opts_1727_, lean_object* v_opt_1728_){
_start:
{
lean_object* v_name_1729_; lean_object* v_defValue_1730_; lean_object* v_map_1731_; lean_object* v___x_1732_; 
v_name_1729_ = lean_ctor_get(v_opt_1728_, 0);
v_defValue_1730_ = lean_ctor_get(v_opt_1728_, 1);
v_map_1731_ = lean_ctor_get(v_opts_1727_, 0);
v___x_1732_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1731_, v_name_1729_);
if (lean_obj_tag(v___x_1732_) == 0)
{
uint8_t v___x_1733_; 
v___x_1733_ = lean_unbox(v_defValue_1730_);
return v___x_1733_;
}
else
{
lean_object* v_val_1734_; 
v_val_1734_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_val_1734_);
lean_dec_ref(v___x_1732_);
if (lean_obj_tag(v_val_1734_) == 1)
{
uint8_t v_v_1735_; 
v_v_1735_ = lean_ctor_get_uint8(v_val_1734_, 0);
lean_dec_ref(v_val_1734_);
return v_v_1735_;
}
else
{
uint8_t v___x_1736_; 
lean_dec(v_val_1734_);
v___x_1736_ = lean_unbox(v_defValue_1730_);
return v___x_1736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object* v_opts_1737_, lean_object* v_opt_1738_){
_start:
{
uint8_t v_res_1739_; lean_object* v_r_1740_; 
v_res_1739_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(v_opts_1737_, v_opt_1738_);
lean_dec_ref(v_opt_1738_);
lean_dec_ref(v_opts_1737_);
v_r_1740_ = lean_box(v_res_1739_);
return v_r_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(lean_object* v_cls_1741_, lean_object* v_____do__lift_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_options_1751_; uint8_t v_hasTrace_1752_; 
v_options_1751_ = lean_ctor_get(v___y_1748_, 2);
v_hasTrace_1752_ = lean_ctor_get_uint8(v_options_1751_, sizeof(void*)*1);
if (v_hasTrace_1752_ == 0)
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec(v_cls_1741_);
v___x_1753_ = lean_box(v_hasTrace_1752_);
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
return v___x_1754_;
}
else
{
lean_object* v___x_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1755_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_1756_ = l_Lean_Name_append(v___x_1755_, v_cls_1741_);
v___x_1757_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_1742_, v_options_1751_, v___x_1756_);
lean_dec(v___x_1756_);
v___x_1758_ = lean_box(v___x_1757_);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
return v___x_1759_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0___boxed(lean_object* v_cls_1760_, lean_object* v_____do__lift_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_1760_, v_____do__lift_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v_____do__lift_1761_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__1(lean_object* v___x_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_mkAppB(v___x_1771_, v___y_1772_, v___y_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2(lean_object* v_val_1775_, lean_object* v_lhs_1776_, lean_object* v_rhs_1777_, lean_object* v_P_1778_, uint8_t v___x_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v___x_1786_; 
lean_inc_ref(v_lhs_1776_);
lean_inc_ref(v_val_1775_);
v___x_1786_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(v_val_1775_, v_lhs_1776_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v_fst_1788_; lean_object* v_snd_1789_; lean_object* v___x_1790_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref(v___x_1786_);
v_fst_1788_ = lean_ctor_get(v_a_1787_, 0);
lean_inc(v_fst_1788_);
v_snd_1789_ = lean_ctor_get(v_a_1787_, 1);
lean_inc(v_snd_1789_);
lean_dec(v_a_1787_);
lean_inc_ref(v_rhs_1777_);
lean_inc_ref(v_val_1775_);
v___x_1790_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(v_val_1775_, v_rhs_1777_, v_snd_1789_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v_fst_1792_; lean_object* v_snd_1793_; lean_object* v___x_1794_; lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1885_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref(v___x_1790_);
v_fst_1792_ = lean_ctor_get(v_a_1791_, 0);
lean_inc(v_fst_1792_);
v_snd_1793_ = lean_ctor_get(v_a_1791_, 1);
lean_inc(v_snd_1793_);
lean_dec(v_a_1791_);
v___x_1794_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(v_fst_1788_, v_fst_1792_, v_snd_1793_);
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1797_ = v___x_1794_;
v_isShared_1798_ = v_isSharedCheck_1885_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1794_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1885_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v_fst_1799_; lean_object* v_snd_1800_; lean_object* v_common_1801_; lean_object* v_x_1802_; lean_object* v_y_1803_; lean_object* v___x_1804_; 
v_fst_1799_ = lean_ctor_get(v_a_1795_, 0);
lean_inc(v_fst_1799_);
v_snd_1800_ = lean_ctor_get(v_a_1795_, 1);
lean_inc(v_snd_1800_);
lean_dec(v_a_1795_);
v_common_1801_ = lean_ctor_get(v_fst_1799_, 0);
lean_inc_ref(v_common_1801_);
v_x_1802_ = lean_ctor_get(v_fst_1799_, 1);
lean_inc_ref(v_x_1802_);
v_y_1803_ = lean_ctor_get(v_fst_1799_, 2);
lean_inc_ref(v_y_1803_);
lean_dec(v_fst_1799_);
lean_inc_ref(v_val_1775_);
v___x_1804_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_common_1801_, v_val_1775_, v_snd_1800_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec_ref(v_common_1801_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v_fst_1806_; lean_object* v_snd_1807_; lean_object* v___x_1808_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_a_1805_);
lean_dec_ref(v___x_1804_);
v_fst_1806_ = lean_ctor_get(v_a_1805_, 0);
lean_inc(v_fst_1806_);
v_snd_1807_ = lean_ctor_get(v_a_1805_, 1);
lean_inc(v_snd_1807_);
lean_dec(v_a_1805_);
lean_inc_ref(v_val_1775_);
v___x_1808_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_x_1802_, v_val_1775_, v_snd_1807_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec_ref(v_x_1802_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v_fst_1810_; lean_object* v_snd_1811_; lean_object* v___x_1812_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref(v___x_1808_);
v_fst_1810_ = lean_ctor_get(v_a_1809_, 0);
lean_inc(v_fst_1810_);
v_snd_1811_ = lean_ctor_get(v_a_1809_, 1);
lean_inc(v_snd_1811_);
lean_dec(v_a_1809_);
lean_inc_ref(v_val_1775_);
v___x_1812_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_y_1803_, v_val_1775_, v_snd_1811_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec_ref(v_y_1803_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v_fst_1814_; lean_object* v_snd_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1860_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1813_);
lean_dec_ref(v___x_1812_);
v_fst_1814_ = lean_ctor_get(v_a_1813_, 0);
v_snd_1815_ = lean_ctor_get(v_a_1813_, 1);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_a_1813_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1817_ = v_a_1813_;
v_isShared_1818_ = v_isSharedCheck_1860_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_snd_1815_);
lean_inc(v_fst_1814_);
lean_dec(v_a_1813_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1860_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___x_1850_; lean_object* v___f_1851_; lean_object* v___y_1853_; lean_object* v___x_1857_; 
lean_inc_ref(v_val_1775_);
v___x_1850_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_1775_);
v___f_1851_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_1851_, 0, v___x_1850_);
lean_inc(v_fst_1806_);
lean_inc_ref(v___f_1851_);
v___x_1857_ = l_Option_merge___redArg(v___f_1851_, v_fst_1806_, v_fst_1810_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v___x_1858_; 
lean_inc_ref(v_val_1775_);
v___x_1858_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_neutralElement(v_val_1775_);
v___y_1853_ = v___x_1858_;
goto v___jp_1852_;
}
else
{
lean_object* v_val_1859_; 
v_val_1859_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_val_1859_);
lean_dec_ref(v___x_1857_);
v___y_1853_ = v_val_1859_;
goto v___jp_1852_;
}
v___jp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_inc_ref(v_P_1778_);
v___x_1822_ = l_Lean_mkAppB(v_P_1778_, v_lhs_1776_, v_rhs_1777_);
v___x_1823_ = l_Lean_mkAppB(v_P_1778_, v___y_1820_, v___y_1821_);
lean_inc_ref(v___x_1823_);
v___x_1824_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC(v___x_1822_, v___x_1823_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1841_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1841_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1841_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set_tag(v___x_1797_, 1);
lean_ctor_set(v___x_1797_, 0, v_a_1825_);
v___x_1830_ = v___x_1797_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1831_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1831_, 0, v___x_1823_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*2, v___x_1779_);
v___x_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
v___x_1833_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1833_);
v___x_1835_ = v___x_1817_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1833_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_snd_1815_);
v___x_1835_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1837_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1835_);
v___x_1837_ = v___x_1827_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_dec_ref(v___x_1823_);
lean_del_object(v___x_1817_);
lean_dec(v_snd_1815_);
lean_del_object(v___x_1797_);
v_a_1842_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1824_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1824_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
v___jp_1852_:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Option_merge___redArg(v___f_1851_, v_fst_1806_, v_fst_1814_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_neutralElement(v_val_1775_);
v___y_1820_ = v___y_1853_;
v___y_1821_ = v___x_1855_;
goto v___jp_1819_;
}
else
{
lean_object* v_val_1856_; 
lean_dec_ref(v_val_1775_);
v_val_1856_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_val_1856_);
lean_dec_ref(v___x_1854_);
v___y_1820_ = v___y_1853_;
v___y_1821_ = v_val_1856_;
goto v___jp_1819_;
}
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_fst_1810_);
lean_dec(v_fst_1806_);
lean_del_object(v___x_1797_);
lean_dec_ref(v_P_1778_);
lean_dec_ref(v_rhs_1777_);
lean_dec_ref(v_lhs_1776_);
lean_dec_ref(v_val_1775_);
v_a_1861_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1812_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1812_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_fst_1806_);
lean_dec_ref(v_y_1803_);
lean_del_object(v___x_1797_);
lean_dec_ref(v_P_1778_);
lean_dec_ref(v_rhs_1777_);
lean_dec_ref(v_lhs_1776_);
lean_dec_ref(v_val_1775_);
v_a_1869_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1808_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1808_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec_ref(v_y_1803_);
lean_dec_ref(v_x_1802_);
lean_del_object(v___x_1797_);
lean_dec_ref(v_P_1778_);
lean_dec_ref(v_rhs_1777_);
lean_dec_ref(v_lhs_1776_);
lean_dec_ref(v_val_1775_);
v_a_1877_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1804_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1804_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec(v_fst_1788_);
lean_dec_ref(v_P_1778_);
lean_dec_ref(v_rhs_1777_);
lean_dec_ref(v_lhs_1776_);
lean_dec_ref(v_val_1775_);
v_a_1886_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1790_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1790_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec_ref(v_P_1778_);
lean_dec_ref(v_rhs_1777_);
lean_dec_ref(v_lhs_1776_);
lean_dec_ref(v_val_1775_);
v_a_1894_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1786_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1786_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object* v_val_1902_, lean_object* v_lhs_1903_, lean_object* v_rhs_1904_, lean_object* v_P_1905_, lean_object* v___x_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
uint8_t v___x_118078__boxed_1913_; lean_object* v_res_1914_; 
v___x_118078__boxed_1913_ = lean_unbox(v___x_1906_);
v_res_1914_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2(v_val_1902_, v_lhs_1903_, v_rhs_1904_, v_P_1905_, v___x_118078__boxed_1913_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
return v_res_1914_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_1917_ = l_Lean_stringToMessageData(v___x_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3(lean_object* v_x_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__1);
v___x_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object* v_x_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3(v_x_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v_x_1929_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__5(lean_object* v_val_1939_, lean_object* v_lhs_1940_, lean_object* v_rhs_1941_, lean_object* v_P_1942_, uint8_t v_hasTrace_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; 
lean_inc_ref(v_lhs_1940_);
lean_inc_ref(v_val_1939_);
v___x_1950_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(v_val_1939_, v_lhs_1940_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v_fst_1952_; lean_object* v_snd_1953_; lean_object* v___x_1954_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref(v___x_1950_);
v_fst_1952_ = lean_ctor_get(v_a_1951_, 0);
lean_inc(v_fst_1952_);
v_snd_1953_ = lean_ctor_get(v_a_1951_, 1);
lean_inc(v_snd_1953_);
lean_dec(v_a_1951_);
lean_inc_ref(v_rhs_1941_);
lean_inc_ref(v_val_1939_);
v___x_1954_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(v_val_1939_, v_rhs_1941_, v_snd_1953_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v_fst_1956_; lean_object* v_snd_1957_; lean_object* v___x_1958_; lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_2049_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
lean_dec_ref(v___x_1954_);
v_fst_1956_ = lean_ctor_get(v_a_1955_, 0);
lean_inc(v_fst_1956_);
v_snd_1957_ = lean_ctor_get(v_a_1955_, 1);
lean_inc(v_snd_1957_);
lean_dec(v_a_1955_);
v___x_1958_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(v_fst_1952_, v_fst_1956_, v_snd_1957_);
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_2049_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_2049_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v_fst_1963_; lean_object* v_snd_1964_; lean_object* v_common_1965_; lean_object* v_x_1966_; lean_object* v_y_1967_; lean_object* v___x_1968_; 
v_fst_1963_ = lean_ctor_get(v_a_1959_, 0);
lean_inc(v_fst_1963_);
v_snd_1964_ = lean_ctor_get(v_a_1959_, 1);
lean_inc(v_snd_1964_);
lean_dec(v_a_1959_);
v_common_1965_ = lean_ctor_get(v_fst_1963_, 0);
lean_inc_ref(v_common_1965_);
v_x_1966_ = lean_ctor_get(v_fst_1963_, 1);
lean_inc_ref(v_x_1966_);
v_y_1967_ = lean_ctor_get(v_fst_1963_, 2);
lean_inc_ref(v_y_1967_);
lean_dec(v_fst_1963_);
lean_inc_ref(v_val_1939_);
v___x_1968_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_common_1965_, v_val_1939_, v_snd_1964_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
lean_dec_ref(v_common_1965_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v_fst_1970_; lean_object* v_snd_1971_; lean_object* v___x_1972_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref(v___x_1968_);
v_fst_1970_ = lean_ctor_get(v_a_1969_, 0);
lean_inc(v_fst_1970_);
v_snd_1971_ = lean_ctor_get(v_a_1969_, 1);
lean_inc(v_snd_1971_);
lean_dec(v_a_1969_);
lean_inc_ref(v_val_1939_);
v___x_1972_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_x_1966_, v_val_1939_, v_snd_1971_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
lean_dec_ref(v_x_1966_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v_fst_1974_; lean_object* v_snd_1975_; lean_object* v___x_1976_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref(v___x_1972_);
v_fst_1974_ = lean_ctor_get(v_a_1973_, 0);
lean_inc(v_fst_1974_);
v_snd_1975_ = lean_ctor_get(v_a_1973_, 1);
lean_inc(v_snd_1975_);
lean_dec(v_a_1973_);
lean_inc_ref(v_val_1939_);
v___x_1976_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_y_1967_, v_val_1939_, v_snd_1975_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
lean_dec_ref(v_y_1967_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v_fst_1978_; lean_object* v_snd_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_2024_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref(v___x_1976_);
v_fst_1978_ = lean_ctor_get(v_a_1977_, 0);
v_snd_1979_ = lean_ctor_get(v_a_1977_, 1);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_a_1977_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_1981_ = v_a_1977_;
v_isShared_1982_ = v_isSharedCheck_2024_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_snd_1979_);
lean_inc(v_fst_1978_);
lean_dec(v_a_1977_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_2024_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___x_2014_; lean_object* v___f_2015_; lean_object* v___y_2017_; lean_object* v___x_2021_; 
lean_inc_ref(v_val_1939_);
v___x_2014_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_1939_);
v___f_2015_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_2015_, 0, v___x_2014_);
lean_inc(v_fst_1970_);
lean_inc_ref(v___f_2015_);
v___x_2021_ = l_Option_merge___redArg(v___f_2015_, v_fst_1970_, v_fst_1974_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v___x_2022_; 
lean_inc_ref(v_val_1939_);
v___x_2022_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_neutralElement(v_val_1939_);
v___y_2017_ = v___x_2022_;
goto v___jp_2016_;
}
else
{
lean_object* v_val_2023_; 
v_val_2023_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_val_2023_);
lean_dec_ref(v___x_2021_);
v___y_2017_ = v_val_2023_;
goto v___jp_2016_;
}
v___jp_1983_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
lean_inc_ref(v_P_1942_);
v___x_1986_ = l_Lean_mkAppB(v_P_1942_, v_lhs_1940_, v_rhs_1941_);
v___x_1987_ = l_Lean_mkAppB(v_P_1942_, v___y_1984_, v___y_1985_);
lean_inc_ref(v___x_1987_);
v___x_1988_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC(v___x_1986_, v___x_1987_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2005_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_2005_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2005_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1962_ == 0)
{
lean_ctor_set_tag(v___x_1961_, 1);
lean_ctor_set(v___x_1961_, 0, v_a_1989_);
v___x_1994_ = v___x_1961_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1999_; 
v___x_1995_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1995_, 0, v___x_1987_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
lean_ctor_set_uint8(v___x_1995_, sizeof(void*)*2, v_hasTrace_1943_);
v___x_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
v___x_1997_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v___x_1997_);
v___x_1999_ = v___x_1981_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1997_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_snd_1979_);
v___x_1999_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2001_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_1999_);
v___x_2001_ = v___x_1991_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_dec_ref(v___x_1987_);
lean_del_object(v___x_1981_);
lean_dec(v_snd_1979_);
lean_del_object(v___x_1961_);
v_a_2006_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_1988_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_1988_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
v___jp_2016_:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Option_merge___redArg(v___f_2015_, v_fst_1970_, v_fst_1978_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_neutralElement(v_val_1939_);
v___y_1984_ = v___y_2017_;
v___y_1985_ = v___x_2019_;
goto v___jp_1983_;
}
else
{
lean_object* v_val_2020_; 
lean_dec_ref(v_val_1939_);
v_val_2020_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_val_2020_);
lean_dec_ref(v___x_2018_);
v___y_1984_ = v___y_2017_;
v___y_1985_ = v_val_2020_;
goto v___jp_1983_;
}
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec(v_fst_1974_);
lean_dec(v_fst_1970_);
lean_del_object(v___x_1961_);
lean_dec_ref(v_P_1942_);
lean_dec_ref(v_rhs_1941_);
lean_dec_ref(v_lhs_1940_);
lean_dec_ref(v_val_1939_);
v_a_2025_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_1976_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_1976_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_dec(v_fst_1970_);
lean_dec_ref(v_y_1967_);
lean_del_object(v___x_1961_);
lean_dec_ref(v_P_1942_);
lean_dec_ref(v_rhs_1941_);
lean_dec_ref(v_lhs_1940_);
lean_dec_ref(v_val_1939_);
v_a_2033_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_1972_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_1972_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec_ref(v_y_1967_);
lean_dec_ref(v_x_1966_);
lean_del_object(v___x_1961_);
lean_dec_ref(v_P_1942_);
lean_dec_ref(v_rhs_1941_);
lean_dec_ref(v_lhs_1940_);
lean_dec_ref(v_val_1939_);
v_a_2041_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_1968_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_1968_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec(v_fst_1952_);
lean_dec_ref(v_P_1942_);
lean_dec_ref(v_rhs_1941_);
lean_dec_ref(v_lhs_1940_);
lean_dec_ref(v_val_1939_);
v_a_2050_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_1954_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_1954_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec_ref(v_P_1942_);
lean_dec_ref(v_rhs_1941_);
lean_dec_ref(v_lhs_1940_);
lean_dec_ref(v_val_1939_);
v_a_2058_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_1950_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_1950_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__5___boxed(lean_object* v_val_2066_, lean_object* v_lhs_2067_, lean_object* v_rhs_2068_, lean_object* v_P_2069_, lean_object* v_hasTrace_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
uint8_t v_hasTrace_boxed_2077_; lean_object* v_res_2078_; 
v_hasTrace_boxed_2077_ = lean_unbox(v_hasTrace_2070_);
v_res_2078_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__5(v_val_2066_, v_lhs_2067_, v_rhs_2068_, v_P_2069_, v_hasTrace_boxed_2077_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object* v_cls_2079_, lean_object* v_msg_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v_ref_2086_; lean_object* v___x_2087_; lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2132_; 
v_ref_2086_ = lean_ctor_get(v___y_2083_, 5);
v___x_2087_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2090_ = v___x_2087_;
v_isShared_2091_ = v_isSharedCheck_2132_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2087_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2132_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2092_; lean_object* v_traceState_2093_; lean_object* v_env_2094_; lean_object* v_nextMacroScope_2095_; lean_object* v_ngen_2096_; lean_object* v_auxDeclNGen_2097_; lean_object* v_cache_2098_; lean_object* v_messages_2099_; lean_object* v_infoState_2100_; lean_object* v_snapshotTasks_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2131_; 
v___x_2092_ = lean_st_ref_take(v___y_2084_);
v_traceState_2093_ = lean_ctor_get(v___x_2092_, 4);
v_env_2094_ = lean_ctor_get(v___x_2092_, 0);
v_nextMacroScope_2095_ = lean_ctor_get(v___x_2092_, 1);
v_ngen_2096_ = lean_ctor_get(v___x_2092_, 2);
v_auxDeclNGen_2097_ = lean_ctor_get(v___x_2092_, 3);
v_cache_2098_ = lean_ctor_get(v___x_2092_, 5);
v_messages_2099_ = lean_ctor_get(v___x_2092_, 6);
v_infoState_2100_ = lean_ctor_get(v___x_2092_, 7);
v_snapshotTasks_2101_ = lean_ctor_get(v___x_2092_, 8);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2103_ = v___x_2092_;
v_isShared_2104_ = v_isSharedCheck_2131_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_snapshotTasks_2101_);
lean_inc(v_infoState_2100_);
lean_inc(v_messages_2099_);
lean_inc(v_cache_2098_);
lean_inc(v_traceState_2093_);
lean_inc(v_auxDeclNGen_2097_);
lean_inc(v_ngen_2096_);
lean_inc(v_nextMacroScope_2095_);
lean_inc(v_env_2094_);
lean_dec(v___x_2092_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2131_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
uint64_t v_tid_2105_; lean_object* v_traces_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2130_; 
v_tid_2105_ = lean_ctor_get_uint64(v_traceState_2093_, sizeof(void*)*1);
v_traces_2106_ = lean_ctor_get(v_traceState_2093_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_traceState_2093_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2108_ = v_traceState_2093_;
v_isShared_2109_ = v_isSharedCheck_2130_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_traces_2106_);
lean_dec(v_traceState_2093_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2130_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2110_; double v___x_2111_; uint8_t v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2120_; 
v___x_2110_ = lean_box(0);
v___x_2111_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0);
v___x_2112_ = 0;
v___x_2113_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1));
v___x_2114_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2114_, 0, v_cls_2079_);
lean_ctor_set(v___x_2114_, 1, v___x_2110_);
lean_ctor_set(v___x_2114_, 2, v___x_2113_);
lean_ctor_set_float(v___x_2114_, sizeof(void*)*3, v___x_2111_);
lean_ctor_set_float(v___x_2114_, sizeof(void*)*3 + 8, v___x_2111_);
lean_ctor_set_uint8(v___x_2114_, sizeof(void*)*3 + 16, v___x_2112_);
v___x_2115_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__2));
v___x_2116_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2114_);
lean_ctor_set(v___x_2116_, 1, v_a_2088_);
lean_ctor_set(v___x_2116_, 2, v___x_2115_);
lean_inc(v_ref_2086_);
v___x_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2117_, 0, v_ref_2086_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___x_2118_ = l_Lean_PersistentArray_push___redArg(v_traces_2106_, v___x_2117_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2118_);
v___x_2120_ = v___x_2108_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2118_);
lean_ctor_set_uint64(v_reuseFailAlloc_2129_, sizeof(void*)*1, v_tid_2105_);
v___x_2120_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
lean_object* v___x_2122_; 
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 4, v___x_2120_);
v___x_2122_ = v___x_2103_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_env_2094_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_nextMacroScope_2095_);
lean_ctor_set(v_reuseFailAlloc_2128_, 2, v_ngen_2096_);
lean_ctor_set(v_reuseFailAlloc_2128_, 3, v_auxDeclNGen_2097_);
lean_ctor_set(v_reuseFailAlloc_2128_, 4, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2128_, 5, v_cache_2098_);
lean_ctor_set(v_reuseFailAlloc_2128_, 6, v_messages_2099_);
lean_ctor_set(v_reuseFailAlloc_2128_, 7, v_infoState_2100_);
lean_ctor_set(v_reuseFailAlloc_2128_, 8, v_snapshotTasks_2101_);
v___x_2122_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2123_ = lean_st_ref_set(v___y_2084_, v___x_2122_);
v___x_2124_ = lean_box(0);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2124_);
v___x_2126_ = v___x_2090_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object* v_cls_2133_, lean_object* v_msg_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2133_, v_msg_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
return v_res_2140_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__1));
v___x_2145_ = l_Lean_stringToMessageData(v___x_2144_);
return v___x_2145_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4(void){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2147_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__3));
v___x_2148_ = l_Lean_stringToMessageData(v___x_2147_);
return v___x_2148_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6(void){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__5));
v___x_2151_ = l_Lean_stringToMessageData(v___x_2150_);
return v___x_2151_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__7(void){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2152_ = lean_box(0);
v___x_2153_ = lean_unsigned_to_nat(16u);
v___x_2154_ = lean_mk_array(v___x_2153_, v___x_2152_);
return v___x_2154_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8(void){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2155_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__7);
v___x_2156_ = lean_unsigned_to_nat(0u);
v___x_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
lean_ctor_set(v___x_2157_, 1, v___x_2155_);
return v___x_2157_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__10));
v___x_2162_ = l_Lean_stringToMessageData(v___x_2161_);
return v___x_2162_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__12));
v___x_2165_ = l_Lean_stringToMessageData(v___x_2164_);
return v___x_2165_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__14));
v___x_2168_ = l_Lean_stringToMessageData(v___x_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4(lean_object* v_lhs_2169_, lean_object* v_rhs_2170_, lean_object* v___f_2171_, lean_object* v_cls_2172_, uint8_t v___x_2173_, lean_object* v_P_2174_, uint8_t v_hasTrace_2175_, lean_object* v_____r_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v___x_2194_; 
lean_inc_ref(v_lhs_2169_);
v___x_2194_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_lhs_2169_);
if (lean_obj_tag(v___x_2194_) == 1)
{
lean_object* v_val_2195_; lean_object* v___x_2196_; 
v_val_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_val_2195_);
lean_dec_ref(v___x_2194_);
lean_inc_ref(v_rhs_2170_);
v___x_2196_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_rhs_2170_);
if (lean_obj_tag(v___x_2196_) == 1)
{
lean_object* v_val_2197_; uint8_t v___x_2236_; 
v_val_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_val_2197_);
lean_dec_ref(v___x_2196_);
v___x_2236_ = lean_expr_eqv(v_val_2195_, v_val_2197_);
if (v___x_2236_ == 0)
{
lean_dec_ref(v_P_2174_);
goto v___jp_2198_;
}
else
{
if (v___x_2173_ == 0)
{
lean_object* v_options_2237_; lean_object* v_inheritedTraceOptions_2238_; uint8_t v_hasTrace_2239_; lean_object* v___x_2240_; lean_object* v___f_2241_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; 
lean_dec(v_val_2197_);
lean_dec_ref(v___f_2171_);
v_options_2237_ = lean_ctor_get(v___y_2182_, 2);
v_inheritedTraceOptions_2238_ = lean_ctor_get(v___y_2182_, 13);
v_hasTrace_2239_ = lean_ctor_get_uint8(v_options_2237_, sizeof(void*)*1);
v___x_2240_ = lean_box(v_hasTrace_2175_);
lean_inc(v_val_2195_);
v___f_2241_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__5___boxed), 11, 5);
lean_closure_set(v___f_2241_, 0, v_val_2195_);
lean_closure_set(v___f_2241_, 1, v_lhs_2169_);
lean_closure_set(v___f_2241_, 2, v_rhs_2170_);
lean_closure_set(v___f_2241_, 3, v_P_2174_);
lean_closure_set(v___f_2241_, 4, v___x_2240_);
if (v_hasTrace_2239_ == 0)
{
lean_dec(v_cls_2172_);
v___y_2243_ = v___y_2180_;
v___y_2244_ = v___y_2181_;
v___y_2245_ = v___y_2182_;
v___y_2246_ = v___y_2183_;
goto v___jp_2242_;
}
else
{
lean_object* v___x_2251_; lean_object* v___x_2252_; uint8_t v___x_2253_; 
v___x_2251_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2172_);
v___x_2252_ = l_Lean_Name_append(v___x_2251_, v_cls_2172_);
v___x_2253_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2238_, v_options_2237_, v___x_2252_);
lean_dec(v___x_2252_);
if (v___x_2253_ == 0)
{
lean_dec(v_cls_2172_);
v___y_2243_ = v___y_2180_;
v___y_2244_ = v___y_2181_;
v___y_2245_ = v___y_2182_;
v___y_2246_ = v___y_2183_;
goto v___jp_2242_;
}
else
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2254_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11);
lean_inc(v_val_2195_);
v___x_2255_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2195_);
v___x_2256_ = l_Lean_MessageData_ofExpr(v___x_2255_);
v___x_2257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2254_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
v___x_2258_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13);
v___x_2259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2257_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
v___x_2260_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2172_, v___x_2259_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_dec_ref(v___x_2260_);
v___y_2243_ = v___y_2180_;
v___y_2244_ = v___y_2181_;
v___y_2245_ = v___y_2182_;
v___y_2246_ = v___y_2183_;
goto v___jp_2242_;
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
lean_dec_ref(v___f_2241_);
lean_dec(v_val_2195_);
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2260_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2260_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
}
v___jp_2242_:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2247_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8);
v___x_2248_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__9));
v___x_2249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2249_, 0, v_val_2195_);
lean_ctor_set(v___x_2249_, 1, v___x_2247_);
lean_ctor_set(v___x_2249_, 2, v___x_2248_);
v___x_2250_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg(v___f_2241_, v___x_2249_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
return v___x_2250_;
}
}
else
{
lean_dec_ref(v_P_2174_);
goto v___jp_2198_;
}
}
v___jp_2198_:
{
lean_object* v_inheritedTraceOptions_2199_; lean_object* v___x_2200_; 
v_inheritedTraceOptions_2199_ = lean_ctor_get(v___y_2182_, 13);
lean_inc(v___y_2183_);
lean_inc_ref(v___y_2182_);
lean_inc(v___y_2181_);
lean_inc_ref(v___y_2180_);
lean_inc(v___y_2179_);
lean_inc_ref(v___y_2178_);
lean_inc(v___y_2177_);
lean_inc_ref(v_inheritedTraceOptions_2199_);
v___x_2200_ = lean_apply_9(v___f_2171_, v_inheritedTraceOptions_2199_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, lean_box(0));
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; uint8_t v___x_2202_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref(v___x_2200_);
v___x_2202_ = lean_unbox(v_a_2201_);
lean_dec(v_a_2201_);
if (v___x_2202_ == 0)
{
lean_dec(v_val_2197_);
lean_dec(v_val_2195_);
lean_dec(v_cls_2172_);
lean_dec_ref(v_rhs_2170_);
lean_dec_ref(v_lhs_2169_);
goto v___jp_2185_;
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2203_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2);
v___x_2204_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2195_);
v___x_2205_ = l_Lean_MessageData_ofExpr(v___x_2204_);
v___x_2206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2203_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
v___x_2207_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4);
v___x_2208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2206_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
v___x_2209_ = l_Lean_indentExpr(v_lhs_2169_);
v___x_2210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2208_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
v___x_2211_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6);
v___x_2212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2210_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
v___x_2213_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2197_);
v___x_2214_ = l_Lean_MessageData_ofExpr(v___x_2213_);
v___x_2215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2212_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
lean_ctor_set(v___x_2216_, 1, v___x_2207_);
v___x_2217_ = l_Lean_indentExpr(v_rhs_2170_);
v___x_2218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2216_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
v___x_2219_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2172_, v___x_2218_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_dec_ref(v___x_2219_);
goto v___jp_2185_;
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2219_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2219_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec(v_val_2197_);
lean_dec(v_val_2195_);
lean_dec(v_cls_2172_);
lean_dec_ref(v_rhs_2170_);
lean_dec_ref(v_lhs_2169_);
v_a_2228_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2200_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2200_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2269_; lean_object* v___x_2270_; 
lean_dec(v___x_2196_);
lean_dec(v_val_2195_);
lean_dec_ref(v_P_2174_);
lean_dec_ref(v_lhs_2169_);
v_inheritedTraceOptions_2269_ = lean_ctor_get(v___y_2182_, 13);
lean_inc(v___y_2183_);
lean_inc_ref(v___y_2182_);
lean_inc(v___y_2181_);
lean_inc_ref(v___y_2180_);
lean_inc(v___y_2179_);
lean_inc_ref(v___y_2178_);
lean_inc(v___y_2177_);
lean_inc_ref(v_inheritedTraceOptions_2269_);
v___x_2270_ = lean_apply_9(v___f_2171_, v_inheritedTraceOptions_2269_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, lean_box(0));
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; uint8_t v___x_2272_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2271_);
lean_dec_ref(v___x_2270_);
v___x_2272_ = lean_unbox(v_a_2271_);
lean_dec(v_a_2271_);
if (v___x_2272_ == 0)
{
lean_dec(v_cls_2172_);
lean_dec_ref(v_rhs_2170_);
goto v___jp_2188_;
}
else
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2273_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2274_ = l_Lean_indentExpr(v_rhs_2170_);
v___x_2275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2273_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
v___x_2276_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2172_, v___x_2275_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_dec_ref(v___x_2276_);
goto v___jp_2188_;
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2276_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2276_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_dec(v_cls_2172_);
lean_dec_ref(v_rhs_2170_);
v_a_2285_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2270_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2270_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2293_; lean_object* v___x_2294_; 
lean_dec(v___x_2194_);
lean_dec_ref(v_P_2174_);
lean_dec_ref(v_rhs_2170_);
v_inheritedTraceOptions_2293_ = lean_ctor_get(v___y_2182_, 13);
lean_inc(v___y_2183_);
lean_inc_ref(v___y_2182_);
lean_inc(v___y_2181_);
lean_inc_ref(v___y_2180_);
lean_inc(v___y_2179_);
lean_inc_ref(v___y_2178_);
lean_inc(v___y_2177_);
lean_inc_ref(v_inheritedTraceOptions_2293_);
v___x_2294_ = lean_apply_9(v___f_2171_, v_inheritedTraceOptions_2293_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, lean_box(0));
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; uint8_t v___x_2296_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref(v___x_2294_);
v___x_2296_ = lean_unbox(v_a_2295_);
lean_dec(v_a_2295_);
if (v___x_2296_ == 0)
{
lean_dec(v_cls_2172_);
lean_dec_ref(v_lhs_2169_);
goto v___jp_2191_;
}
else
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2297_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2298_ = l_Lean_indentExpr(v_lhs_2169_);
v___x_2299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2297_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
v___x_2300_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2172_, v___x_2299_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_dec_ref(v___x_2300_);
goto v___jp_2191_;
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2300_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2300_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_dec(v_cls_2172_);
lean_dec_ref(v_lhs_2169_);
v_a_2309_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2294_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2294_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
v___jp_2185_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
return v___x_2187_;
}
v___jp_2188_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
return v___x_2190_;
}
v___jp_2191_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
return v___x_2193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___boxed(lean_object* v_lhs_2317_, lean_object* v_rhs_2318_, lean_object* v___f_2319_, lean_object* v_cls_2320_, lean_object* v___x_2321_, lean_object* v_P_2322_, lean_object* v_hasTrace_2323_, lean_object* v_____r_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
uint8_t v___x_118788__boxed_2333_; uint8_t v_hasTrace_boxed_2334_; lean_object* v_res_2335_; 
v___x_118788__boxed_2333_ = lean_unbox(v___x_2321_);
v_hasTrace_boxed_2334_ = lean_unbox(v_hasTrace_2323_);
v_res_2335_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2317_, v_rhs_2318_, v___f_2319_, v_cls_2320_, v___x_118788__boxed_2333_, v_P_2322_, v_hasTrace_boxed_2334_, v_____r_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__8(lean_object* v_lhs_2336_, lean_object* v_rhs_2337_, lean_object* v_P_2338_, uint8_t v___x_2339_, lean_object* v_cls_2340_, lean_object* v___f_2341_, lean_object* v_____r_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v___x_2360_; 
lean_inc_ref(v_lhs_2336_);
v___x_2360_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_lhs_2336_);
if (lean_obj_tag(v___x_2360_) == 1)
{
lean_object* v_val_2361_; lean_object* v___x_2362_; 
v_val_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_val_2361_);
lean_dec_ref(v___x_2360_);
lean_inc_ref(v_rhs_2337_);
v___x_2362_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_rhs_2337_);
if (lean_obj_tag(v___x_2362_) == 1)
{
lean_object* v_val_2363_; lean_object* v___x_2364_; lean_object* v___f_2365_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; uint8_t v___x_2397_; 
v_val_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_val_2363_);
lean_dec_ref(v___x_2362_);
v___x_2364_ = lean_box(v___x_2339_);
lean_inc_ref(v_rhs_2337_);
lean_inc_ref(v_lhs_2336_);
lean_inc(v_val_2361_);
v___f_2365_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___boxed), 11, 5);
lean_closure_set(v___f_2365_, 0, v_val_2361_);
lean_closure_set(v___f_2365_, 1, v_lhs_2336_);
lean_closure_set(v___f_2365_, 2, v_rhs_2337_);
lean_closure_set(v___f_2365_, 3, v_P_2338_);
lean_closure_set(v___f_2365_, 4, v___x_2364_);
v___x_2397_ = lean_expr_eqv(v_val_2361_, v_val_2363_);
if (v___x_2397_ == 0)
{
if (v___x_2339_ == 0)
{
lean_dec(v_val_2363_);
lean_dec_ref(v___f_2341_);
lean_dec_ref(v_rhs_2337_);
lean_dec_ref(v_lhs_2336_);
goto v___jp_2375_;
}
else
{
lean_object* v_inheritedTraceOptions_2398_; lean_object* v___x_2399_; 
lean_dec_ref(v___f_2365_);
v_inheritedTraceOptions_2398_ = lean_ctor_get(v___y_2348_, 13);
lean_inc(v___y_2349_);
lean_inc_ref(v___y_2348_);
lean_inc(v___y_2347_);
lean_inc_ref(v___y_2346_);
lean_inc(v___y_2345_);
lean_inc_ref(v___y_2344_);
lean_inc(v___y_2343_);
lean_inc_ref(v_inheritedTraceOptions_2398_);
v___x_2399_ = lean_apply_9(v___f_2341_, v_inheritedTraceOptions_2398_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, lean_box(0));
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; uint8_t v___x_2401_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_a_2400_);
lean_dec_ref(v___x_2399_);
v___x_2401_ = lean_unbox(v_a_2400_);
lean_dec(v_a_2400_);
if (v___x_2401_ == 0)
{
lean_dec(v_val_2363_);
lean_dec(v_val_2361_);
lean_dec(v_cls_2340_);
lean_dec_ref(v_rhs_2337_);
lean_dec_ref(v_lhs_2336_);
goto v___jp_2351_;
}
else
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2402_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2);
v___x_2403_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2361_);
v___x_2404_ = l_Lean_MessageData_ofExpr(v___x_2403_);
v___x_2405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2402_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
v___x_2406_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4);
v___x_2407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2405_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
v___x_2408_ = l_Lean_indentExpr(v_lhs_2336_);
v___x_2409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2407_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6);
v___x_2411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2409_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2363_);
v___x_2413_ = l_Lean_MessageData_ofExpr(v___x_2412_);
v___x_2414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2411_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
lean_ctor_set(v___x_2415_, 1, v___x_2406_);
v___x_2416_ = l_Lean_indentExpr(v_rhs_2337_);
v___x_2417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2415_);
lean_ctor_set(v___x_2417_, 1, v___x_2416_);
v___x_2418_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2340_, v___x_2417_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_dec_ref(v___x_2418_);
goto v___jp_2351_;
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2418_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2418_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_dec(v_val_2363_);
lean_dec(v_val_2361_);
lean_dec(v_cls_2340_);
lean_dec_ref(v_rhs_2337_);
lean_dec_ref(v_lhs_2336_);
v_a_2427_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2399_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2399_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
}
else
{
lean_dec(v_val_2363_);
lean_dec_ref(v___f_2341_);
lean_dec_ref(v_rhs_2337_);
lean_dec_ref(v_lhs_2336_);
goto v___jp_2375_;
}
v___jp_2366_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2371_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8);
v___x_2372_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__9));
v___x_2373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2373_, 0, v_val_2361_);
lean_ctor_set(v___x_2373_, 1, v___x_2371_);
lean_ctor_set(v___x_2373_, 2, v___x_2372_);
v___x_2374_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg(v___f_2365_, v___x_2373_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
return v___x_2374_;
}
v___jp_2375_:
{
lean_object* v_options_2376_; uint8_t v_hasTrace_2377_; 
v_options_2376_ = lean_ctor_get(v___y_2348_, 2);
v_hasTrace_2377_ = lean_ctor_get_uint8(v_options_2376_, sizeof(void*)*1);
if (v_hasTrace_2377_ == 0)
{
lean_dec(v_cls_2340_);
v___y_2367_ = v___y_2346_;
v___y_2368_ = v___y_2347_;
v___y_2369_ = v___y_2348_;
v___y_2370_ = v___y_2349_;
goto v___jp_2366_;
}
else
{
lean_object* v_inheritedTraceOptions_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; uint8_t v___x_2381_; 
v_inheritedTraceOptions_2378_ = lean_ctor_get(v___y_2348_, 13);
v___x_2379_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2340_);
v___x_2380_ = l_Lean_Name_append(v___x_2379_, v_cls_2340_);
v___x_2381_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2378_, v_options_2376_, v___x_2380_);
lean_dec(v___x_2380_);
if (v___x_2381_ == 0)
{
lean_dec(v_cls_2340_);
v___y_2367_ = v___y_2346_;
v___y_2368_ = v___y_2347_;
v___y_2369_ = v___y_2348_;
v___y_2370_ = v___y_2349_;
goto v___jp_2366_;
}
else
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2382_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11);
lean_inc(v_val_2361_);
v___x_2383_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2361_);
v___x_2384_ = l_Lean_MessageData_ofExpr(v___x_2383_);
v___x_2385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2382_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
v___x_2386_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13);
v___x_2387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2385_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
v___x_2388_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2340_, v___x_2387_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_dec_ref(v___x_2388_);
v___y_2367_ = v___y_2346_;
v___y_2368_ = v___y_2347_;
v___y_2369_ = v___y_2348_;
v___y_2370_ = v___y_2349_;
goto v___jp_2366_;
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec_ref(v___f_2365_);
lean_dec(v_val_2361_);
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2388_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2388_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2435_; lean_object* v___x_2436_; 
lean_dec(v___x_2362_);
lean_dec(v_val_2361_);
lean_dec_ref(v_P_2338_);
lean_dec_ref(v_lhs_2336_);
v_inheritedTraceOptions_2435_ = lean_ctor_get(v___y_2348_, 13);
lean_inc(v___y_2349_);
lean_inc_ref(v___y_2348_);
lean_inc(v___y_2347_);
lean_inc_ref(v___y_2346_);
lean_inc(v___y_2345_);
lean_inc_ref(v___y_2344_);
lean_inc(v___y_2343_);
lean_inc_ref(v_inheritedTraceOptions_2435_);
v___x_2436_ = lean_apply_9(v___f_2341_, v_inheritedTraceOptions_2435_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, lean_box(0));
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; uint8_t v___x_2438_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_a_2437_);
lean_dec_ref(v___x_2436_);
v___x_2438_ = lean_unbox(v_a_2437_);
lean_dec(v_a_2437_);
if (v___x_2438_ == 0)
{
lean_dec(v_cls_2340_);
lean_dec_ref(v_rhs_2337_);
goto v___jp_2354_;
}
else
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2439_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2440_ = l_Lean_indentExpr(v_rhs_2337_);
v___x_2441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2439_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
v___x_2442_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2340_, v___x_2441_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_dec_ref(v___x_2442_);
goto v___jp_2354_;
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec(v_cls_2340_);
lean_dec_ref(v_rhs_2337_);
v_a_2451_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2436_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2436_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2459_; lean_object* v___x_2460_; 
lean_dec(v___x_2360_);
lean_dec_ref(v_P_2338_);
lean_dec_ref(v_rhs_2337_);
v_inheritedTraceOptions_2459_ = lean_ctor_get(v___y_2348_, 13);
lean_inc(v___y_2349_);
lean_inc_ref(v___y_2348_);
lean_inc(v___y_2347_);
lean_inc_ref(v___y_2346_);
lean_inc(v___y_2345_);
lean_inc_ref(v___y_2344_);
lean_inc(v___y_2343_);
lean_inc_ref(v_inheritedTraceOptions_2459_);
v___x_2460_ = lean_apply_9(v___f_2341_, v_inheritedTraceOptions_2459_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, lean_box(0));
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; uint8_t v___x_2462_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2461_);
lean_dec_ref(v___x_2460_);
v___x_2462_ = lean_unbox(v_a_2461_);
lean_dec(v_a_2461_);
if (v___x_2462_ == 0)
{
lean_dec(v_cls_2340_);
lean_dec_ref(v_lhs_2336_);
goto v___jp_2357_;
}
else
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2463_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2464_ = l_Lean_indentExpr(v_lhs_2336_);
v___x_2465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2340_, v___x_2465_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_dec_ref(v___x_2466_);
goto v___jp_2357_;
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2466_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2466_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec(v_cls_2340_);
lean_dec_ref(v_lhs_2336_);
v_a_2475_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2460_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2460_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
v___jp_2351_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
return v___x_2353_;
}
v___jp_2354_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
return v___x_2356_;
}
v___jp_2357_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
return v___x_2359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__8___boxed(lean_object* v_lhs_2483_, lean_object* v_rhs_2484_, lean_object* v_P_2485_, lean_object* v___x_2486_, lean_object* v_cls_2487_, lean_object* v___f_2488_, lean_object* v_____r_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
uint8_t v___x_119144__boxed_2498_; lean_object* v_res_2499_; 
v___x_119144__boxed_2498_ = lean_unbox(v___x_2486_);
v_res_2499_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__8(v_lhs_2483_, v_rhs_2484_, v_P_2485_, v___x_119144__boxed_2498_, v_cls_2487_, v___f_2488_, v_____r_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg(lean_object* v_x_2500_){
_start:
{
if (lean_obj_tag(v_x_2500_) == 0)
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
v_a_2502_ = lean_ctor_get(v_x_2500_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v_x_2500_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v_x_2500_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v_x_2500_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
lean_ctor_set_tag(v___x_2504_, 1);
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
else
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
v_a_2510_ = lean_ctor_get(v_x_2500_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v_x_2500_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v_x_2500_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v_x_2500_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
lean_ctor_set_tag(v___x_2512_, 0);
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg___boxed(lean_object* v_x_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg(v_x_2518_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4_spec__5(size_t v_sz_2521_, size_t v_i_2522_, lean_object* v_bs_2523_){
_start:
{
uint8_t v___x_2524_; 
v___x_2524_ = lean_usize_dec_lt(v_i_2522_, v_sz_2521_);
if (v___x_2524_ == 0)
{
return v_bs_2523_;
}
else
{
lean_object* v_v_2525_; lean_object* v_msg_2526_; lean_object* v___x_2527_; lean_object* v_bs_x27_2528_; size_t v___x_2529_; size_t v___x_2530_; lean_object* v___x_2531_; 
v_v_2525_ = lean_array_uget_borrowed(v_bs_2523_, v_i_2522_);
v_msg_2526_ = lean_ctor_get(v_v_2525_, 1);
lean_inc_ref(v_msg_2526_);
v___x_2527_ = lean_unsigned_to_nat(0u);
v_bs_x27_2528_ = lean_array_uset(v_bs_2523_, v_i_2522_, v___x_2527_);
v___x_2529_ = ((size_t)1ULL);
v___x_2530_ = lean_usize_add(v_i_2522_, v___x_2529_);
v___x_2531_ = lean_array_uset(v_bs_x27_2528_, v_i_2522_, v_msg_2526_);
v_i_2522_ = v___x_2530_;
v_bs_2523_ = v___x_2531_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_2533_, lean_object* v_i_2534_, lean_object* v_bs_2535_){
_start:
{
size_t v_sz_boxed_2536_; size_t v_i_boxed_2537_; lean_object* v_res_2538_; 
v_sz_boxed_2536_ = lean_unbox_usize(v_sz_2533_);
lean_dec(v_sz_2533_);
v_i_boxed_2537_ = lean_unbox_usize(v_i_2534_);
lean_dec(v_i_2534_);
v_res_2538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4_spec__5(v_sz_boxed_2536_, v_i_boxed_2537_, v_bs_2535_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(lean_object* v_oldTraces_2539_, lean_object* v_data_2540_, lean_object* v_ref_2541_, lean_object* v_msg_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v_fileName_2548_; lean_object* v_fileMap_2549_; lean_object* v_options_2550_; lean_object* v_currRecDepth_2551_; lean_object* v_maxRecDepth_2552_; lean_object* v_ref_2553_; lean_object* v_currNamespace_2554_; lean_object* v_openDecls_2555_; lean_object* v_initHeartbeats_2556_; lean_object* v_maxHeartbeats_2557_; lean_object* v_quotContext_2558_; lean_object* v_currMacroScope_2559_; uint8_t v_diag_2560_; lean_object* v_cancelTk_x3f_2561_; uint8_t v_suppressElabErrors_2562_; lean_object* v_inheritedTraceOptions_2563_; lean_object* v___x_2564_; lean_object* v_traceState_2565_; lean_object* v_traces_2566_; lean_object* v_ref_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; size_t v_sz_2570_; size_t v___x_2571_; lean_object* v___x_2572_; lean_object* v_msg_2573_; lean_object* v___x_2574_; lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2612_; 
v_fileName_2548_ = lean_ctor_get(v___y_2545_, 0);
v_fileMap_2549_ = lean_ctor_get(v___y_2545_, 1);
v_options_2550_ = lean_ctor_get(v___y_2545_, 2);
v_currRecDepth_2551_ = lean_ctor_get(v___y_2545_, 3);
v_maxRecDepth_2552_ = lean_ctor_get(v___y_2545_, 4);
v_ref_2553_ = lean_ctor_get(v___y_2545_, 5);
v_currNamespace_2554_ = lean_ctor_get(v___y_2545_, 6);
v_openDecls_2555_ = lean_ctor_get(v___y_2545_, 7);
v_initHeartbeats_2556_ = lean_ctor_get(v___y_2545_, 8);
v_maxHeartbeats_2557_ = lean_ctor_get(v___y_2545_, 9);
v_quotContext_2558_ = lean_ctor_get(v___y_2545_, 10);
v_currMacroScope_2559_ = lean_ctor_get(v___y_2545_, 11);
v_diag_2560_ = lean_ctor_get_uint8(v___y_2545_, sizeof(void*)*14);
v_cancelTk_x3f_2561_ = lean_ctor_get(v___y_2545_, 12);
v_suppressElabErrors_2562_ = lean_ctor_get_uint8(v___y_2545_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2563_ = lean_ctor_get(v___y_2545_, 13);
v___x_2564_ = lean_st_ref_get(v___y_2546_);
v_traceState_2565_ = lean_ctor_get(v___x_2564_, 4);
lean_inc_ref(v_traceState_2565_);
lean_dec(v___x_2564_);
v_traces_2566_ = lean_ctor_get(v_traceState_2565_, 0);
lean_inc_ref(v_traces_2566_);
lean_dec_ref(v_traceState_2565_);
v_ref_2567_ = l_Lean_replaceRef(v_ref_2541_, v_ref_2553_);
lean_inc_ref(v_inheritedTraceOptions_2563_);
lean_inc(v_cancelTk_x3f_2561_);
lean_inc(v_currMacroScope_2559_);
lean_inc(v_quotContext_2558_);
lean_inc(v_maxHeartbeats_2557_);
lean_inc(v_initHeartbeats_2556_);
lean_inc(v_openDecls_2555_);
lean_inc(v_currNamespace_2554_);
lean_inc(v_maxRecDepth_2552_);
lean_inc(v_currRecDepth_2551_);
lean_inc_ref(v_options_2550_);
lean_inc_ref(v_fileMap_2549_);
lean_inc_ref(v_fileName_2548_);
v___x_2568_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2568_, 0, v_fileName_2548_);
lean_ctor_set(v___x_2568_, 1, v_fileMap_2549_);
lean_ctor_set(v___x_2568_, 2, v_options_2550_);
lean_ctor_set(v___x_2568_, 3, v_currRecDepth_2551_);
lean_ctor_set(v___x_2568_, 4, v_maxRecDepth_2552_);
lean_ctor_set(v___x_2568_, 5, v_ref_2567_);
lean_ctor_set(v___x_2568_, 6, v_currNamespace_2554_);
lean_ctor_set(v___x_2568_, 7, v_openDecls_2555_);
lean_ctor_set(v___x_2568_, 8, v_initHeartbeats_2556_);
lean_ctor_set(v___x_2568_, 9, v_maxHeartbeats_2557_);
lean_ctor_set(v___x_2568_, 10, v_quotContext_2558_);
lean_ctor_set(v___x_2568_, 11, v_currMacroScope_2559_);
lean_ctor_set(v___x_2568_, 12, v_cancelTk_x3f_2561_);
lean_ctor_set(v___x_2568_, 13, v_inheritedTraceOptions_2563_);
lean_ctor_set_uint8(v___x_2568_, sizeof(void*)*14, v_diag_2560_);
lean_ctor_set_uint8(v___x_2568_, sizeof(void*)*14 + 1, v_suppressElabErrors_2562_);
v___x_2569_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2566_);
lean_dec_ref(v_traces_2566_);
v_sz_2570_ = lean_array_size(v___x_2569_);
v___x_2571_ = ((size_t)0ULL);
v___x_2572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4_spec__5(v_sz_2570_, v___x_2571_, v___x_2569_);
v_msg_2573_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2573_, 0, v_data_2540_);
lean_ctor_set(v_msg_2573_, 1, v_msg_2542_);
lean_ctor_set(v_msg_2573_, 2, v___x_2572_);
v___x_2574_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2573_, v___y_2543_, v___y_2544_, v___x_2568_, v___y_2546_);
lean_dec_ref(v___x_2568_);
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2577_ = v___x_2574_;
v_isShared_2578_ = v_isSharedCheck_2612_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2612_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2579_; lean_object* v_traceState_2580_; lean_object* v_env_2581_; lean_object* v_nextMacroScope_2582_; lean_object* v_ngen_2583_; lean_object* v_auxDeclNGen_2584_; lean_object* v_cache_2585_; lean_object* v_messages_2586_; lean_object* v_infoState_2587_; lean_object* v_snapshotTasks_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2611_; 
v___x_2579_ = lean_st_ref_take(v___y_2546_);
v_traceState_2580_ = lean_ctor_get(v___x_2579_, 4);
v_env_2581_ = lean_ctor_get(v___x_2579_, 0);
v_nextMacroScope_2582_ = lean_ctor_get(v___x_2579_, 1);
v_ngen_2583_ = lean_ctor_get(v___x_2579_, 2);
v_auxDeclNGen_2584_ = lean_ctor_get(v___x_2579_, 3);
v_cache_2585_ = lean_ctor_get(v___x_2579_, 5);
v_messages_2586_ = lean_ctor_get(v___x_2579_, 6);
v_infoState_2587_ = lean_ctor_get(v___x_2579_, 7);
v_snapshotTasks_2588_ = lean_ctor_get(v___x_2579_, 8);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2590_ = v___x_2579_;
v_isShared_2591_ = v_isSharedCheck_2611_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_snapshotTasks_2588_);
lean_inc(v_infoState_2587_);
lean_inc(v_messages_2586_);
lean_inc(v_cache_2585_);
lean_inc(v_traceState_2580_);
lean_inc(v_auxDeclNGen_2584_);
lean_inc(v_ngen_2583_);
lean_inc(v_nextMacroScope_2582_);
lean_inc(v_env_2581_);
lean_dec(v___x_2579_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2611_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
uint64_t v_tid_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2609_; 
v_tid_2592_ = lean_ctor_get_uint64(v_traceState_2580_, sizeof(void*)*1);
v_isSharedCheck_2609_ = !lean_is_exclusive(v_traceState_2580_);
if (v_isSharedCheck_2609_ == 0)
{
lean_object* v_unused_2610_; 
v_unused_2610_ = lean_ctor_get(v_traceState_2580_, 0);
lean_dec(v_unused_2610_);
v___x_2594_ = v_traceState_2580_;
v_isShared_2595_ = v_isSharedCheck_2609_;
goto v_resetjp_2593_;
}
else
{
lean_dec(v_traceState_2580_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2609_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2599_; 
v___x_2596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2596_, 0, v_ref_2541_);
lean_ctor_set(v___x_2596_, 1, v_a_2575_);
v___x_2597_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2539_, v___x_2596_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2597_);
v___x_2599_ = v___x_2594_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2597_);
lean_ctor_set_uint64(v_reuseFailAlloc_2608_, sizeof(void*)*1, v_tid_2592_);
v___x_2599_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
lean_object* v___x_2601_; 
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 4, v___x_2599_);
v___x_2601_ = v___x_2590_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_env_2581_);
lean_ctor_set(v_reuseFailAlloc_2607_, 1, v_nextMacroScope_2582_);
lean_ctor_set(v_reuseFailAlloc_2607_, 2, v_ngen_2583_);
lean_ctor_set(v_reuseFailAlloc_2607_, 3, v_auxDeclNGen_2584_);
lean_ctor_set(v_reuseFailAlloc_2607_, 4, v___x_2599_);
lean_ctor_set(v_reuseFailAlloc_2607_, 5, v_cache_2585_);
lean_ctor_set(v_reuseFailAlloc_2607_, 6, v_messages_2586_);
lean_ctor_set(v_reuseFailAlloc_2607_, 7, v_infoState_2587_);
lean_ctor_set(v_reuseFailAlloc_2607_, 8, v_snapshotTasks_2588_);
v___x_2601_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2605_; 
v___x_2602_ = lean_st_ref_set(v___y_2546_, v___x_2601_);
v___x_2603_ = lean_box(0);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2603_);
v___x_2605_ = v___x_2577_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2603_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg___boxed(lean_object* v_oldTraces_2613_, lean_object* v_data_2614_, lean_object* v_ref_2615_, lean_object* v_msg_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_oldTraces_2613_, v_data_2614_, v_ref_2615_, v_msg_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__6(lean_object* v_opts_2623_, lean_object* v_opt_2624_){
_start:
{
lean_object* v_name_2625_; lean_object* v_defValue_2626_; lean_object* v_map_2627_; lean_object* v___x_2628_; 
v_name_2625_ = lean_ctor_get(v_opt_2624_, 0);
v_defValue_2626_ = lean_ctor_get(v_opt_2624_, 1);
v_map_2627_ = lean_ctor_get(v_opts_2623_, 0);
v___x_2628_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2627_, v_name_2625_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_inc(v_defValue_2626_);
return v_defValue_2626_;
}
else
{
lean_object* v_val_2629_; 
v_val_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_val_2629_);
lean_dec_ref(v___x_2628_);
if (lean_obj_tag(v_val_2629_) == 3)
{
lean_object* v_v_2630_; 
v_v_2630_ = lean_ctor_get(v_val_2629_, 0);
lean_inc(v_v_2630_);
lean_dec_ref(v_val_2629_);
return v_v_2630_;
}
else
{
lean_dec(v_val_2629_);
lean_inc(v_defValue_2626_);
return v_defValue_2626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__6___boxed(lean_object* v_opts_2631_, lean_object* v_opt_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2631_, v_opt_2632_);
lean_dec_ref(v_opt_2632_);
lean_dec_ref(v_opts_2631_);
return v_res_2633_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__3(lean_object* v_e_2634_){
_start:
{
if (lean_obj_tag(v_e_2634_) == 0)
{
uint8_t v___x_2635_; 
v___x_2635_ = 2;
return v___x_2635_;
}
else
{
uint8_t v___x_2636_; 
v___x_2636_ = 0;
return v___x_2636_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__3___boxed(lean_object* v_e_2637_){
_start:
{
uint8_t v_res_2638_; lean_object* v_r_2639_; 
v_res_2638_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__3(v_e_2637_);
lean_dec_ref(v_e_2637_);
v_r_2639_ = lean_box(v_res_2638_);
return v_r_2639_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__0));
v___x_2642_ = l_Lean_stringToMessageData(v___x_2641_);
return v___x_2642_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2643_; double v___x_2644_; 
v___x_2643_ = lean_unsigned_to_nat(1000u);
v___x_2644_ = lean_float_of_nat(v___x_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(lean_object* v_cls_2645_, uint8_t v_collapsed_2646_, lean_object* v_tag_2647_, lean_object* v_opts_2648_, uint8_t v_clsEnabled_2649_, lean_object* v_oldTraces_2650_, lean_object* v_msg_2651_, lean_object* v_resStartStop_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v_fst_2661_; lean_object* v_snd_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2760_; 
v_fst_2661_ = lean_ctor_get(v_resStartStop_2652_, 0);
v_snd_2662_ = lean_ctor_get(v_resStartStop_2652_, 1);
v_isSharedCheck_2760_ = !lean_is_exclusive(v_resStartStop_2652_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2664_ = v_resStartStop_2652_;
v_isShared_2665_ = v_isSharedCheck_2760_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_snd_2662_);
lean_inc(v_fst_2661_);
lean_dec(v_resStartStop_2652_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2760_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v_data_2669_; lean_object* v_fst_2680_; lean_object* v_snd_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2759_; 
v_fst_2680_ = lean_ctor_get(v_snd_2662_, 0);
v_snd_2681_ = lean_ctor_get(v_snd_2662_, 1);
v_isSharedCheck_2759_ = !lean_is_exclusive(v_snd_2662_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2683_ = v_snd_2662_;
v_isShared_2684_ = v_isSharedCheck_2759_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_snd_2681_);
lean_inc(v_fst_2680_);
lean_dec(v_snd_2662_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2759_;
goto v_resetjp_2682_;
}
v___jp_2666_:
{
lean_object* v___x_2670_; 
lean_inc(v___y_2667_);
v___x_2670_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_oldTraces_2650_, v_data_2669_, v___y_2667_, v___y_2668_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v___x_2671_; 
lean_dec_ref(v___x_2670_);
v___x_2671_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg(v_fst_2661_);
return v___x_2671_;
}
else
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
lean_dec(v_fst_2661_);
v_a_2672_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___x_2670_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2670_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
v_resetjp_2682_:
{
lean_object* v___x_2685_; uint8_t v___x_2686_; lean_object* v___y_2688_; lean_object* v_a_2689_; uint8_t v___y_2713_; double v___y_2744_; 
v___x_2685_ = l_Lean_trace_profiler;
v___x_2686_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(v_opts_2648_, v___x_2685_);
if (v___x_2686_ == 0)
{
v___y_2713_ = v___x_2686_;
goto v___jp_2712_;
}
else
{
lean_object* v___x_2749_; uint8_t v___x_2750_; 
v___x_2749_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2750_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(v_opts_2648_, v___x_2749_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; lean_object* v___x_2752_; double v___x_2753_; double v___x_2754_; double v___x_2755_; 
v___x_2751_ = l_Lean_trace_profiler_threshold;
v___x_2752_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2648_, v___x_2751_);
v___x_2753_ = lean_float_of_nat(v___x_2752_);
v___x_2754_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__2);
v___x_2755_ = lean_float_div(v___x_2753_, v___x_2754_);
v___y_2744_ = v___x_2755_;
goto v___jp_2743_;
}
else
{
lean_object* v___x_2756_; lean_object* v___x_2757_; double v___x_2758_; 
v___x_2756_ = l_Lean_trace_profiler_threshold;
v___x_2757_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2648_, v___x_2756_);
v___x_2758_ = lean_float_of_nat(v___x_2757_);
v___y_2744_ = v___x_2758_;
goto v___jp_2743_;
}
}
v___jp_2687_:
{
uint8_t v_result_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2695_; 
v_result_2690_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__3(v_fst_2661_);
v___x_2691_ = l_Lean_TraceResult_toEmoji(v_result_2690_);
v___x_2692_ = l_Lean_stringToMessageData(v___x_2691_);
v___x_2693_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10);
if (v_isShared_2684_ == 0)
{
lean_ctor_set_tag(v___x_2683_, 7);
lean_ctor_set(v___x_2683_, 1, v___x_2693_);
lean_ctor_set(v___x_2683_, 0, v___x_2692_);
v___x_2695_ = v___x_2683_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2692_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
lean_object* v_m_2697_; 
if (v_isShared_2665_ == 0)
{
lean_ctor_set_tag(v___x_2664_, 7);
lean_ctor_set(v___x_2664_, 1, v_a_2689_);
lean_ctor_set(v___x_2664_, 0, v___x_2695_);
v_m_2697_ = v___x_2664_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2695_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v_a_2689_);
v_m_2697_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; double v___x_2700_; lean_object* v_data_2701_; 
v___x_2698_ = lean_box(v_result_2690_);
v___x_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
v___x_2700_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0);
lean_inc_ref(v_tag_2647_);
lean_inc_ref(v___x_2699_);
lean_inc(v_cls_2645_);
v_data_2701_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2701_, 0, v_cls_2645_);
lean_ctor_set(v_data_2701_, 1, v___x_2699_);
lean_ctor_set(v_data_2701_, 2, v_tag_2647_);
lean_ctor_set_float(v_data_2701_, sizeof(void*)*3, v___x_2700_);
lean_ctor_set_float(v_data_2701_, sizeof(void*)*3 + 8, v___x_2700_);
lean_ctor_set_uint8(v_data_2701_, sizeof(void*)*3 + 16, v_collapsed_2646_);
if (v___x_2686_ == 0)
{
lean_dec_ref(v___x_2699_);
lean_dec(v_snd_2681_);
lean_dec(v_fst_2680_);
lean_dec_ref(v_tag_2647_);
lean_dec(v_cls_2645_);
v___y_2667_ = v___y_2688_;
v___y_2668_ = v_m_2697_;
v_data_2669_ = v_data_2701_;
goto v___jp_2666_;
}
else
{
lean_object* v_data_2702_; double v___x_2703_; double v___x_2704_; 
lean_dec_ref(v_data_2701_);
v_data_2702_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2702_, 0, v_cls_2645_);
lean_ctor_set(v_data_2702_, 1, v___x_2699_);
lean_ctor_set(v_data_2702_, 2, v_tag_2647_);
v___x_2703_ = lean_unbox_float(v_fst_2680_);
lean_dec(v_fst_2680_);
lean_ctor_set_float(v_data_2702_, sizeof(void*)*3, v___x_2703_);
v___x_2704_ = lean_unbox_float(v_snd_2681_);
lean_dec(v_snd_2681_);
lean_ctor_set_float(v_data_2702_, sizeof(void*)*3 + 8, v___x_2704_);
lean_ctor_set_uint8(v_data_2702_, sizeof(void*)*3 + 16, v_collapsed_2646_);
v___y_2667_ = v___y_2688_;
v___y_2668_ = v_m_2697_;
v_data_2669_ = v_data_2702_;
goto v___jp_2666_;
}
}
}
}
v___jp_2707_:
{
lean_object* v_ref_2708_; lean_object* v___x_2709_; 
v_ref_2708_ = lean_ctor_get(v___y_2658_, 5);
lean_inc(v___y_2659_);
lean_inc_ref(v___y_2658_);
lean_inc(v___y_2657_);
lean_inc_ref(v___y_2656_);
lean_inc(v___y_2655_);
lean_inc_ref(v___y_2654_);
lean_inc(v___y_2653_);
lean_inc(v_fst_2661_);
v___x_2709_ = lean_apply_9(v_msg_2651_, v_fst_2661_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, lean_box(0));
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref(v___x_2709_);
v___y_2688_ = v_ref_2708_;
v_a_2689_ = v_a_2710_;
goto v___jp_2687_;
}
else
{
lean_object* v___x_2711_; 
lean_dec_ref(v___x_2709_);
v___x_2711_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__1);
v___y_2688_ = v_ref_2708_;
v_a_2689_ = v___x_2711_;
goto v___jp_2687_;
}
}
v___jp_2712_:
{
if (v_clsEnabled_2649_ == 0)
{
if (v___y_2713_ == 0)
{
lean_object* v___x_2714_; lean_object* v_traceState_2715_; lean_object* v_env_2716_; lean_object* v_nextMacroScope_2717_; lean_object* v_ngen_2718_; lean_object* v_auxDeclNGen_2719_; lean_object* v_cache_2720_; lean_object* v_messages_2721_; lean_object* v_infoState_2722_; lean_object* v_snapshotTasks_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2742_; 
lean_del_object(v___x_2683_);
lean_dec(v_snd_2681_);
lean_dec(v_fst_2680_);
lean_del_object(v___x_2664_);
lean_dec_ref(v_msg_2651_);
lean_dec_ref(v_tag_2647_);
lean_dec(v_cls_2645_);
v___x_2714_ = lean_st_ref_take(v___y_2659_);
v_traceState_2715_ = lean_ctor_get(v___x_2714_, 4);
v_env_2716_ = lean_ctor_get(v___x_2714_, 0);
v_nextMacroScope_2717_ = lean_ctor_get(v___x_2714_, 1);
v_ngen_2718_ = lean_ctor_get(v___x_2714_, 2);
v_auxDeclNGen_2719_ = lean_ctor_get(v___x_2714_, 3);
v_cache_2720_ = lean_ctor_get(v___x_2714_, 5);
v_messages_2721_ = lean_ctor_get(v___x_2714_, 6);
v_infoState_2722_ = lean_ctor_get(v___x_2714_, 7);
v_snapshotTasks_2723_ = lean_ctor_get(v___x_2714_, 8);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2725_ = v___x_2714_;
v_isShared_2726_ = v_isSharedCheck_2742_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_snapshotTasks_2723_);
lean_inc(v_infoState_2722_);
lean_inc(v_messages_2721_);
lean_inc(v_cache_2720_);
lean_inc(v_traceState_2715_);
lean_inc(v_auxDeclNGen_2719_);
lean_inc(v_ngen_2718_);
lean_inc(v_nextMacroScope_2717_);
lean_inc(v_env_2716_);
lean_dec(v___x_2714_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2742_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
uint64_t v_tid_2727_; lean_object* v_traces_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2741_; 
v_tid_2727_ = lean_ctor_get_uint64(v_traceState_2715_, sizeof(void*)*1);
v_traces_2728_ = lean_ctor_get(v_traceState_2715_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_traceState_2715_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2730_ = v_traceState_2715_;
v_isShared_2731_ = v_isSharedCheck_2741_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_traces_2728_);
lean_dec(v_traceState_2715_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2741_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2732_; lean_object* v___x_2734_; 
v___x_2732_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2650_, v_traces_2728_);
lean_dec_ref(v_traces_2728_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 0, v___x_2732_);
v___x_2734_ = v___x_2730_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2732_);
lean_ctor_set_uint64(v_reuseFailAlloc_2740_, sizeof(void*)*1, v_tid_2727_);
v___x_2734_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
lean_object* v___x_2736_; 
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 4, v___x_2734_);
v___x_2736_ = v___x_2725_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_env_2716_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_nextMacroScope_2717_);
lean_ctor_set(v_reuseFailAlloc_2739_, 2, v_ngen_2718_);
lean_ctor_set(v_reuseFailAlloc_2739_, 3, v_auxDeclNGen_2719_);
lean_ctor_set(v_reuseFailAlloc_2739_, 4, v___x_2734_);
lean_ctor_set(v_reuseFailAlloc_2739_, 5, v_cache_2720_);
lean_ctor_set(v_reuseFailAlloc_2739_, 6, v_messages_2721_);
lean_ctor_set(v_reuseFailAlloc_2739_, 7, v_infoState_2722_);
lean_ctor_set(v_reuseFailAlloc_2739_, 8, v_snapshotTasks_2723_);
v___x_2736_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = lean_st_ref_set(v___y_2659_, v___x_2736_);
v___x_2738_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg(v_fst_2661_);
return v___x_2738_;
}
}
}
}
}
else
{
goto v___jp_2707_;
}
}
else
{
goto v___jp_2707_;
}
}
v___jp_2743_:
{
double v___x_2745_; double v___x_2746_; double v___x_2747_; uint8_t v___x_2748_; 
v___x_2745_ = lean_unbox_float(v_snd_2681_);
v___x_2746_ = lean_unbox_float(v_fst_2680_);
v___x_2747_ = lean_float_sub(v___x_2745_, v___x_2746_);
v___x_2748_ = lean_float_decLt(v___y_2744_, v___x_2747_);
v___y_2713_ = v___x_2748_;
goto v___jp_2712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___boxed(lean_object* v_cls_2761_, lean_object* v_collapsed_2762_, lean_object* v_tag_2763_, lean_object* v_opts_2764_, lean_object* v_clsEnabled_2765_, lean_object* v_oldTraces_2766_, lean_object* v_msg_2767_, lean_object* v_resStartStop_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
uint8_t v_collapsed_boxed_2777_; uint8_t v_clsEnabled_boxed_2778_; lean_object* v_res_2779_; 
v_collapsed_boxed_2777_ = lean_unbox(v_collapsed_2762_);
v_clsEnabled_boxed_2778_ = lean_unbox(v_clsEnabled_2765_);
v_res_2779_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(v_cls_2761_, v_collapsed_boxed_2777_, v_tag_2763_, v_opts_2764_, v_clsEnabled_boxed_2778_, v_oldTraces_2766_, v_msg_2767_, v_resStartStop_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v_opts_2764_);
return v_res_2779_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2(void){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1));
v___x_2784_ = l_Lean_stringToMessageData(v___x_2783_);
return v___x_2784_;
}
}
static double _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__4(void){
_start:
{
lean_object* v___x_2786_; double v___x_2787_; 
v___x_2786_ = lean_unsigned_to_nat(1000000000u);
v___x_2787_ = lean_float_of_nat(v___x_2786_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing(lean_object* v_P_2788_, lean_object* v_lhs_2789_, lean_object* v_rhs_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_){
_start:
{
lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v_options_2819_; lean_object* v_inheritedTraceOptions_2820_; uint8_t v_hasTrace_2821_; lean_object* v_cls_2822_; lean_object* v___f_2823_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; uint8_t v_____do__lift_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; 
v_options_2819_ = lean_ctor_get(v_a_2796_, 2);
v_inheritedTraceOptions_2820_ = lean_ctor_get(v_a_2796_, 13);
v_hasTrace_2821_ = lean_ctor_get_uint8(v_options_2819_, sizeof(void*)*1);
v_cls_2822_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___f_2823_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__0));
if (v_hasTrace_2821_ == 0)
{
lean_object* v___x_2942_; lean_object* v_a_2943_; uint8_t v___x_2944_; 
v___x_2942_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2822_, v_inheritedTraceOptions_2820_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
lean_dec_ref(v___x_2942_);
v___x_2944_ = lean_unbox(v_a_2943_);
lean_dec(v_a_2943_);
v_____do__lift_2921_ = v___x_2944_;
v___y_2922_ = v_a_2791_;
v___y_2923_ = v_a_2792_;
v___y_2924_ = v_a_2793_;
v___y_2925_ = v_a_2794_;
v___y_2926_ = v_a_2795_;
v___y_2927_ = v_a_2796_;
v___y_2928_ = v_a_2797_;
goto v___jp_2920_;
}
else
{
lean_object* v___f_2945_; uint8_t v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; uint8_t v___x_2949_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v_a_2953_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v_a_2965_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v_a_2983_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v_a_2998_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; 
v___f_2945_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__3));
v___x_2946_ = 0;
v___x_2947_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1));
v___x_2948_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_2949_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2820_, v_options_2819_, v___x_2948_);
if (v___x_2949_ == 0)
{
lean_object* v___x_3046_; uint8_t v___x_3047_; 
v___x_3046_ = l_Lean_trace_profiler;
v___x_3047_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(v_options_2819_, v___x_3046_);
if (v___x_3047_ == 0)
{
lean_object* v___x_3048_; lean_object* v_a_3049_; uint8_t v___x_3050_; 
v___x_3048_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2822_, v_inheritedTraceOptions_2820_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref(v___x_3048_);
v___x_3050_ = lean_unbox(v_a_3049_);
lean_dec(v_a_3049_);
v_____do__lift_2921_ = v___x_3050_;
v___y_2922_ = v_a_2791_;
v___y_2923_ = v_a_2792_;
v___y_2924_ = v_a_2793_;
v___y_2925_ = v_a_2794_;
v___y_2926_ = v_a_2795_;
v___y_2927_ = v_a_2796_;
v___y_2928_ = v_a_2797_;
goto v___jp_2920_;
}
else
{
goto v___jp_3013_;
}
}
else
{
goto v___jp_3013_;
}
v___jp_2950_:
{
lean_object* v___x_2954_; double v___x_2955_; double v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2954_ = lean_io_get_num_heartbeats();
v___x_2955_ = lean_float_of_nat(v___y_2952_);
v___x_2956_ = lean_float_of_nat(v___x_2954_);
v___x_2957_ = lean_box_float(v___x_2955_);
v___x_2958_ = lean_box_float(v___x_2956_);
v___x_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2957_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2960_, 0, v_a_2953_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
v___x_2961_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(v_cls_2822_, v___x_2946_, v___x_2947_, v_options_2819_, v___x_2949_, v___y_2951_, v___f_2945_, v___x_2960_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
return v___x_2961_;
}
v___jp_2962_:
{
lean_object* v___x_2966_; 
v___x_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2966_, 0, v_a_2965_);
v___y_2951_ = v___y_2963_;
v___y_2952_ = v___y_2964_;
v_a_2953_ = v___x_2966_;
goto v___jp_2950_;
}
v___jp_2967_:
{
if (lean_obj_tag(v___y_2970_) == 0)
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
v_a_2971_ = lean_ctor_get(v___y_2970_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___y_2970_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___y_2970_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___y_2970_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
lean_ctor_set_tag(v___x_2973_, 1);
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
v___y_2951_ = v___y_2968_;
v___y_2952_ = v___y_2969_;
v_a_2953_ = v___x_2976_;
goto v___jp_2950_;
}
}
}
else
{
lean_object* v_a_2979_; 
v_a_2979_ = lean_ctor_get(v___y_2970_, 0);
lean_inc(v_a_2979_);
lean_dec_ref(v___y_2970_);
v___y_2963_ = v___y_2968_;
v___y_2964_ = v___y_2969_;
v_a_2965_ = v_a_2979_;
goto v___jp_2962_;
}
}
v___jp_2980_:
{
lean_object* v___x_2984_; double v___x_2985_; double v___x_2986_; double v___x_2987_; double v___x_2988_; double v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2984_ = lean_io_mono_nanos_now();
v___x_2985_ = lean_float_of_nat(v___y_2981_);
v___x_2986_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__4);
v___x_2987_ = lean_float_div(v___x_2985_, v___x_2986_);
v___x_2988_ = lean_float_of_nat(v___x_2984_);
v___x_2989_ = lean_float_div(v___x_2988_, v___x_2986_);
v___x_2990_ = lean_box_float(v___x_2987_);
v___x_2991_ = lean_box_float(v___x_2989_);
v___x_2992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2990_);
lean_ctor_set(v___x_2992_, 1, v___x_2991_);
v___x_2993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2993_, 0, v_a_2983_);
lean_ctor_set(v___x_2993_, 1, v___x_2992_);
v___x_2994_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(v_cls_2822_, v___x_2946_, v___x_2947_, v_options_2819_, v___x_2949_, v___y_2982_, v___f_2945_, v___x_2993_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
return v___x_2994_;
}
v___jp_2995_:
{
lean_object* v___x_2999_; 
v___x_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2999_, 0, v_a_2998_);
v___y_2981_ = v___y_2996_;
v___y_2982_ = v___y_2997_;
v_a_2983_ = v___x_2999_;
goto v___jp_2980_;
}
v___jp_3000_:
{
if (lean_obj_tag(v___y_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3011_; 
v_a_3004_ = lean_ctor_get(v___y_3003_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___y_3003_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3006_ = v___y_3003_;
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v___y_3003_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
if (v_isShared_3007_ == 0)
{
lean_ctor_set_tag(v___x_3006_, 1);
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_a_3004_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
v___y_2981_ = v___y_3001_;
v___y_2982_ = v___y_3002_;
v_a_2983_ = v___x_3009_;
goto v___jp_2980_;
}
}
}
else
{
lean_object* v_a_3012_; 
v_a_3012_ = lean_ctor_get(v___y_3003_, 0);
lean_inc(v_a_3012_);
lean_dec_ref(v___y_3003_);
v___y_2996_ = v___y_3001_;
v___y_2997_ = v___y_3002_;
v_a_2998_ = v_a_3012_;
goto v___jp_2995_;
}
}
v___jp_3013_:
{
lean_object* v___x_3014_; lean_object* v_a_3015_; lean_object* v___x_3016_; uint8_t v___x_3017_; 
v___x_3014_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v_a_2797_);
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref(v___x_3014_);
v___x_3016_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3017_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(v_options_2819_, v___x_3016_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v_a_3020_; uint8_t v___x_3021_; 
v___x_3018_ = lean_io_mono_nanos_now();
v___x_3019_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2822_, v_inheritedTraceOptions_2820_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref(v___x_3019_);
v___x_3021_ = lean_unbox(v_a_3020_);
lean_dec(v_a_3020_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = lean_box(0);
v___x_3023_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2789_, v_rhs_2790_, v___f_2823_, v_cls_2822_, v___x_3017_, v_P_2788_, v_hasTrace_2821_, v___x_3022_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
v___y_3001_ = v___x_3018_;
v___y_3002_ = v_a_3015_;
v___y_3003_ = v___x_3023_;
goto v___jp_3000_;
}
else
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3024_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2790_);
lean_inc_ref(v_lhs_2789_);
lean_inc_ref(v_P_2788_);
v___x_3025_ = l_Lean_mkAppB(v_P_2788_, v_lhs_2789_, v_rhs_2790_);
v___x_3026_ = l_Lean_indentExpr(v___x_3025_);
v___x_3027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3024_);
lean_ctor_set(v___x_3027_, 1, v___x_3026_);
v___x_3028_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2822_, v___x_3027_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v___x_3030_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
lean_dec_ref(v___x_3028_);
v___x_3030_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2789_, v_rhs_2790_, v___f_2823_, v_cls_2822_, v___x_3017_, v_P_2788_, v_hasTrace_2821_, v_a_3029_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
v___y_3001_ = v___x_3018_;
v___y_3002_ = v_a_3015_;
v___y_3003_ = v___x_3030_;
goto v___jp_3000_;
}
else
{
lean_object* v_a_3031_; 
lean_dec_ref(v_rhs_2790_);
lean_dec_ref(v_lhs_2789_);
lean_dec_ref(v_P_2788_);
v_a_3031_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3031_);
lean_dec_ref(v___x_3028_);
v___y_2996_ = v___x_3018_;
v___y_2997_ = v_a_3015_;
v_a_2998_ = v_a_3031_;
goto v___jp_2995_;
}
}
}
else
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v_a_3034_; uint8_t v___x_3035_; 
v___x_3032_ = lean_io_get_num_heartbeats();
v___x_3033_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2822_, v_inheritedTraceOptions_2820_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3034_);
lean_dec_ref(v___x_3033_);
v___x_3035_ = lean_unbox(v_a_3034_);
lean_dec(v_a_3034_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3036_ = lean_box(0);
v___x_3037_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__8(v_lhs_2789_, v_rhs_2790_, v_P_2788_, v___x_3017_, v_cls_2822_, v___f_2823_, v___x_3036_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
v___y_2968_ = v_a_3015_;
v___y_2969_ = v___x_3032_;
v___y_2970_ = v___x_3037_;
goto v___jp_2967_;
}
else
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3038_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2790_);
lean_inc_ref(v_lhs_2789_);
lean_inc_ref(v_P_2788_);
v___x_3039_ = l_Lean_mkAppB(v_P_2788_, v_lhs_2789_, v_rhs_2790_);
v___x_3040_ = l_Lean_indentExpr(v___x_3039_);
v___x_3041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3038_);
lean_ctor_set(v___x_3041_, 1, v___x_3040_);
v___x_3042_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2822_, v___x_3041_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___x_3044_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref(v___x_3042_);
v___x_3044_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__8(v_lhs_2789_, v_rhs_2790_, v_P_2788_, v___x_3017_, v_cls_2822_, v___f_2823_, v_a_3043_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
v___y_2968_ = v_a_3015_;
v___y_2969_ = v___x_3032_;
v___y_2970_ = v___x_3044_;
goto v___jp_2967_;
}
else
{
lean_object* v_a_3045_; 
lean_dec_ref(v_rhs_2790_);
lean_dec_ref(v_lhs_2789_);
lean_dec_ref(v_P_2788_);
v_a_3045_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3045_);
lean_dec_ref(v___x_3042_);
v___y_2963_ = v_a_3015_;
v___y_2964_ = v___x_3032_;
v_a_2965_ = v_a_3045_;
goto v___jp_2962_;
}
}
}
}
}
v___jp_2799_:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
return v___x_2801_;
}
v___jp_2802_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
return v___x_2804_;
}
v___jp_2805_:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
return v___x_2807_;
}
v___jp_2808_:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2815_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8);
v___x_2816_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__9));
v___x_2817_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2817_, 0, v___y_2810_);
lean_ctor_set(v___x_2817_, 1, v___x_2815_);
lean_ctor_set(v___x_2817_, 2, v___x_2816_);
v___x_2818_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg(v___y_2809_, v___x_2817_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
return v___x_2818_;
}
v___jp_2824_:
{
lean_object* v___x_2832_; 
lean_inc_ref(v_lhs_2789_);
v___x_2832_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_lhs_2789_);
if (lean_obj_tag(v___x_2832_) == 1)
{
lean_object* v_val_2833_; lean_object* v___x_2834_; 
v_val_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_val_2833_);
lean_dec_ref(v___x_2832_);
lean_inc_ref(v_rhs_2790_);
v___x_2834_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_rhs_2790_);
if (lean_obj_tag(v___x_2834_) == 1)
{
lean_object* v_val_2835_; uint8_t v___x_2836_; 
v_val_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_val_2835_);
lean_dec_ref(v___x_2834_);
v___x_2836_ = lean_expr_eqv(v_val_2833_, v_val_2835_);
if (v___x_2836_ == 0)
{
lean_object* v_inheritedTraceOptions_2837_; lean_object* v___x_2838_; lean_object* v_a_2839_; uint8_t v___x_2840_; 
lean_dec_ref(v_P_2788_);
v_inheritedTraceOptions_2837_ = lean_ctor_get(v___y_2830_, 13);
v___x_2838_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2822_, v_inheritedTraceOptions_2837_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref(v___x_2838_);
v___x_2840_ = lean_unbox(v_a_2839_);
lean_dec(v_a_2839_);
if (v___x_2840_ == 0)
{
lean_dec(v_val_2835_);
lean_dec(v_val_2833_);
lean_dec_ref(v_rhs_2790_);
lean_dec_ref(v_lhs_2789_);
goto v___jp_2805_;
}
else
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2841_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2);
v___x_2842_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2833_);
v___x_2843_ = l_Lean_MessageData_ofExpr(v___x_2842_);
v___x_2844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2841_);
lean_ctor_set(v___x_2844_, 1, v___x_2843_);
v___x_2845_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4);
v___x_2846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2844_);
lean_ctor_set(v___x_2846_, 1, v___x_2845_);
v___x_2847_ = l_Lean_indentExpr(v_lhs_2789_);
v___x_2848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2846_);
lean_ctor_set(v___x_2848_, 1, v___x_2847_);
v___x_2849_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6);
v___x_2850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2848_);
lean_ctor_set(v___x_2850_, 1, v___x_2849_);
v___x_2851_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2835_);
v___x_2852_ = l_Lean_MessageData_ofExpr(v___x_2851_);
v___x_2853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2850_);
lean_ctor_set(v___x_2853_, 1, v___x_2852_);
v___x_2854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
lean_ctor_set(v___x_2854_, 1, v___x_2845_);
v___x_2855_ = l_Lean_indentExpr(v_rhs_2790_);
v___x_2856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2854_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2822_, v___x_2856_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_dec_ref(v___x_2857_);
goto v___jp_2805_;
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2857_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2857_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
}
else
{
lean_object* v_options_2866_; lean_object* v_inheritedTraceOptions_2867_; uint8_t v_hasTrace_2868_; lean_object* v___x_2869_; lean_object* v___f_2870_; 
lean_dec(v_val_2835_);
v_options_2866_ = lean_ctor_get(v___y_2830_, 2);
v_inheritedTraceOptions_2867_ = lean_ctor_get(v___y_2830_, 13);
v_hasTrace_2868_ = lean_ctor_get_uint8(v_options_2866_, sizeof(void*)*1);
v___x_2869_ = lean_box(v___x_2836_);
lean_inc(v_val_2833_);
v___f_2870_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___boxed), 11, 5);
lean_closure_set(v___f_2870_, 0, v_val_2833_);
lean_closure_set(v___f_2870_, 1, v_lhs_2789_);
lean_closure_set(v___f_2870_, 2, v_rhs_2790_);
lean_closure_set(v___f_2870_, 3, v_P_2788_);
lean_closure_set(v___f_2870_, 4, v___x_2869_);
if (v_hasTrace_2868_ == 0)
{
v___y_2809_ = v___f_2870_;
v___y_2810_ = v_val_2833_;
v___y_2811_ = v___y_2828_;
v___y_2812_ = v___y_2829_;
v___y_2813_ = v___y_2830_;
v___y_2814_ = v___y_2831_;
goto v___jp_2808_;
}
else
{
lean_object* v___x_2871_; uint8_t v___x_2872_; 
v___x_2871_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_2872_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2867_, v_options_2866_, v___x_2871_);
if (v___x_2872_ == 0)
{
v___y_2809_ = v___f_2870_;
v___y_2810_ = v_val_2833_;
v___y_2811_ = v___y_2828_;
v___y_2812_ = v___y_2829_;
v___y_2813_ = v___y_2830_;
v___y_2814_ = v___y_2831_;
goto v___jp_2808_;
}
else
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2873_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11);
lean_inc(v_val_2833_);
v___x_2874_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2833_);
v___x_2875_ = l_Lean_MessageData_ofExpr(v___x_2874_);
v___x_2876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2873_);
lean_ctor_set(v___x_2876_, 1, v___x_2875_);
v___x_2877_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13);
v___x_2878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2876_);
lean_ctor_set(v___x_2878_, 1, v___x_2877_);
v___x_2879_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2822_, v___x_2878_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_dec_ref(v___x_2879_);
v___y_2809_ = v___f_2870_;
v___y_2810_ = v_val_2833_;
v___y_2811_ = v___y_2828_;
v___y_2812_ = v___y_2829_;
v___y_2813_ = v___y_2830_;
v___y_2814_ = v___y_2831_;
goto v___jp_2808_;
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec_ref(v___f_2870_);
lean_dec(v_val_2833_);
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2879_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2879_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
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
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2888_; lean_object* v___x_2889_; lean_object* v_a_2890_; uint8_t v___x_2891_; 
lean_dec(v___x_2834_);
lean_dec(v_val_2833_);
lean_dec_ref(v_lhs_2789_);
lean_dec_ref(v_P_2788_);
v_inheritedTraceOptions_2888_ = lean_ctor_get(v___y_2830_, 13);
v___x_2889_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2822_, v_inheritedTraceOptions_2888_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_a_2890_);
lean_dec_ref(v___x_2889_);
v___x_2891_ = lean_unbox(v_a_2890_);
lean_dec(v_a_2890_);
if (v___x_2891_ == 0)
{
lean_dec_ref(v_rhs_2790_);
goto v___jp_2802_;
}
else
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2892_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2893_ = l_Lean_indentExpr(v_rhs_2790_);
v___x_2894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2892_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
v___x_2895_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2822_, v___x_2894_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_dec_ref(v___x_2895_);
goto v___jp_2802_;
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2895_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2895_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2904_; lean_object* v___x_2905_; lean_object* v_a_2906_; uint8_t v___x_2907_; 
lean_dec(v___x_2832_);
lean_dec_ref(v_rhs_2790_);
lean_dec_ref(v_P_2788_);
v_inheritedTraceOptions_2904_ = lean_ctor_get(v___y_2830_, 13);
v___x_2905_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2822_, v_inheritedTraceOptions_2904_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref(v___x_2905_);
v___x_2907_ = lean_unbox(v_a_2906_);
lean_dec(v_a_2906_);
if (v___x_2907_ == 0)
{
lean_dec_ref(v_lhs_2789_);
goto v___jp_2799_;
}
else
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2908_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2909_ = l_Lean_indentExpr(v_lhs_2789_);
v___x_2910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2908_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
v___x_2911_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2822_, v___x_2910_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_dec_ref(v___x_2911_);
goto v___jp_2799_;
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2911_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2911_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
}
v___jp_2920_:
{
if (v_____do__lift_2921_ == 0)
{
v___y_2825_ = v___y_2922_;
v___y_2826_ = v___y_2923_;
v___y_2827_ = v___y_2924_;
v___y_2828_ = v___y_2925_;
v___y_2829_ = v___y_2926_;
v___y_2830_ = v___y_2927_;
v___y_2831_ = v___y_2928_;
goto v___jp_2824_;
}
else
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2929_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2790_);
lean_inc_ref(v_lhs_2789_);
lean_inc_ref(v_P_2788_);
v___x_2930_ = l_Lean_mkAppB(v_P_2788_, v_lhs_2789_, v_rhs_2790_);
v___x_2931_ = l_Lean_indentExpr(v___x_2930_);
v___x_2932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2929_);
lean_ctor_set(v___x_2932_, 1, v___x_2931_);
v___x_2933_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2822_, v___x_2932_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_dec_ref(v___x_2933_);
v___y_2825_ = v___y_2922_;
v___y_2826_ = v___y_2923_;
v___y_2827_ = v___y_2924_;
v___y_2828_ = v___y_2925_;
v___y_2829_ = v___y_2926_;
v___y_2830_ = v___y_2927_;
v___y_2831_ = v___y_2928_;
goto v___jp_2824_;
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec_ref(v_rhs_2790_);
lean_dec_ref(v_lhs_2789_);
lean_dec_ref(v_P_2788_);
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2933_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2933_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___boxed(lean_object* v_P_3051_, lean_object* v_lhs_3052_, lean_object* v_rhs_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing(v_P_3051_, v_lhs_3052_, v_rhs_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
lean_dec(v_a_3060_);
lean_dec_ref(v_a_3059_);
lean_dec(v_a_3058_);
lean_dec_ref(v_a_3057_);
lean_dec(v_a_3056_);
lean_dec_ref(v_a_3055_);
lean_dec(v_a_3054_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0(lean_object* v_cls_3063_, lean_object* v_msg_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3063_, v_msg_3064_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object* v_cls_3074_, lean_object* v_msg_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0(v_cls_3074_, v_msg_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5(lean_object* v_00_u03b1_3085_, lean_object* v_x_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v___x_3095_; 
v___x_3095_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg(v_x_3086_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___boxed(lean_object* v_00_u03b1_3096_, lean_object* v_x_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_00_u03b1_3096_, v_x_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4(lean_object* v_oldTraces_3107_, lean_object* v_data_3108_, lean_object* v_ref_3109_, lean_object* v_msg_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v___x_3119_; 
v___x_3119_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_oldTraces_3107_, v_data_3108_, v_ref_3109_, v_msg_3110_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___boxed(lean_object* v_oldTraces_3120_, lean_object* v_data_3121_, lean_object* v_ref_3122_, lean_object* v_msg_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4(v_oldTraces_3120_, v_data_3121_, v_ref_3122_, v_msg_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
return v_res_3132_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__6(void){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3142_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__5));
v___x_3143_ = l_Lean_stringToMessageData(v___x_3142_);
return v___x_3143_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__7(void){
_start:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3144_ = l_Lean_checkEmoji;
v___x_3145_ = l_Lean_stringToMessageData(v___x_3144_);
return v___x_3145_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8(void){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3146_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__7);
v___x_3147_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__6);
v___x_3148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
lean_ctor_set(v___x_3148_, 1, v___x_3146_);
return v___x_3148_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__10(void){
_start:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3150_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__9));
v___x_3151_ = l_Lean_stringToMessageData(v___x_3150_);
return v___x_3151_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__11(void){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3152_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__10);
v___x_3153_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8);
v___x_3154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
lean_ctor_set(v___x_3154_, 1, v___x_3152_);
return v___x_3154_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__13(void){
_start:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3156_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__12));
v___x_3157_ = l_Lean_stringToMessageData(v___x_3156_);
return v___x_3157_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__14(void){
_start:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3158_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__13);
v___x_3159_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8);
v___x_3160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
lean_ctor_set(v___x_3160_, 1, v___x_3158_);
return v___x_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost(lean_object* v_e_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_){
_start:
{
lean_object* v___x_3170_; 
v___x_3170_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3161_, v_a_3166_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3277_; 
v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3173_ = v___x_3170_;
v_isShared_3174_ = v_isSharedCheck_3277_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3170_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3277_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3180_; uint8_t v___x_3181_; 
v___x_3180_ = l_Lean_Expr_cleanupAnnotations(v_a_3171_);
v___x_3181_ = l_Lean_Expr_isApp(v___x_3180_);
if (v___x_3181_ == 0)
{
lean_dec_ref(v___x_3180_);
goto v___jp_3175_;
}
else
{
lean_object* v_arg_3182_; lean_object* v___x_3183_; uint8_t v___x_3184_; 
v_arg_3182_ = lean_ctor_get(v___x_3180_, 1);
lean_inc_ref(v_arg_3182_);
v___x_3183_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3180_);
v___x_3184_ = l_Lean_Expr_isApp(v___x_3183_);
if (v___x_3184_ == 0)
{
lean_dec_ref(v___x_3183_);
lean_dec_ref(v_arg_3182_);
goto v___jp_3175_;
}
else
{
lean_object* v_arg_3185_; lean_object* v___x_3186_; uint8_t v___x_3187_; 
v_arg_3185_ = lean_ctor_get(v___x_3183_, 1);
lean_inc_ref(v_arg_3185_);
v___x_3186_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3183_);
v___x_3187_ = l_Lean_Expr_isApp(v___x_3186_);
if (v___x_3187_ == 0)
{
lean_dec_ref(v___x_3186_);
lean_dec_ref(v_arg_3185_);
lean_dec_ref(v_arg_3182_);
goto v___jp_3175_;
}
else
{
lean_object* v_arg_3188_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___x_3213_; lean_object* v___x_3214_; uint8_t v___x_3215_; 
v_arg_3188_ = lean_ctor_get(v___x_3186_, 1);
lean_inc_ref(v_arg_3188_);
v___x_3213_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3186_);
v___x_3214_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__1));
v___x_3215_ = l_Lean_Expr_isConstOf(v___x_3213_, v___x_3214_);
if (v___x_3215_ == 0)
{
uint8_t v___x_3216_; 
v___x_3216_ = l_Lean_Expr_isApp(v___x_3213_);
if (v___x_3216_ == 0)
{
lean_dec_ref(v___x_3213_);
lean_dec_ref(v_arg_3188_);
lean_dec_ref(v_arg_3185_);
lean_dec_ref(v_arg_3182_);
goto v___jp_3175_;
}
else
{
lean_object* v_arg_3217_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___x_3242_; lean_object* v___x_3243_; uint8_t v___x_3244_; 
v_arg_3217_ = lean_ctor_get(v___x_3213_, 1);
lean_inc_ref(v_arg_3217_);
v___x_3242_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3213_);
v___x_3243_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__4));
v___x_3244_ = l_Lean_Expr_isConstOf(v___x_3242_, v___x_3243_);
lean_dec_ref(v___x_3242_);
if (v___x_3244_ == 0)
{
lean_dec_ref(v_arg_3217_);
lean_dec_ref(v_arg_3188_);
lean_dec_ref(v_arg_3185_);
lean_dec_ref(v_arg_3182_);
goto v___jp_3175_;
}
else
{
lean_object* v_options_3245_; uint8_t v_hasTrace_3246_; 
lean_del_object(v___x_3173_);
v_options_3245_ = lean_ctor_get(v_a_3167_, 2);
v_hasTrace_3246_ = lean_ctor_get_uint8(v_options_3245_, sizeof(void*)*1);
if (v_hasTrace_3246_ == 0)
{
v___y_3219_ = v_a_3162_;
v___y_3220_ = v_a_3163_;
v___y_3221_ = v_a_3164_;
v___y_3222_ = v_a_3165_;
v___y_3223_ = v_a_3166_;
v___y_3224_ = v_a_3167_;
v___y_3225_ = v_a_3168_;
goto v___jp_3218_;
}
else
{
lean_object* v_inheritedTraceOptions_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; uint8_t v___x_3250_; 
v_inheritedTraceOptions_3247_ = lean_ctor_get(v_a_3167_, 13);
v___x_3248_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3249_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3250_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3247_, v_options_3245_, v___x_3249_);
if (v___x_3250_ == 0)
{
v___y_3219_ = v_a_3162_;
v___y_3220_ = v_a_3163_;
v___y_3221_ = v_a_3164_;
v___y_3222_ = v_a_3165_;
v___y_3223_ = v_a_3166_;
v___y_3224_ = v_a_3167_;
v___y_3225_ = v_a_3168_;
goto v___jp_3218_;
}
else
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__11);
v___x_3252_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3248_, v___x_3251_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_dec_ref(v___x_3252_);
v___y_3219_ = v_a_3162_;
v___y_3220_ = v_a_3163_;
v___y_3221_ = v_a_3164_;
v___y_3222_ = v_a_3165_;
v___y_3223_ = v_a_3166_;
v___y_3224_ = v_a_3167_;
v___y_3225_ = v_a_3168_;
goto v___jp_3218_;
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_dec_ref(v_arg_3217_);
lean_dec_ref(v_arg_3188_);
lean_dec_ref(v_arg_3185_);
lean_dec_ref(v_arg_3182_);
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3252_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3252_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
}
}
v___jp_3218_:
{
lean_object* v___x_3226_; 
lean_inc_ref(v_arg_3217_);
v___x_3226_ = l_Lean_Meta_getDecLevel(v_arg_3217_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_a_3227_);
lean_dec_ref(v___x_3226_);
v___x_3228_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__4));
v___x_3229_ = lean_box(0);
v___x_3230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3230_, 0, v_a_3227_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
v___x_3231_ = l_Lean_Expr_const___override(v___x_3228_, v___x_3230_);
v___x_3232_ = l_Lean_mkAppB(v___x_3231_, v_arg_3217_, v_arg_3188_);
v___x_3233_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing(v___x_3232_, v_arg_3185_, v_arg_3182_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
return v___x_3233_;
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec_ref(v_arg_3217_);
lean_dec_ref(v_arg_3188_);
lean_dec_ref(v_arg_3185_);
lean_dec_ref(v_arg_3182_);
v_a_3234_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3226_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3226_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
}
}
else
{
lean_object* v_options_3261_; uint8_t v_hasTrace_3262_; 
lean_dec_ref(v___x_3213_);
lean_del_object(v___x_3173_);
v_options_3261_ = lean_ctor_get(v_a_3167_, 2);
v_hasTrace_3262_ = lean_ctor_get_uint8(v_options_3261_, sizeof(void*)*1);
if (v_hasTrace_3262_ == 0)
{
v___y_3190_ = v_a_3162_;
v___y_3191_ = v_a_3163_;
v___y_3192_ = v_a_3164_;
v___y_3193_ = v_a_3165_;
v___y_3194_ = v_a_3166_;
v___y_3195_ = v_a_3167_;
v___y_3196_ = v_a_3168_;
goto v___jp_3189_;
}
else
{
lean_object* v_inheritedTraceOptions_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; uint8_t v___x_3266_; 
v_inheritedTraceOptions_3263_ = lean_ctor_get(v_a_3167_, 13);
v___x_3264_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3265_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3266_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3263_, v_options_3261_, v___x_3265_);
if (v___x_3266_ == 0)
{
v___y_3190_ = v_a_3162_;
v___y_3191_ = v_a_3163_;
v___y_3192_ = v_a_3164_;
v___y_3193_ = v_a_3165_;
v___y_3194_ = v_a_3166_;
v___y_3195_ = v_a_3167_;
v___y_3196_ = v_a_3168_;
goto v___jp_3189_;
}
else
{
lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3267_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__14, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__14_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__14);
v___x_3268_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3264_, v___x_3267_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_dec_ref(v___x_3268_);
v___y_3190_ = v_a_3162_;
v___y_3191_ = v_a_3163_;
v___y_3192_ = v_a_3164_;
v___y_3193_ = v_a_3165_;
v___y_3194_ = v_a_3166_;
v___y_3195_ = v_a_3167_;
v___y_3196_ = v_a_3168_;
goto v___jp_3189_;
}
else
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3276_; 
lean_dec_ref(v_arg_3188_);
lean_dec_ref(v_arg_3185_);
lean_dec_ref(v_arg_3182_);
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3271_ = v___x_3268_;
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3268_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3272_ == 0)
{
v___x_3274_ = v___x_3271_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_a_3269_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
}
}
v___jp_3189_:
{
lean_object* v___x_3197_; 
lean_inc_ref(v_arg_3188_);
v___x_3197_ = l_Lean_Meta_getLevel(v_arg_3188_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_a_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_a_3198_);
lean_dec_ref(v___x_3197_);
v___x_3199_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__1));
v___x_3200_ = lean_box(0);
v___x_3201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3201_, 0, v_a_3198_);
lean_ctor_set(v___x_3201_, 1, v___x_3200_);
v___x_3202_ = l_Lean_Expr_const___override(v___x_3199_, v___x_3201_);
v___x_3203_ = l_Lean_Expr_app___override(v___x_3202_, v_arg_3188_);
v___x_3204_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing(v___x_3203_, v_arg_3185_, v_arg_3182_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
return v___x_3204_;
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_dec_ref(v_arg_3188_);
lean_dec_ref(v_arg_3185_);
lean_dec_ref(v_arg_3182_);
v_a_3205_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3197_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3197_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
}
}
}
v___jp_3175_:
{
lean_object* v___x_3176_; lean_object* v___x_3178_; 
v___x_3176_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 0, v___x_3176_);
v___x_3178_ = v___x_3173_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3176_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
else
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3285_; 
v_a_3278_ = lean_ctor_get(v___x_3170_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3280_ = v___x_3170_;
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3170_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3283_; 
if (v_isShared_3281_ == 0)
{
v___x_3283_ = v___x_3280_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___boxed(lean_object* v_e_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost(v_e_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
lean_dec(v_a_3293_);
lean_dec_ref(v_a_3292_);
lean_dec(v_a_3291_);
lean_dec_ref(v_a_3290_);
lean_dec(v_a_3289_);
lean_dec_ref(v_a_3288_);
lean_dec(v_a_3287_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__0(lean_object* v_x_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3305_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__0___boxed(lean_object* v_x_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__0(v_x_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec_ref(v_x_3307_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1(lean_object* v_x_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3328_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1___closed__0));
v___x_3329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3328_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1___boxed(lean_object* v_x_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1(v_x_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v_x_3330_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__2(lean_object* v_e_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3349_, 0, v_e_3340_);
v___x_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__2___boxed(lean_object* v_e_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__2(v_e_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v___y_3352_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__3(lean_object* v_x_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3370_ = lean_box(0);
v___x_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3370_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__3___boxed(lean_object* v_x_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__3(v_x_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec_ref(v_x_3372_);
return v_res_3381_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__5(void){
_start:
{
lean_object* v___x_3388_; 
v___x_3388_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3388_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6(void){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3389_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__5);
v___x_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
return v___x_3390_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__7(void){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3391_ = lean_unsigned_to_nat(0u);
v___x_3392_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6);
v___x_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
lean_ctor_set(v___x_3393_, 1, v___x_3391_);
return v___x_3393_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__8(void){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3394_ = lean_unsigned_to_nat(32u);
v___x_3395_ = lean_mk_empty_array_with_capacity(v___x_3394_);
v___x_3396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
return v___x_3396_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__9(void){
_start:
{
size_t v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3397_ = ((size_t)5ULL);
v___x_3398_ = lean_unsigned_to_nat(0u);
v___x_3399_ = lean_unsigned_to_nat(32u);
v___x_3400_ = lean_mk_empty_array_with_capacity(v___x_3399_);
v___x_3401_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__8);
v___x_3402_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
lean_ctor_set(v___x_3402_, 1, v___x_3400_);
lean_ctor_set(v___x_3402_, 2, v___x_3398_);
lean_ctor_set(v___x_3402_, 3, v___x_3398_);
lean_ctor_set_usize(v___x_3402_, 4, v___x_3397_);
return v___x_3402_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__10(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3403_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__9);
v___x_3404_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6);
v___x_3405_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
lean_ctor_set(v___x_3405_, 1, v___x_3404_);
lean_ctor_set(v___x_3405_, 2, v___x_3404_);
lean_ctor_set(v___x_3405_, 3, v___x_3403_);
return v___x_3405_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3406_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__10);
v___x_3407_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__7);
v___x_3408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
lean_ctor_set(v___x_3408_, 1, v___x_3406_);
return v___x_3408_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__12(void){
_start:
{
uint8_t v___x_3409_; lean_object* v___f_3410_; lean_object* v___f_3411_; lean_object* v___f_3412_; lean_object* v___x_3413_; lean_object* v___f_3414_; lean_object* v___x_3415_; 
v___x_3409_ = 1;
v___f_3410_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__4));
v___f_3411_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__3));
v___f_3412_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__2));
v___x_3413_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___boxed), 9, 0);
v___f_3414_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__1));
v___x_3415_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3415_, 0, v___f_3414_);
lean_ctor_set(v___x_3415_, 1, v___x_3413_);
lean_ctor_set(v___x_3415_, 2, v___f_3412_);
lean_ctor_set(v___x_3415_, 3, v___f_3411_);
lean_ctor_set(v___x_3415_, 4, v___f_3410_);
lean_ctor_set_uint8(v___x_3415_, sizeof(void*)*5, v___x_3409_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget(lean_object* v_mvarId_3416_, lean_object* v_maxSteps_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_){
_start:
{
lean_object* v___x_3423_; 
v___x_3423_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_3421_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; lean_object* v___x_3425_; lean_object* v_maxDischargeDepth_3426_; uint8_t v_contextual_3427_; uint8_t v_memoize_3428_; uint8_t v_singlePass_3429_; uint8_t v_zeta_3430_; uint8_t v_beta_3431_; uint8_t v_eta_3432_; uint8_t v_etaStruct_3433_; uint8_t v_iota_3434_; uint8_t v_proj_3435_; uint8_t v_decide_3436_; uint8_t v_arith_3437_; uint8_t v_autoUnfold_3438_; uint8_t v_dsimp_3439_; uint8_t v_failIfUnchanged_3440_; uint8_t v_ground_3441_; uint8_t v_unfoldPartialApp_3442_; uint8_t v_zetaDelta_3443_; uint8_t v_index_3444_; uint8_t v_implicitDefEqProofs_3445_; uint8_t v_zetaUnused_3446_; uint8_t v_catchRuntime_3447_; uint8_t v_zetaHave_3448_; uint8_t v_letToHave_3449_; uint8_t v_congrConsts_3450_; uint8_t v_bitVecOfNat_3451_; uint8_t v_warnExponents_3452_; uint8_t v_suggestions_3453_; lean_object* v_maxSuggestions_3454_; uint8_t v_locals_3455_; uint8_t v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
lean_dec_ref(v___x_3423_);
v___x_3425_ = l_Lean_Meta_Simp_neutralConfig;
v_maxDischargeDepth_3426_ = lean_ctor_get(v___x_3425_, 1);
v_contextual_3427_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3);
v_memoize_3428_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 1);
v_singlePass_3429_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 2);
v_zeta_3430_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 3);
v_beta_3431_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 4);
v_eta_3432_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 5);
v_etaStruct_3433_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 6);
v_iota_3434_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 7);
v_proj_3435_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 8);
v_decide_3436_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 9);
v_arith_3437_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 10);
v_autoUnfold_3438_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 11);
v_dsimp_3439_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 12);
v_failIfUnchanged_3440_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 13);
v_ground_3441_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_3442_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 15);
v_zetaDelta_3443_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 16);
v_index_3444_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_3445_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 18);
v_zetaUnused_3446_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 19);
v_catchRuntime_3447_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 20);
v_zetaHave_3448_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 21);
v_letToHave_3449_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 22);
v_congrConsts_3450_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 23);
v_bitVecOfNat_3451_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 24);
v_warnExponents_3452_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 25);
v_suggestions_3453_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 26);
v_maxSuggestions_3454_ = lean_ctor_get(v___x_3425_, 2);
v_locals_3455_ = lean_ctor_get_uint8(v___x_3425_, sizeof(void*)*3 + 27);
v___x_3456_ = 1;
lean_inc(v_maxSuggestions_3454_);
lean_inc(v_maxDischargeDepth_3426_);
v___x_3457_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_3457_, 0, v_maxSteps_3417_);
lean_ctor_set(v___x_3457_, 1, v_maxDischargeDepth_3426_);
lean_ctor_set(v___x_3457_, 2, v_maxSuggestions_3454_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3, v_contextual_3427_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 1, v_memoize_3428_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 2, v_singlePass_3429_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 3, v_zeta_3430_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 4, v_beta_3431_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 5, v_eta_3432_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 6, v_etaStruct_3433_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 7, v_iota_3434_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 8, v_proj_3435_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 9, v_decide_3436_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 10, v_arith_3437_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 11, v_autoUnfold_3438_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 12, v_dsimp_3439_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 13, v_failIfUnchanged_3440_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 14, v_ground_3441_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 15, v_unfoldPartialApp_3442_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 16, v_zetaDelta_3443_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 17, v_index_3444_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_3445_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 19, v_zetaUnused_3446_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 20, v_catchRuntime_3447_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 21, v_zetaHave_3448_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 22, v_letToHave_3449_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 23, v_congrConsts_3450_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 24, v_bitVecOfNat_3451_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 25, v_warnExponents_3452_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 26, v_suggestions_3453_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 27, v_locals_3455_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*3 + 28, v___x_3456_);
v___x_3458_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__0));
v___x_3459_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_3457_, v___x_3458_, v_a_3424_, v_a_3418_, v_a_3420_, v_a_3421_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v___x_3461_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref(v___x_3459_);
lean_inc(v_mvarId_3416_);
v___x_3461_ = l_Lean_MVarId_getType(v_mvarId_3416_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; lean_object* v___x_3463_; lean_object* v_a_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref(v___x_3461_);
v___x_3463_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(v_a_3462_, v_a_3419_);
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc_n(v_a_3464_, 2);
lean_dec_ref(v___x_3463_);
v___x_3465_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11);
v___x_3466_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__12);
v___x_3467_ = l_Lean_Meta_Simp_main(v_a_3464_, v_a_3460_, v___x_3465_, v___x_3466_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; lean_object* v_fst_3469_; lean_object* v___x_3470_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3468_);
lean_dec_ref(v___x_3467_);
v_fst_3469_ = lean_ctor_get(v_a_3468_, 0);
lean_inc(v_fst_3469_);
lean_dec(v_a_3468_);
v___x_3470_ = l_Lean_Meta_applySimpResultToTarget(v_mvarId_3416_, v_a_3464_, v_fst_3469_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_);
lean_dec(v_a_3464_);
return v___x_3470_;
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec(v_a_3464_);
lean_dec(v_mvarId_3416_);
v_a_3471_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3467_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3467_);
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
lean_dec(v_a_3460_);
lean_dec(v_mvarId_3416_);
v_a_3479_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3461_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3461_);
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
lean_dec(v_mvarId_3416_);
v_a_3487_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___x_3459_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3459_);
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
else
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
lean_dec(v_maxSteps_3417_);
lean_dec(v_mvarId_3416_);
v_a_3495_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3497_ = v___x_3423_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3423_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3495_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___boxed(lean_object* v_mvarId_3503_, lean_object* v_maxSteps_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget(v_mvarId_3503_, v_maxSteps_3504_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_);
lean_dec(v_a_3508_);
lean_dec_ref(v_a_3507_);
lean_dec(v_a_3506_);
lean_dec_ref(v_a_3505_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg(lean_object* v_mvarId_3511_, lean_object* v_x_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3511_, v_x_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_3518_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3518_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3519_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3534_; 
v_a_3527_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3529_ = v___x_3518_;
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3518_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3532_; 
if (v_isShared_3530_ == 0)
{
v___x_3532_ = v___x_3529_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3527_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg___boxed(lean_object* v_mvarId_3535_, lean_object* v_x_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg(v_mvarId_3535_, v_x_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0(lean_object* v_00_u03b1_3543_, lean_object* v_mvarId_3544_, lean_object* v_x_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v___x_3551_; 
v___x_3551_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg(v_mvarId_3544_, v_x_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___boxed(lean_object* v_00_u03b1_3552_, lean_object* v_mvarId_3553_, lean_object* v_x_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0(v_00_u03b1_3552_, v_mvarId_3553_, v_x_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___lam__4(lean_object* v_maxSteps_3561_, lean_object* v_fvarId_3562_, lean_object* v___f_3563_, lean_object* v___f_3564_, lean_object* v___f_3565_, lean_object* v___f_3566_, lean_object* v_goal_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
lean_object* v___x_3573_; 
v___x_3573_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_3571_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_a_3574_; lean_object* v___x_3575_; lean_object* v_maxDischargeDepth_3576_; uint8_t v_contextual_3577_; uint8_t v_memoize_3578_; uint8_t v_singlePass_3579_; uint8_t v_zeta_3580_; uint8_t v_beta_3581_; uint8_t v_eta_3582_; uint8_t v_etaStruct_3583_; uint8_t v_iota_3584_; uint8_t v_proj_3585_; uint8_t v_decide_3586_; uint8_t v_arith_3587_; uint8_t v_autoUnfold_3588_; uint8_t v_dsimp_3589_; uint8_t v_failIfUnchanged_3590_; uint8_t v_ground_3591_; uint8_t v_unfoldPartialApp_3592_; uint8_t v_zetaDelta_3593_; uint8_t v_index_3594_; uint8_t v_implicitDefEqProofs_3595_; uint8_t v_zetaUnused_3596_; uint8_t v_catchRuntime_3597_; uint8_t v_zetaHave_3598_; uint8_t v_letToHave_3599_; uint8_t v_congrConsts_3600_; uint8_t v_bitVecOfNat_3601_; uint8_t v_warnExponents_3602_; uint8_t v_suggestions_3603_; lean_object* v_maxSuggestions_3604_; uint8_t v_locals_3605_; uint8_t v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
lean_inc(v_a_3574_);
lean_dec_ref(v___x_3573_);
v___x_3575_ = l_Lean_Meta_Simp_neutralConfig;
v_maxDischargeDepth_3576_ = lean_ctor_get(v___x_3575_, 1);
v_contextual_3577_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3);
v_memoize_3578_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 1);
v_singlePass_3579_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 2);
v_zeta_3580_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 3);
v_beta_3581_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 4);
v_eta_3582_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 5);
v_etaStruct_3583_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 6);
v_iota_3584_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 7);
v_proj_3585_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 8);
v_decide_3586_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 9);
v_arith_3587_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 10);
v_autoUnfold_3588_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 11);
v_dsimp_3589_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 12);
v_failIfUnchanged_3590_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 13);
v_ground_3591_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_3592_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 15);
v_zetaDelta_3593_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 16);
v_index_3594_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_3595_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 18);
v_zetaUnused_3596_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 19);
v_catchRuntime_3597_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 20);
v_zetaHave_3598_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 21);
v_letToHave_3599_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 22);
v_congrConsts_3600_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 23);
v_bitVecOfNat_3601_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 24);
v_warnExponents_3602_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 25);
v_suggestions_3603_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 26);
v_maxSuggestions_3604_ = lean_ctor_get(v___x_3575_, 2);
v_locals_3605_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*3 + 27);
v___x_3606_ = 1;
lean_inc(v_maxSuggestions_3604_);
lean_inc(v_maxDischargeDepth_3576_);
v___x_3607_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_3607_, 0, v_maxSteps_3561_);
lean_ctor_set(v___x_3607_, 1, v_maxDischargeDepth_3576_);
lean_ctor_set(v___x_3607_, 2, v_maxSuggestions_3604_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3, v_contextual_3577_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 1, v_memoize_3578_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 2, v_singlePass_3579_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 3, v_zeta_3580_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 4, v_beta_3581_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 5, v_eta_3582_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 6, v_etaStruct_3583_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 7, v_iota_3584_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 8, v_proj_3585_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 9, v_decide_3586_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 10, v_arith_3587_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 11, v_autoUnfold_3588_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 12, v_dsimp_3589_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 13, v_failIfUnchanged_3590_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 14, v_ground_3591_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 15, v_unfoldPartialApp_3592_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 16, v_zetaDelta_3593_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 17, v_index_3594_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_3595_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 19, v_zetaUnused_3596_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 20, v_catchRuntime_3597_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 21, v_zetaHave_3598_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 22, v_letToHave_3599_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 23, v_congrConsts_3600_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 24, v_bitVecOfNat_3601_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 25, v_warnExponents_3602_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 26, v_suggestions_3603_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 27, v_locals_3605_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*3 + 28, v___x_3606_);
v___x_3608_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__0));
v___x_3609_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_3607_, v___x_3608_, v_a_3574_, v___y_3568_, v___y_3570_, v___y_3571_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; lean_object* v___x_3611_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3610_);
lean_dec_ref(v___x_3609_);
lean_inc(v_fvarId_3562_);
v___x_3611_ = l_Lean_FVarId_getType___redArg(v_fvarId_3562_, v___y_3568_, v___y_3570_, v___y_3571_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; lean_object* v___x_3613_; lean_object* v_a_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_a_3612_);
lean_dec_ref(v___x_3611_);
v___x_3613_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(v_a_3612_, v___y_3569_);
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_a_3614_);
lean_dec_ref(v___x_3613_);
v___x_3615_ = lean_unsigned_to_nat(32u);
v___x_3616_ = lean_mk_empty_array_with_capacity(v___x_3615_);
lean_dec_ref(v___x_3616_);
v___x_3617_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11);
v___x_3618_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___boxed), 9, 0);
v___x_3619_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3619_, 0, v___f_3563_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
lean_ctor_set(v___x_3619_, 2, v___f_3564_);
lean_ctor_set(v___x_3619_, 3, v___f_3565_);
lean_ctor_set(v___x_3619_, 4, v___f_3566_);
lean_ctor_set_uint8(v___x_3619_, sizeof(void*)*5, v___x_3606_);
v___x_3620_ = l_Lean_Meta_Simp_main(v_a_3614_, v_a_3610_, v___x_3617_, v___x_3619_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; lean_object* v_fst_3622_; uint8_t v___x_3623_; lean_object* v___x_3624_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_a_3621_);
lean_dec_ref(v___x_3620_);
v_fst_3622_ = lean_ctor_get(v_a_3621_, 0);
lean_inc(v_fst_3622_);
lean_dec(v_a_3621_);
v___x_3623_ = 0;
v___x_3624_ = l_Lean_Meta_applySimpResultToLocalDecl(v_goal_3567_, v_fvarId_3562_, v_fst_3622_, v___x_3623_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3645_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3627_ = v___x_3624_;
v_isShared_3628_ = v_isSharedCheck_3645_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3624_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3645_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
if (lean_obj_tag(v_a_3625_) == 0)
{
lean_object* v___x_3629_; lean_object* v___x_3631_; 
v___x_3629_ = lean_box(0);
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 0, v___x_3629_);
v___x_3631_ = v___x_3627_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3629_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
else
{
lean_object* v_val_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3644_; 
v_val_3633_ = lean_ctor_get(v_a_3625_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v_a_3625_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3635_ = v_a_3625_;
v_isShared_3636_ = v_isSharedCheck_3644_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_val_3633_);
lean_dec(v_a_3625_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3644_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v_snd_3637_; lean_object* v___x_3639_; 
v_snd_3637_ = lean_ctor_get(v_val_3633_, 1);
lean_inc(v_snd_3637_);
lean_dec(v_val_3633_);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 0, v_snd_3637_);
v___x_3639_ = v___x_3635_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_snd_3637_);
v___x_3639_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
lean_object* v___x_3641_; 
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 0, v___x_3639_);
v___x_3641_ = v___x_3627_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v___x_3639_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
}
}
}
else
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
v_a_3646_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3624_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3624_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3646_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
else
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3661_; 
lean_dec(v_goal_3567_);
lean_dec(v_fvarId_3562_);
v_a_3654_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3656_ = v___x_3620_;
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3620_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3659_; 
if (v_isShared_3657_ == 0)
{
v___x_3659_ = v___x_3656_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
}
else
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3669_; 
lean_dec(v_a_3610_);
lean_dec(v_goal_3567_);
lean_dec_ref(v___f_3566_);
lean_dec_ref(v___f_3565_);
lean_dec_ref(v___f_3564_);
lean_dec_ref(v___f_3563_);
lean_dec(v_fvarId_3562_);
v_a_3662_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3664_ = v___x_3611_;
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3611_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3667_; 
if (v_isShared_3665_ == 0)
{
v___x_3667_ = v___x_3664_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3662_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
lean_dec(v_goal_3567_);
lean_dec_ref(v___f_3566_);
lean_dec_ref(v___f_3565_);
lean_dec_ref(v___f_3564_);
lean_dec_ref(v___f_3563_);
lean_dec(v_fvarId_3562_);
v_a_3670_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3609_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3609_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_dec(v_goal_3567_);
lean_dec_ref(v___f_3566_);
lean_dec_ref(v___f_3565_);
lean_dec_ref(v___f_3564_);
lean_dec_ref(v___f_3563_);
lean_dec(v_fvarId_3562_);
lean_dec(v_maxSteps_3561_);
v_a_3678_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3573_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3573_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___lam__4___boxed(lean_object* v_maxSteps_3686_, lean_object* v_fvarId_3687_, lean_object* v___f_3688_, lean_object* v___f_3689_, lean_object* v___f_3690_, lean_object* v___f_3691_, lean_object* v_goal_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_){
_start:
{
lean_object* v_res_3698_; 
v_res_3698_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___lam__4(v_maxSteps_3686_, v_fvarId_3687_, v___f_3688_, v___f_3689_, v___f_3690_, v___f_3691_, v_goal_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec(v___y_3694_);
lean_dec_ref(v___y_3693_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta(lean_object* v_goal_3699_, lean_object* v_fvarId_3700_, lean_object* v_maxSteps_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_){
_start:
{
lean_object* v___f_3707_; lean_object* v___f_3708_; lean_object* v___f_3709_; lean_object* v___f_3710_; lean_object* v___f_3711_; lean_object* v___x_3712_; 
v___f_3707_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__4));
v___f_3708_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__3));
v___f_3709_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__2));
v___f_3710_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__1));
lean_inc(v_goal_3699_);
v___f_3711_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___lam__4___boxed), 12, 7);
lean_closure_set(v___f_3711_, 0, v_maxSteps_3701_);
lean_closure_set(v___f_3711_, 1, v_fvarId_3700_);
lean_closure_set(v___f_3711_, 2, v___f_3710_);
lean_closure_set(v___f_3711_, 3, v___f_3709_);
lean_closure_set(v___f_3711_, 4, v___f_3708_);
lean_closure_set(v___f_3711_, 5, v___f_3707_);
lean_closure_set(v___f_3711_, 6, v_goal_3699_);
v___x_3712_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg(v_goal_3699_, v___f_3711_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_);
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___boxed(lean_object* v_goal_3713_, lean_object* v_fvarId_3714_, lean_object* v_maxSteps_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta(v_goal_3713_, v_fvarId_3714_, v_maxSteps_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_);
lean_dec(v_a_3719_);
lean_dec_ref(v_a_3718_);
lean_dec(v_a_3717_);
lean_dec_ref(v_a_3716_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0(lean_object* v_x_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v___x_3730_; 
lean_inc(v___y_3724_);
lean_inc_ref(v___y_3723_);
v___x_3730_ = lean_apply_7(v_x_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, lean_box(0));
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0___boxed(lean_object* v_x_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0(v_x_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(lean_object* v_mvarId_3740_, lean_object* v_x_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v___f_3749_; lean_object* v___x_3750_; 
lean_inc(v___y_3743_);
lean_inc_ref(v___y_3742_);
v___f_3749_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3749_, 0, v_x_3741_);
lean_closure_set(v___f_3749_, 1, v___y_3742_);
lean_closure_set(v___f_3749_, 2, v___y_3743_);
v___x_3750_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3740_, v___f_3749_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_);
if (lean_obj_tag(v___x_3750_) == 0)
{
return v___x_3750_;
}
else
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3758_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3753_ = v___x_3750_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3750_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
if (v_isShared_3754_ == 0)
{
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_a_3751_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___boxed(lean_object* v_mvarId_3759_, lean_object* v_x_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(v_mvarId_3759_, v_x_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
lean_dec(v___y_3766_);
lean_dec_ref(v___y_3765_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4(lean_object* v_00_u03b1_3769_, lean_object* v_mvarId_3770_, lean_object* v_x_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(v_mvarId_3770_, v_x_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___boxed(lean_object* v_00_u03b1_3780_, lean_object* v_mvarId_3781_, lean_object* v_x_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v_res_3790_; 
v_res_3790_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4(v_00_u03b1_3780_, v_mvarId_3781_, v_x_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
return v_res_3790_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(lean_object* v_a_3791_, lean_object* v_x_3792_){
_start:
{
if (lean_obj_tag(v_x_3792_) == 0)
{
uint8_t v___x_3793_; 
v___x_3793_ = 0;
return v___x_3793_;
}
else
{
lean_object* v_key_3794_; lean_object* v_tail_3795_; uint8_t v___x_3796_; 
v_key_3794_ = lean_ctor_get(v_x_3792_, 0);
v_tail_3795_ = lean_ctor_get(v_x_3792_, 2);
v___x_3796_ = l_Lean_instBEqFVarId_beq(v_key_3794_, v_a_3791_);
if (v___x_3796_ == 0)
{
v_x_3792_ = v_tail_3795_;
goto _start;
}
else
{
return v___x_3796_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg___boxed(lean_object* v_a_3798_, lean_object* v_x_3799_){
_start:
{
uint8_t v_res_3800_; lean_object* v_r_3801_; 
v_res_3800_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_3798_, v_x_3799_);
lean_dec(v_x_3799_);
lean_dec(v_a_3798_);
v_r_3801_ = lean_box(v_res_3800_);
return v_r_3801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(lean_object* v_x_3802_, lean_object* v_x_3803_){
_start:
{
if (lean_obj_tag(v_x_3803_) == 0)
{
return v_x_3802_;
}
else
{
lean_object* v_key_3804_; lean_object* v_value_3805_; lean_object* v_tail_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3829_; 
v_key_3804_ = lean_ctor_get(v_x_3803_, 0);
v_value_3805_ = lean_ctor_get(v_x_3803_, 1);
v_tail_3806_ = lean_ctor_get(v_x_3803_, 2);
v_isSharedCheck_3829_ = !lean_is_exclusive(v_x_3803_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3808_ = v_x_3803_;
v_isShared_3809_ = v_isSharedCheck_3829_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_tail_3806_);
lean_inc(v_value_3805_);
lean_inc(v_key_3804_);
lean_dec(v_x_3803_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3829_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3810_; uint64_t v___x_3811_; uint64_t v___x_3812_; uint64_t v___x_3813_; uint64_t v_fold_3814_; uint64_t v___x_3815_; uint64_t v___x_3816_; uint64_t v___x_3817_; size_t v___x_3818_; size_t v___x_3819_; size_t v___x_3820_; size_t v___x_3821_; size_t v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3825_; 
v___x_3810_ = lean_array_get_size(v_x_3802_);
v___x_3811_ = l_Lean_instHashableFVarId_hash(v_key_3804_);
v___x_3812_ = 32ULL;
v___x_3813_ = lean_uint64_shift_right(v___x_3811_, v___x_3812_);
v_fold_3814_ = lean_uint64_xor(v___x_3811_, v___x_3813_);
v___x_3815_ = 16ULL;
v___x_3816_ = lean_uint64_shift_right(v_fold_3814_, v___x_3815_);
v___x_3817_ = lean_uint64_xor(v_fold_3814_, v___x_3816_);
v___x_3818_ = lean_uint64_to_usize(v___x_3817_);
v___x_3819_ = lean_usize_of_nat(v___x_3810_);
v___x_3820_ = ((size_t)1ULL);
v___x_3821_ = lean_usize_sub(v___x_3819_, v___x_3820_);
v___x_3822_ = lean_usize_land(v___x_3818_, v___x_3821_);
v___x_3823_ = lean_array_uget_borrowed(v_x_3802_, v___x_3822_);
lean_inc(v___x_3823_);
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 2, v___x_3823_);
v___x_3825_ = v___x_3808_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_key_3804_);
lean_ctor_set(v_reuseFailAlloc_3828_, 1, v_value_3805_);
lean_ctor_set(v_reuseFailAlloc_3828_, 2, v___x_3823_);
v___x_3825_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
lean_object* v___x_3826_; 
v___x_3826_ = lean_array_uset(v_x_3802_, v___x_3822_, v___x_3825_);
v_x_3802_ = v___x_3826_;
v_x_3803_ = v_tail_3806_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(lean_object* v_i_3830_, lean_object* v_source_3831_, lean_object* v_target_3832_){
_start:
{
lean_object* v___x_3833_; uint8_t v___x_3834_; 
v___x_3833_ = lean_array_get_size(v_source_3831_);
v___x_3834_ = lean_nat_dec_lt(v_i_3830_, v___x_3833_);
if (v___x_3834_ == 0)
{
lean_dec_ref(v_source_3831_);
lean_dec(v_i_3830_);
return v_target_3832_;
}
else
{
lean_object* v_es_3835_; lean_object* v___x_3836_; lean_object* v_source_3837_; lean_object* v_target_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v_es_3835_ = lean_array_fget(v_source_3831_, v_i_3830_);
v___x_3836_ = lean_box(0);
v_source_3837_ = lean_array_fset(v_source_3831_, v_i_3830_, v___x_3836_);
v_target_3838_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(v_target_3832_, v_es_3835_);
v___x_3839_ = lean_unsigned_to_nat(1u);
v___x_3840_ = lean_nat_add(v_i_3830_, v___x_3839_);
lean_dec(v_i_3830_);
v_i_3830_ = v___x_3840_;
v_source_3831_ = v_source_3837_;
v_target_3832_ = v_target_3838_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(lean_object* v_data_3842_){
_start:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v_nbuckets_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3843_ = lean_array_get_size(v_data_3842_);
v___x_3844_ = lean_unsigned_to_nat(2u);
v_nbuckets_3845_ = lean_nat_mul(v___x_3843_, v___x_3844_);
v___x_3846_ = lean_unsigned_to_nat(0u);
v___x_3847_ = lean_box(0);
v___x_3848_ = lean_mk_array(v_nbuckets_3845_, v___x_3847_);
v___x_3849_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(v___x_3846_, v_data_3842_, v___x_3848_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object* v_m_3850_, lean_object* v_a_3851_, lean_object* v_b_3852_){
_start:
{
lean_object* v_size_3853_; lean_object* v_buckets_3854_; lean_object* v___x_3855_; uint64_t v___x_3856_; uint64_t v___x_3857_; uint64_t v___x_3858_; uint64_t v_fold_3859_; uint64_t v___x_3860_; uint64_t v___x_3861_; uint64_t v___x_3862_; size_t v___x_3863_; size_t v___x_3864_; size_t v___x_3865_; size_t v___x_3866_; size_t v___x_3867_; lean_object* v_bkt_3868_; uint8_t v___x_3869_; 
v_size_3853_ = lean_ctor_get(v_m_3850_, 0);
v_buckets_3854_ = lean_ctor_get(v_m_3850_, 1);
v___x_3855_ = lean_array_get_size(v_buckets_3854_);
v___x_3856_ = l_Lean_instHashableFVarId_hash(v_a_3851_);
v___x_3857_ = 32ULL;
v___x_3858_ = lean_uint64_shift_right(v___x_3856_, v___x_3857_);
v_fold_3859_ = lean_uint64_xor(v___x_3856_, v___x_3858_);
v___x_3860_ = 16ULL;
v___x_3861_ = lean_uint64_shift_right(v_fold_3859_, v___x_3860_);
v___x_3862_ = lean_uint64_xor(v_fold_3859_, v___x_3861_);
v___x_3863_ = lean_uint64_to_usize(v___x_3862_);
v___x_3864_ = lean_usize_of_nat(v___x_3855_);
v___x_3865_ = ((size_t)1ULL);
v___x_3866_ = lean_usize_sub(v___x_3864_, v___x_3865_);
v___x_3867_ = lean_usize_land(v___x_3863_, v___x_3866_);
v_bkt_3868_ = lean_array_uget_borrowed(v_buckets_3854_, v___x_3867_);
v___x_3869_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_3851_, v_bkt_3868_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3890_; 
lean_inc_ref(v_buckets_3854_);
lean_inc(v_size_3853_);
v_isSharedCheck_3890_ = !lean_is_exclusive(v_m_3850_);
if (v_isSharedCheck_3890_ == 0)
{
lean_object* v_unused_3891_; lean_object* v_unused_3892_; 
v_unused_3891_ = lean_ctor_get(v_m_3850_, 1);
lean_dec(v_unused_3891_);
v_unused_3892_ = lean_ctor_get(v_m_3850_, 0);
lean_dec(v_unused_3892_);
v___x_3871_ = v_m_3850_;
v_isShared_3872_ = v_isSharedCheck_3890_;
goto v_resetjp_3870_;
}
else
{
lean_dec(v_m_3850_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3890_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3873_; lean_object* v_size_x27_3874_; lean_object* v___x_3875_; lean_object* v_buckets_x27_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; uint8_t v___x_3882_; 
v___x_3873_ = lean_unsigned_to_nat(1u);
v_size_x27_3874_ = lean_nat_add(v_size_3853_, v___x_3873_);
lean_dec(v_size_3853_);
lean_inc(v_bkt_3868_);
v___x_3875_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3875_, 0, v_a_3851_);
lean_ctor_set(v___x_3875_, 1, v_b_3852_);
lean_ctor_set(v___x_3875_, 2, v_bkt_3868_);
v_buckets_x27_3876_ = lean_array_uset(v_buckets_3854_, v___x_3867_, v___x_3875_);
v___x_3877_ = lean_unsigned_to_nat(4u);
v___x_3878_ = lean_nat_mul(v_size_x27_3874_, v___x_3877_);
v___x_3879_ = lean_unsigned_to_nat(3u);
v___x_3880_ = lean_nat_div(v___x_3878_, v___x_3879_);
lean_dec(v___x_3878_);
v___x_3881_ = lean_array_get_size(v_buckets_x27_3876_);
v___x_3882_ = lean_nat_dec_le(v___x_3880_, v___x_3881_);
lean_dec(v___x_3880_);
if (v___x_3882_ == 0)
{
lean_object* v_val_3883_; lean_object* v___x_3885_; 
v_val_3883_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(v_buckets_x27_3876_);
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 1, v_val_3883_);
lean_ctor_set(v___x_3871_, 0, v_size_x27_3874_);
v___x_3885_ = v___x_3871_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_size_x27_3874_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v_val_3883_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
else
{
lean_object* v___x_3888_; 
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 1, v_buckets_x27_3876_);
lean_ctor_set(v___x_3871_, 0, v_size_x27_3874_);
v___x_3888_ = v___x_3871_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_size_x27_3874_);
lean_ctor_set(v_reuseFailAlloc_3889_, 1, v_buckets_x27_3876_);
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
lean_dec(v_b_3852_);
lean_dec(v_a_3851_);
return v_m_3850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(lean_object* v_as_3893_, size_t v_i_3894_, size_t v_stop_3895_, lean_object* v_b_3896_, lean_object* v___y_3897_){
_start:
{
uint8_t v___x_3899_; 
v___x_3899_ = lean_usize_dec_eq(v_i_3894_, v_stop_3895_);
if (v___x_3899_ == 0)
{
lean_object* v___x_3900_; lean_object* v_rewriteCache_3901_; lean_object* v_acNfCache_3902_; lean_object* v_typeAnalysis_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3917_; 
v___x_3900_ = lean_st_ref_take(v___y_3897_);
v_rewriteCache_3901_ = lean_ctor_get(v___x_3900_, 0);
v_acNfCache_3902_ = lean_ctor_get(v___x_3900_, 1);
v_typeAnalysis_3903_ = lean_ctor_get(v___x_3900_, 2);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3905_ = v___x_3900_;
v_isShared_3906_ = v_isSharedCheck_3917_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_typeAnalysis_3903_);
lean_inc(v_acNfCache_3902_);
lean_inc(v_rewriteCache_3901_);
lean_dec(v___x_3900_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3917_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3911_; 
v___x_3907_ = lean_array_uget_borrowed(v_as_3893_, v_i_3894_);
v___x_3908_ = lean_box(0);
lean_inc(v___x_3907_);
v___x_3909_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1___redArg(v_acNfCache_3902_, v___x_3907_, v___x_3908_);
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 1, v___x_3909_);
v___x_3911_ = v___x_3905_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_rewriteCache_3901_);
lean_ctor_set(v_reuseFailAlloc_3916_, 1, v___x_3909_);
lean_ctor_set(v_reuseFailAlloc_3916_, 2, v_typeAnalysis_3903_);
v___x_3911_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
lean_object* v___x_3912_; size_t v___x_3913_; size_t v___x_3914_; 
v___x_3912_ = lean_st_ref_set(v___y_3897_, v___x_3911_);
v___x_3913_ = ((size_t)1ULL);
v___x_3914_ = lean_usize_add(v_i_3894_, v___x_3913_);
v_i_3894_ = v___x_3914_;
v_b_3896_ = v___x_3908_;
goto _start;
}
}
}
else
{
lean_object* v___x_3918_; 
v___x_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3918_, 0, v_b_3896_);
return v___x_3918_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg___boxed(lean_object* v_as_3919_, lean_object* v_i_3920_, lean_object* v_stop_3921_, lean_object* v_b_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
size_t v_i_boxed_3925_; size_t v_stop_boxed_3926_; lean_object* v_res_3927_; 
v_i_boxed_3925_ = lean_unbox_usize(v_i_3920_);
lean_dec(v_i_3920_);
v_stop_boxed_3926_ = lean_unbox_usize(v_stop_3921_);
lean_dec(v_stop_3921_);
v_res_3927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(v_as_3919_, v_i_boxed_3925_, v_stop_boxed_3926_, v_b_3922_, v___y_3923_);
lean_dec(v___y_3923_);
lean_dec_ref(v_as_3919_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__0(lean_object* v___x_3928_, size_t v___x_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
lean_object* v___x_3937_; 
v___x_3937_ = l_Lean_Meta_getPropHyps(v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3956_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3940_ = v___x_3937_;
v_isShared_3941_ = v_isSharedCheck_3956_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3937_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3956_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; uint8_t v___x_3944_; 
v___x_3942_ = lean_array_get_size(v_a_3938_);
v___x_3943_ = lean_box(0);
v___x_3944_ = lean_nat_dec_lt(v___x_3928_, v___x_3942_);
if (v___x_3944_ == 0)
{
lean_object* v___x_3946_; 
lean_dec(v_a_3938_);
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 0, v___x_3943_);
v___x_3946_ = v___x_3940_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3943_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
else
{
uint8_t v___x_3948_; 
v___x_3948_ = lean_nat_dec_le(v___x_3942_, v___x_3942_);
if (v___x_3948_ == 0)
{
if (v___x_3944_ == 0)
{
lean_object* v___x_3950_; 
lean_dec(v_a_3938_);
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 0, v___x_3943_);
v___x_3950_ = v___x_3940_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v___x_3943_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
else
{
size_t v___x_3952_; lean_object* v___x_3953_; 
lean_del_object(v___x_3940_);
v___x_3952_ = lean_usize_of_nat(v___x_3942_);
v___x_3953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(v_a_3938_, v___x_3929_, v___x_3952_, v___x_3943_, v___y_3931_);
lean_dec(v_a_3938_);
return v___x_3953_;
}
}
else
{
size_t v___x_3954_; lean_object* v___x_3955_; 
lean_del_object(v___x_3940_);
v___x_3954_ = lean_usize_of_nat(v___x_3942_);
v___x_3955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(v_a_3938_, v___x_3929_, v___x_3954_, v___x_3943_, v___y_3931_);
lean_dec(v_a_3938_);
return v___x_3955_;
}
}
}
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
v_a_3957_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3937_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3937_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__0___boxed(lean_object* v___x_3965_, lean_object* v___x_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_){
_start:
{
size_t v___x_8305__boxed_3974_; lean_object* v_res_3975_; 
v___x_8305__boxed_3974_ = lean_unbox_usize(v___x_3966_);
lean_dec(v___x_3966_);
v_res_3975_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__0(v___x_3965_, v___x_8305__boxed_3974_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___x_3965_);
return v_res_3975_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object* v_m_3976_, lean_object* v_a_3977_){
_start:
{
lean_object* v_buckets_3978_; lean_object* v___x_3979_; uint64_t v___x_3980_; uint64_t v___x_3981_; uint64_t v___x_3982_; uint64_t v_fold_3983_; uint64_t v___x_3984_; uint64_t v___x_3985_; uint64_t v___x_3986_; size_t v___x_3987_; size_t v___x_3988_; size_t v___x_3989_; size_t v___x_3990_; size_t v___x_3991_; lean_object* v___x_3992_; uint8_t v___x_3993_; 
v_buckets_3978_ = lean_ctor_get(v_m_3976_, 1);
v___x_3979_ = lean_array_get_size(v_buckets_3978_);
v___x_3980_ = l_Lean_instHashableFVarId_hash(v_a_3977_);
v___x_3981_ = 32ULL;
v___x_3982_ = lean_uint64_shift_right(v___x_3980_, v___x_3981_);
v_fold_3983_ = lean_uint64_xor(v___x_3980_, v___x_3982_);
v___x_3984_ = 16ULL;
v___x_3985_ = lean_uint64_shift_right(v_fold_3983_, v___x_3984_);
v___x_3986_ = lean_uint64_xor(v_fold_3983_, v___x_3985_);
v___x_3987_ = lean_uint64_to_usize(v___x_3986_);
v___x_3988_ = lean_usize_of_nat(v___x_3979_);
v___x_3989_ = ((size_t)1ULL);
v___x_3990_ = lean_usize_sub(v___x_3988_, v___x_3989_);
v___x_3991_ = lean_usize_land(v___x_3987_, v___x_3990_);
v___x_3992_ = lean_array_uget_borrowed(v_buckets_3978_, v___x_3991_);
v___x_3993_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_3977_, v___x_3992_);
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object* v_m_3994_, lean_object* v_a_3995_){
_start:
{
uint8_t v_res_3996_; lean_object* v_r_3997_; 
v_res_3996_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg(v_m_3994_, v_a_3995_);
lean_dec(v_a_3995_);
lean_dec_ref(v_m_3994_);
v_r_3997_ = lean_box(v_res_3996_);
return v_r_3997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(lean_object* v_as_3998_, size_t v_i_3999_, size_t v_stop_4000_, lean_object* v_b_4001_, lean_object* v___y_4002_){
_start:
{
lean_object* v_a_4005_; uint8_t v___x_4009_; 
v___x_4009_ = lean_usize_dec_eq(v_i_3999_, v_stop_4000_);
if (v___x_4009_ == 0)
{
lean_object* v___x_4010_; lean_object* v_acNfCache_4011_; lean_object* v___x_4012_; uint8_t v___x_4013_; 
v___x_4010_ = lean_st_ref_get(v___y_4002_);
v_acNfCache_4011_ = lean_ctor_get(v___x_4010_, 1);
lean_inc_ref(v_acNfCache_4011_);
lean_dec(v___x_4010_);
v___x_4012_ = lean_array_uget_borrowed(v_as_3998_, v_i_3999_);
v___x_4013_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg(v_acNfCache_4011_, v___x_4012_);
lean_dec_ref(v_acNfCache_4011_);
if (v___x_4013_ == 0)
{
lean_object* v___x_4014_; 
lean_inc(v___x_4012_);
v___x_4014_ = lean_array_push(v_b_4001_, v___x_4012_);
v_a_4005_ = v___x_4014_;
goto v___jp_4004_;
}
else
{
v_a_4005_ = v_b_4001_;
goto v___jp_4004_;
}
}
else
{
lean_object* v___x_4015_; 
v___x_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4015_, 0, v_b_4001_);
return v___x_4015_;
}
v___jp_4004_:
{
size_t v___x_4006_; size_t v___x_4007_; 
v___x_4006_ = ((size_t)1ULL);
v___x_4007_ = lean_usize_add(v_i_3999_, v___x_4006_);
v_i_3999_ = v___x_4007_;
v_b_4001_ = v_a_4005_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg___boxed(lean_object* v_as_4016_, lean_object* v_i_4017_, lean_object* v_stop_4018_, lean_object* v_b_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_){
_start:
{
size_t v_i_boxed_4022_; size_t v_stop_boxed_4023_; lean_object* v_res_4024_; 
v_i_boxed_4022_ = lean_unbox_usize(v_i_4017_);
lean_dec(v_i_4017_);
v_stop_boxed_4023_ = lean_unbox_usize(v_stop_4018_);
lean_dec(v_stop_4018_);
v_res_4024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(v_as_4016_, v_i_boxed_4022_, v_stop_boxed_4023_, v_b_4019_, v___y_4020_);
lean_dec(v___y_4020_);
lean_dec_ref(v_as_4016_);
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object* v_as_4025_, size_t v_sz_4026_, size_t v_i_4027_, lean_object* v_b_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
uint8_t v___x_4035_; 
v___x_4035_ = lean_usize_dec_lt(v_i_4027_, v_sz_4026_);
if (v___x_4035_ == 0)
{
lean_object* v___x_4036_; 
v___x_4036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4036_, 0, v_b_4028_);
return v___x_4036_;
}
else
{
lean_object* v_maxSteps_4037_; lean_object* v_a_4038_; lean_object* v___x_4039_; 
v_maxSteps_4037_ = lean_ctor_get(v___y_4029_, 1);
v_a_4038_ = lean_array_uget_borrowed(v_as_4025_, v_i_4027_);
lean_inc(v_maxSteps_4037_);
lean_inc(v_a_4038_);
lean_inc(v_b_4028_);
v___x_4039_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta(v_b_4028_, v_a_4038_, v_maxSteps_4037_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_a_4040_; lean_object* v_a_4042_; 
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc(v_a_4040_);
lean_dec_ref(v___x_4039_);
if (lean_obj_tag(v_a_4040_) == 1)
{
lean_object* v_val_4046_; 
lean_dec(v_b_4028_);
v_val_4046_ = lean_ctor_get(v_a_4040_, 0);
lean_inc(v_val_4046_);
lean_dec_ref(v_a_4040_);
v_a_4042_ = v_val_4046_;
goto v___jp_4041_;
}
else
{
lean_dec(v_a_4040_);
v_a_4042_ = v_b_4028_;
goto v___jp_4041_;
}
v___jp_4041_:
{
size_t v___x_4043_; size_t v___x_4044_; 
v___x_4043_ = ((size_t)1ULL);
v___x_4044_ = lean_usize_add(v_i_4027_, v___x_4043_);
v_i_4027_ = v___x_4044_;
v_b_4028_ = v_a_4042_;
goto _start;
}
}
else
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
lean_dec(v_b_4028_);
v_a_4047_ = lean_ctor_get(v___x_4039_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4049_ = v___x_4039_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4039_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object* v_as_4055_, lean_object* v_sz_4056_, lean_object* v_i_4057_, lean_object* v_b_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
size_t v_sz_boxed_4065_; size_t v_i_boxed_4066_; lean_object* v_res_4067_; 
v_sz_boxed_4065_ = lean_unbox_usize(v_sz_4056_);
lean_dec(v_sz_4056_);
v_i_boxed_4066_ = lean_unbox_usize(v_i_4057_);
lean_dec(v_i_4057_);
v_res_4067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg(v_as_4055_, v_sz_boxed_4065_, v_i_boxed_4066_, v_b_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec_ref(v___y_4059_);
lean_dec_ref(v_as_4055_);
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1(lean_object* v_goal_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Lean_Meta_getPropHyps(v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v_a_4084_; lean_object* v___x_4085_; lean_object* v_a_4087_; lean_object* v___y_4120_; lean_object* v___x_4130_; lean_object* v___x_4131_; uint8_t v___x_4132_; 
v_a_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc(v_a_4084_);
lean_dec_ref(v___x_4083_);
v___x_4085_ = lean_unsigned_to_nat(0u);
v___x_4130_ = lean_array_get_size(v_a_4084_);
v___x_4131_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__1));
v___x_4132_ = lean_nat_dec_lt(v___x_4085_, v___x_4130_);
if (v___x_4132_ == 0)
{
lean_dec(v_a_4084_);
v_a_4087_ = v___x_4131_;
goto v___jp_4086_;
}
else
{
uint8_t v___x_4133_; 
v___x_4133_ = lean_nat_dec_le(v___x_4130_, v___x_4130_);
if (v___x_4133_ == 0)
{
if (v___x_4132_ == 0)
{
lean_dec(v_a_4084_);
v_a_4087_ = v___x_4131_;
goto v___jp_4086_;
}
else
{
size_t v___x_4134_; size_t v___x_4135_; lean_object* v___x_4136_; 
v___x_4134_ = ((size_t)0ULL);
v___x_4135_ = lean_usize_of_nat(v___x_4130_);
v___x_4136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(v_a_4084_, v___x_4134_, v___x_4135_, v___x_4131_, v___y_4077_);
lean_dec(v_a_4084_);
v___y_4120_ = v___x_4136_;
goto v___jp_4119_;
}
}
else
{
size_t v___x_4137_; size_t v___x_4138_; lean_object* v___x_4139_; 
v___x_4137_ = ((size_t)0ULL);
v___x_4138_ = lean_usize_of_nat(v___x_4130_);
v___x_4139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(v_a_4084_, v___x_4137_, v___x_4138_, v___x_4131_, v___y_4077_);
lean_dec(v_a_4084_);
v___y_4120_ = v___x_4139_;
goto v___jp_4119_;
}
}
v___jp_4086_:
{
size_t v_sz_4088_; size_t v___x_4089_; lean_object* v___x_4090_; 
v_sz_4088_ = lean_array_size(v_a_4087_);
v___x_4089_ = ((size_t)0ULL);
v___x_4090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg(v_a_4087_, v_sz_4088_, v___x_4089_, v_goal_4075_, v___y_4076_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
lean_dec_ref(v_a_4087_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v_a_4091_; lean_object* v___f_4092_; lean_object* v___x_4093_; 
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
lean_inc_n(v_a_4091_, 2);
lean_dec_ref(v___x_4090_);
v___f_4092_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__0));
v___x_4093_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(v_a_4091_, v___f_4092_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
if (lean_obj_tag(v___x_4093_) == 0)
{
lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4101_; 
v_isSharedCheck_4101_ = !lean_is_exclusive(v___x_4093_);
if (v_isSharedCheck_4101_ == 0)
{
lean_object* v_unused_4102_; 
v_unused_4102_ = lean_ctor_get(v___x_4093_, 0);
lean_dec(v_unused_4102_);
v___x_4095_ = v___x_4093_;
v_isShared_4096_ = v_isSharedCheck_4101_;
goto v_resetjp_4094_;
}
else
{
lean_dec(v___x_4093_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4101_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4097_; lean_object* v___x_4099_; 
v___x_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4097_, 0, v_a_4091_);
if (v_isShared_4096_ == 0)
{
lean_ctor_set(v___x_4095_, 0, v___x_4097_);
v___x_4099_ = v___x_4095_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v___x_4097_);
v___x_4099_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
return v___x_4099_;
}
}
}
else
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4110_; 
lean_dec(v_a_4091_);
v_a_4103_ = lean_ctor_get(v___x_4093_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4093_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4105_ = v___x_4093_;
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4093_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
}
else
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
v_a_4111_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4090_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4090_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
v___jp_4119_:
{
if (lean_obj_tag(v___y_4120_) == 0)
{
lean_object* v_a_4121_; 
v_a_4121_ = lean_ctor_get(v___y_4120_, 0);
lean_inc(v_a_4121_);
lean_dec_ref(v___y_4120_);
v_a_4087_ = v_a_4121_;
goto v___jp_4086_;
}
else
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4129_; 
lean_dec(v_goal_4075_);
v_a_4122_ = lean_ctor_get(v___y_4120_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___y_4120_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4124_ = v___y_4120_;
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___y_4120_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4127_; 
if (v_isShared_4125_ == 0)
{
v___x_4127_ = v___x_4124_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4122_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
}
}
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
lean_dec(v_goal_4075_);
v_a_4140_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4083_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4083_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___boxed(lean_object* v_goal_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
lean_object* v_res_4156_; 
v_res_4156_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1(v_goal_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
return v_res_4156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__2(lean_object* v_goal_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v___f_4165_; lean_object* v___x_4166_; 
lean_inc(v_goal_4157_);
v___f_4165_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___boxed), 8, 1);
lean_closure_set(v___f_4165_, 0, v_goal_4157_);
v___x_4166_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(v_goal_4157_, v___f_4165_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
return v___x_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__2___boxed(lean_object* v_goal_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__2(v_goal_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec(v___y_4171_);
lean_dec_ref(v___y_4170_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
return v_res_4175_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0(lean_object* v_00_u03b2_4184_, lean_object* v_m_4185_, lean_object* v_a_4186_){
_start:
{
uint8_t v___x_4187_; 
v___x_4187_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg(v_m_4185_, v_a_4186_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___boxed(lean_object* v_00_u03b2_4188_, lean_object* v_m_4189_, lean_object* v_a_4190_){
_start:
{
uint8_t v_res_4191_; lean_object* v_r_4192_; 
v_res_4191_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0(v_00_u03b2_4188_, v_m_4189_, v_a_4190_);
lean_dec(v_a_4190_);
lean_dec_ref(v_m_4189_);
v_r_4192_ = lean_box(v_res_4191_);
return v_r_4192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1(lean_object* v_00_u03b2_4193_, lean_object* v_m_4194_, lean_object* v_a_4195_, lean_object* v_b_4196_){
_start:
{
lean_object* v___x_4197_; 
v___x_4197_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1___redArg(v_m_4194_, v_a_4195_, v_b_4196_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2(lean_object* v_as_4198_, size_t v_sz_4199_, size_t v_i_4200_, lean_object* v_b_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
lean_object* v___x_4209_; 
v___x_4209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg(v_as_4198_, v_sz_4199_, v_i_4200_, v_b_4201_, v___y_4202_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_);
return v___x_4209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object* v_as_4210_, lean_object* v_sz_4211_, lean_object* v_i_4212_, lean_object* v_b_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
size_t v_sz_boxed_4221_; size_t v_i_boxed_4222_; lean_object* v_res_4223_; 
v_sz_boxed_4221_ = lean_unbox_usize(v_sz_4211_);
lean_dec(v_sz_4211_);
v_i_boxed_4222_ = lean_unbox_usize(v_i_4212_);
lean_dec(v_i_4212_);
v_res_4223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2(v_as_4210_, v_sz_boxed_4221_, v_i_boxed_4222_, v_b_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec_ref(v_as_4210_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3(lean_object* v_as_4224_, size_t v_i_4225_, size_t v_stop_4226_, lean_object* v_b_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v___x_4235_; 
v___x_4235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(v_as_4224_, v_i_4225_, v_stop_4226_, v_b_4227_, v___y_4229_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___boxed(lean_object* v_as_4236_, lean_object* v_i_4237_, lean_object* v_stop_4238_, lean_object* v_b_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
size_t v_i_boxed_4247_; size_t v_stop_boxed_4248_; lean_object* v_res_4249_; 
v_i_boxed_4247_ = lean_unbox_usize(v_i_4237_);
lean_dec(v_i_4237_);
v_stop_boxed_4248_ = lean_unbox_usize(v_stop_4238_);
lean_dec(v_stop_4238_);
v_res_4249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3(v_as_4236_, v_i_boxed_4247_, v_stop_boxed_4248_, v_b_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec_ref(v_as_4236_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5(lean_object* v_as_4250_, size_t v_i_4251_, size_t v_stop_4252_, lean_object* v_b_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v___x_4261_; 
v___x_4261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(v_as_4250_, v_i_4251_, v_stop_4252_, v_b_4253_, v___y_4255_);
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___boxed(lean_object* v_as_4262_, lean_object* v_i_4263_, lean_object* v_stop_4264_, lean_object* v_b_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_){
_start:
{
size_t v_i_boxed_4273_; size_t v_stop_boxed_4274_; lean_object* v_res_4275_; 
v_i_boxed_4273_ = lean_unbox_usize(v_i_4263_);
lean_dec(v_i_4263_);
v_stop_boxed_4274_ = lean_unbox_usize(v_stop_4264_);
lean_dec(v_stop_4264_);
v_res_4275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5(v_as_4262_, v_i_boxed_4273_, v_stop_boxed_4274_, v_b_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_);
lean_dec(v___y_4271_);
lean_dec_ref(v___y_4270_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec_ref(v_as_4262_);
return v_res_4275_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0(lean_object* v_00_u03b2_4276_, lean_object* v_a_4277_, lean_object* v_x_4278_){
_start:
{
uint8_t v___x_4279_; 
v___x_4279_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_4277_, v_x_4278_);
return v___x_4279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4280_, lean_object* v_a_4281_, lean_object* v_x_4282_){
_start:
{
uint8_t v_res_4283_; lean_object* v_r_4284_; 
v_res_4283_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0(v_00_u03b2_4280_, v_a_4281_, v_x_4282_);
lean_dec(v_x_4282_);
lean_dec(v_a_4281_);
v_r_4284_ = lean_box(v_res_4283_);
return v_r_4284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2(lean_object* v_00_u03b2_4285_, lean_object* v_data_4286_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(v_data_4286_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4288_, lean_object* v_i_4289_, lean_object* v_source_4290_, lean_object* v_target_4291_){
_start:
{
lean_object* v___x_4292_; 
v___x_4292_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(v_i_4289_, v_source_4290_, v_target_4291_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4293_, lean_object* v_x_4294_, lean_object* v_x_4295_){
_start:
{
lean_object* v___x_4296_; 
v___x_4296_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(v_x_4294_, v_x_4295_);
return v___x_4296_;
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
