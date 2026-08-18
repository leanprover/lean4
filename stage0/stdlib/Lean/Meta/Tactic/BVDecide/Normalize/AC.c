// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.AC
// Imports: import Lean.Meta.Tactic.AC.Main public import Lean.Meta.Tactic.BVDecide.Normalize.Basic
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_AC_rewriteUnnormalizedRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_merge___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
extern lean_object* l_Lean_checkEmoji;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instReprExpr_repr(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType(lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instMul"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 82, 7, 193, 128, 145, 145, 228)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul(lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul(lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean.Meta.Tactic.BVDecide.Normalize.Op.mul"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_instToMessageData___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_Op_instToMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_Op_instToMessageData___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_instToMessageData___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_instToMessageData___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_instToMessageData = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_instToMessageData___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "internal error (this is a bug!): index "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = " out of range, the current state only has "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " variables:\n\n"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Found binary operation '"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "', expected '"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "'.Treating as atom."};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "canonicalizeWithSharing"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Operations mismatch:\n      the left-hand-side has operation "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\n        "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "\n      but the right-hand-side has operation "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Canonicalizing with respect to operation: '"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "'."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Failed to recognize operation: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___boxed(lean_object**);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Canonicalizing: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_ac_nf "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " found `BEq.beq`."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " found `Eq`."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "  ==>  "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bv_ac_nf"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(186, 2, 240, 42, 244, 93, 182, 215)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___boxed(lean_object**);
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType(lean_object* v_w_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__2);
v___x_9_ = l_Lean_Expr_app___override(v___x_8_, v_w_7_);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = lean_box(0);
v___x_15_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__1));
v___x_16_ = l_Lean_Expr_const___override(v___x_15_, v___x_14_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul(lean_object* v_w_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__2);
v___x_19_ = l_Lean_Expr_app___override(v___x_18_, v_w_17_);
return v___x_19_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__3(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_26_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__2));
v___x_27_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__1));
v___x_28_ = l_Lean_mkConst(v___x_27_, v___x_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul(lean_object* v_w_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_30_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__3);
lean_inc_ref(v_w_29_);
v___x_31_ = l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType(v_w_29_);
v___x_32_ = l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul(v_w_29_);
v___x_33_ = l_Lean_mkAppB(v___x_30_, v___x_31_, v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__2(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_box(0);
v___x_39_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__1));
v___x_40_ = l_Lean_mkConst(v___x_39_, v___x_38_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit(lean_object* v_w_41_, lean_object* v_n_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__2);
v___x_44_ = l_Lean_mkNatLit(v_n_42_);
v___x_45_ = l_Lean_mkAppB(v___x_43_, v_w_41_, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp_beq(lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
uint8_t v___x_48_; 
v___x_48_ = lean_expr_eqv(v_x_46_, v_x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp_beq___boxed(lean_object* v_x_49_, lean_object* v_x_50_){
_start:
{
uint8_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp_beq(v_x_49_, v_x_50_);
lean_dec_ref(v_x_50_);
lean_dec_ref(v_x_49_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__3(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(2u);
v___x_62_ = lean_nat_to_int(v___x_61_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__4(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_unsigned_to_nat(1u);
v___x_64_ = lean_nat_to_int(v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr(lean_object* v_x_65_, lean_object* v_prec_66_){
_start:
{
lean_object* v___y_68_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(1024u);
v___x_78_ = lean_nat_dec_le(v___x_77_, v_prec_66_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
v___x_79_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__3);
v___y_68_ = v___x_79_;
goto v___jp_67_;
}
else
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__4);
v___y_68_ = v___x_80_;
goto v___jp_67_;
}
v___jp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_69_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__2));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___boxed(lean_object* v_x_81_, lean_object* v_prec_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr(v_x_81_, v_prec_82_);
lean_dec(v_prec_82_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f(lean_object* v_e_91_){
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
v___x_106_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__2));
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
v___x_114_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(lean_object* v_x_118_){
_start:
{
if (lean_obj_tag(v_x_118_) == 5)
{
lean_object* v_fn_119_; 
v_fn_119_ = lean_ctor_get(v_x_118_, 0);
lean_inc_ref(v_fn_119_);
lean_dec_ref_known(v_x_118_, 2);
if (lean_obj_tag(v_fn_119_) == 5)
{
lean_object* v_fn_120_; lean_object* v___x_121_; 
v_fn_120_ = lean_ctor_get(v_fn_119_, 0);
lean_inc_ref(v_fn_120_);
lean_dec_ref_known(v_fn_119_, 2);
v___x_121_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f(v_fn_120_);
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
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = l_Lean_Level_ofNat(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__1(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = lean_box(0);
v___x_127_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0);
v___x_128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__2(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__1);
v___x_130_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0);
v___x_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___x_129_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__3(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__2);
v___x_133_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0);
v___x_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_132_);
return v___x_134_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__4(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__3);
v___x_136_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__2));
v___x_137_ = l_Lean_mkConst(v___x_136_, v___x_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(lean_object* v_x_138_){
_start:
{
lean_object* v_bv_139_; lean_object* v_inst_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
lean_inc_ref(v_x_138_);
v_bv_139_ = l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType(v_x_138_);
v_inst_140_ = l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul(v_x_138_);
v___x_141_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__4);
lean_inc_ref_n(v_bv_139_, 2);
v___x_142_ = l_Lean_mkApp4(v___x_141_, v_bv_139_, v_bv_139_, v_bv_139_, v_inst_140_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(lean_object* v_x_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit(v_x_143_, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(lean_object* v_op_x27_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f(v_op_x27_146_);
if (lean_obj_tag(v___x_147_) == 1)
{
uint8_t v___x_148_; 
lean_dec_ref_known(v___x_147_, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg___boxed(lean_object* v_op_x27_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(v_op_x27_150_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind(lean_object* v_op_153_, lean_object* v_op_x27_154_){
_start:
{
uint8_t v___x_155_; 
v___x_155_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(v_op_x27_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___boxed(lean_object* v_op_156_, lean_object* v_op_x27_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind(v_op_156_, v_op_x27_157_);
lean_dec_ref(v_op_156_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_instToMessageData___lam__0(lean_object* v_op_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_160_);
v___x_162_ = l_Lean_MessageData_ofExpr(v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(lean_object* v_x_165_, lean_object* v_s_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v___x_174_; 
lean_inc(v_a_172_);
lean_inc_ref(v_a_171_);
lean_inc(v_a_170_);
lean_inc_ref(v_a_169_);
lean_inc(v_a_168_);
lean_inc_ref(v_a_167_);
v___x_174_ = lean_apply_8(v_x_165_, v_s_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, lean_box(0));
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_183_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_183_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v_fst_179_; lean_object* v___x_181_; 
v_fst_179_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_179_);
lean_dec(v_a_175_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v_fst_179_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_fst_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
else
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
v_a_184_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_174_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_174_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg___boxed(lean_object* v_x_192_, lean_object* v_s_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v_x_192_, v_s_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27(lean_object* v_00_u03b1_202_, lean_object* v_x_203_, lean_object* v_s_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v_x_203_, v_s_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___boxed(lean_object* v_00_u03b1_213_, lean_object* v_x_214_, lean_object* v_s_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27(v_00_u03b1_213_, v_x_214_, v_s_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(lean_object* v_m_224_, lean_object* v_query_225_, lean_object* v_x_226_, lean_object* v_x_227_, lean_object* v_x_228_){
_start:
{
lean_object* v_zero_229_; uint8_t v_isZero_230_; 
v_zero_229_ = lean_unsigned_to_nat(0u);
v_isZero_230_ = lean_nat_dec_eq(v_x_227_, v_zero_229_);
if (v_isZero_230_ == 1)
{
lean_dec(v_x_228_);
lean_dec(v_x_227_);
if (lean_obj_tag(v_x_226_) == 0)
{
lean_object* v___x_231_; 
v___x_231_ = lean_box(2);
return v___x_231_;
}
else
{
lean_object* v_val_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
v_val_232_ = lean_ctor_get(v_x_226_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v_x_226_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_val_232_);
lean_dec(v_x_226_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_val_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
else
{
lean_object* v_keyArray_240_; lean_object* v_valueArray_241_; lean_object* v___x_242_; uint8_t v_isSome_243_; 
v_keyArray_240_ = lean_ctor_get(v_m_224_, 1);
v_valueArray_241_ = lean_ctor_get(v_m_224_, 2);
v___x_242_ = lean_array_fget_borrowed(v_keyArray_240_, v_x_228_);
v_isSome_243_ = lean_noption_is_some(v___x_242_);
if (v_isSome_243_ == 0)
{
lean_dec(v_x_227_);
if (lean_obj_tag(v_x_226_) == 0)
{
lean_object* v___x_244_; 
v___x_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_244_, 0, v_x_228_);
return v___x_244_;
}
else
{
lean_object* v_val_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
lean_dec(v_x_228_);
v_val_245_ = lean_ctor_get(v_x_226_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v_x_226_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_val_245_);
lean_dec(v_x_226_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_val_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
else
{
lean_object* v_one_253_; lean_object* v_n_254_; lean_object* v___y_256_; 
v_one_253_ = lean_unsigned_to_nat(1u);
v_n_254_ = lean_nat_sub(v_x_227_, v_one_253_);
lean_dec(v_x_227_);
if (v_isSome_243_ == 0)
{
goto v___jp_262_;
}
else
{
lean_object* v___x_264_; uint8_t v_isSome_265_; 
v___x_264_ = lean_array_fget_borrowed(v_valueArray_241_, v_x_228_);
v_isSome_265_ = lean_noption_is_some(v___x_264_);
if (v_isSome_265_ == 0)
{
goto v___jp_262_;
}
else
{
lean_object* v_val_266_; uint8_t v___x_267_; 
lean_inc(v___x_242_);
v_val_266_ = lean_noption_get(v___x_242_);
v___x_267_ = lean_expr_eqv(v_val_266_, v_query_225_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
lean_dec(v_val_266_);
v___x_268_ = lean_array_get_size(v_keyArray_240_);
v___x_269_ = lean_nat_add(v_x_228_, v_one_253_);
lean_dec(v_x_228_);
v___x_270_ = lean_nat_dec_lt(v___x_269_, v___x_268_);
if (v___x_270_ == 0)
{
lean_dec(v___x_269_);
v_x_227_ = v_n_254_;
v_x_228_ = v_zero_229_;
goto _start;
}
else
{
v_x_227_ = v_n_254_;
v_x_228_ = v___x_269_;
goto _start;
}
}
else
{
lean_object* v_val_273_; lean_object* v___x_274_; 
lean_dec(v_n_254_);
lean_dec(v_x_226_);
lean_inc(v___x_264_);
v_val_273_ = lean_noption_get(v___x_264_);
v___x_274_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_274_, 0, v_x_228_);
lean_ctor_set(v___x_274_, 1, v_val_266_);
lean_ctor_set(v___x_274_, 2, v_val_273_);
return v___x_274_;
}
}
}
v___jp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_257_ = lean_array_get_size(v_keyArray_240_);
v___x_258_ = lean_nat_add(v_x_228_, v_one_253_);
lean_dec(v_x_228_);
v___x_259_ = lean_nat_dec_lt(v___x_258_, v___x_257_);
if (v___x_259_ == 0)
{
lean_dec(v___x_258_);
v_x_226_ = v___y_256_;
v_x_227_ = v_n_254_;
v_x_228_ = v_zero_229_;
goto _start;
}
else
{
v_x_226_ = v___y_256_;
v_x_227_ = v_n_254_;
v_x_228_ = v___x_258_;
goto _start;
}
}
v___jp_262_:
{
if (lean_obj_tag(v_x_226_) == 0)
{
lean_object* v___x_263_; 
lean_inc(v_x_228_);
v___x_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_263_, 0, v_x_228_);
v___y_256_ = v___x_263_;
goto v___jp_255_;
}
else
{
v___y_256_ = v_x_226_;
goto v___jp_255_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg___boxed(lean_object* v_m_275_, lean_object* v_query_276_, lean_object* v_x_277_, lean_object* v_x_278_, lean_object* v_x_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_m_275_, v_query_276_, v_x_277_, v_x_278_, v_x_279_);
lean_dec_ref(v_query_276_);
lean_dec_ref(v_m_275_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(lean_object* v_m_281_, lean_object* v_query_282_){
_start:
{
lean_object* v_keyArray_283_; lean_object* v___x_284_; uint64_t v___x_285_; uint64_t v___x_286_; uint64_t v___x_287_; uint64_t v_fold_288_; uint64_t v___x_289_; uint64_t v___x_290_; uint64_t v___x_291_; size_t v___x_292_; size_t v___x_293_; size_t v___x_294_; size_t v___x_295_; size_t v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_keyArray_283_ = lean_ctor_get(v_m_281_, 1);
v___x_284_ = lean_array_get_size(v_keyArray_283_);
v___x_285_ = l_Lean_Expr_hash(v_query_282_);
v___x_286_ = 32ULL;
v___x_287_ = lean_uint64_shift_right(v___x_285_, v___x_286_);
v_fold_288_ = lean_uint64_xor(v___x_285_, v___x_287_);
v___x_289_ = 16ULL;
v___x_290_ = lean_uint64_shift_right(v_fold_288_, v___x_289_);
v___x_291_ = lean_uint64_xor(v_fold_288_, v___x_290_);
v___x_292_ = lean_uint64_to_usize(v___x_291_);
v___x_293_ = lean_usize_of_nat(v___x_284_);
v___x_294_ = ((size_t)1ULL);
v___x_295_ = lean_usize_sub(v___x_293_, v___x_294_);
v___x_296_ = lean_usize_land(v___x_292_, v___x_295_);
v___x_297_ = lean_usize_to_nat(v___x_296_);
v___x_298_ = lean_box(0);
v___x_299_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_m_281_, v_query_282_, v___x_298_, v___x_284_, v___x_297_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg___boxed(lean_object* v_m_300_, lean_object* v_query_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(v_m_300_, v_query_301_);
lean_dec_ref(v_query_301_);
lean_dec_ref(v_m_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4_spec__5___redArg(lean_object* v_b_303_, lean_object* v_acc_304_, lean_object* v_i_305_){
_start:
{
lean_object* v___y_307_; lean_object* v_keyArray_315_; lean_object* v_valueArray_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v_keyArray_315_ = lean_ctor_get(v_b_303_, 1);
v_valueArray_316_ = lean_ctor_get(v_b_303_, 2);
v___x_317_ = lean_array_get_size(v_keyArray_315_);
v___x_318_ = lean_nat_dec_lt(v_i_305_, v___x_317_);
if (v___x_318_ == 0)
{
lean_dec(v_i_305_);
return v_acc_304_;
}
else
{
lean_object* v___x_319_; uint8_t v_isSome_320_; 
v___x_319_ = lean_array_fget_borrowed(v_keyArray_315_, v_i_305_);
v_isSome_320_ = lean_noption_is_some(v___x_319_);
if (v_isSome_320_ == 0)
{
goto v___jp_311_;
}
else
{
lean_object* v___x_321_; uint8_t v_isSome_322_; 
v___x_321_ = lean_array_fget_borrowed(v_valueArray_316_, v_i_305_);
v_isSome_322_ = lean_noption_is_some(v___x_321_);
if (v_isSome_322_ == 0)
{
goto v___jp_311_;
}
else
{
lean_object* v_val_323_; lean_object* v_val_324_; lean_object* v_i_326_; lean_object* v___x_331_; 
lean_inc(v___x_319_);
v_val_323_ = lean_noption_get(v___x_319_);
lean_inc(v___x_321_);
v_val_324_ = lean_noption_get(v___x_321_);
v___x_331_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(v_acc_304_, v_val_323_);
switch(lean_obj_tag(v___x_331_))
{
case 0:
{
lean_object* v_index_332_; lean_object* v_size_333_; lean_object* v___x_334_; 
v_index_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_index_332_);
lean_dec_ref_known(v___x_331_, 3);
v_size_333_ = lean_ctor_get(v_acc_304_, 0);
lean_inc(v_size_333_);
v___x_334_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_304_, v_size_333_, v_index_332_, v_val_323_, v_val_324_);
lean_dec(v_index_332_);
v___y_307_ = v___x_334_;
goto v___jp_306_;
}
case 1:
{
lean_object* v_index_335_; 
v_index_335_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_index_335_);
lean_dec_ref_known(v___x_331_, 1);
v_i_326_ = v_index_335_;
goto v___jp_325_;
}
default: 
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_304_, v___x_336_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_index_338_; 
v_index_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_index_338_);
lean_dec_ref_known(v___x_337_, 1);
v_i_326_ = v_index_338_;
goto v___jp_325_;
}
else
{
lean_dec(v_val_324_);
lean_dec(v_val_323_);
v___y_307_ = v_acc_304_;
goto v___jp_306_;
}
}
}
v___jp_325_:
{
lean_object* v_size_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_size_327_ = lean_ctor_get(v_acc_304_, 0);
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = lean_nat_add(v_size_327_, v___x_328_);
v___x_330_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_304_, v___x_329_, v_i_326_, v_val_323_, v_val_324_);
lean_dec(v_i_326_);
v___y_307_ = v___x_330_;
goto v___jp_306_;
}
}
}
}
v___jp_306_:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = lean_nat_add(v_i_305_, v___x_308_);
lean_dec(v_i_305_);
v_acc_304_ = v___y_307_;
v_i_305_ = v___x_309_;
goto _start;
}
v___jp_311_:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = lean_nat_add(v_i_305_, v___x_312_);
lean_dec(v_i_305_);
v_i_305_ = v___x_313_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_b_339_, lean_object* v_acc_340_, lean_object* v_i_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4_spec__5___redArg(v_b_339_, v_acc_340_, v_i_341_);
lean_dec_ref(v_b_339_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4___redArg(lean_object* v_init_343_, lean_object* v_b_344_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4_spec__5___redArg(v_b_344_, v_init_343_, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4___redArg___boxed(lean_object* v_init_347_, lean_object* v_b_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4___redArg(v_init_347_, v_b_348_);
lean_dec_ref(v_b_348_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2___redArg(lean_object* v_m_350_){
_start:
{
lean_object* v_keyArray_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v_cellCount_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v_target_358_; lean_object* v___x_359_; 
v_keyArray_351_ = lean_ctor_get(v_m_350_, 1);
v___x_352_ = lean_array_get_size(v_keyArray_351_);
v___x_353_ = lean_unsigned_to_nat(2u);
v_cellCount_354_ = lean_nat_mul(v___x_352_, v___x_353_);
v___x_355_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_354_);
v___x_356_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_354_);
v___x_357_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_354_);
v_target_358_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_358_, 0, v___x_355_);
lean_ctor_set(v_target_358_, 1, v___x_356_);
lean_ctor_set(v_target_358_, 2, v___x_357_);
v___x_359_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4___redArg(v_target_358_, v_m_350_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2___redArg___boxed(lean_object* v_m_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2___redArg(v_m_360_);
lean_dec_ref(v_m_360_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(lean_object* v_m_362_, lean_object* v_query_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(v_m_362_, v_query_363_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_index_365_; lean_object* v_key_366_; lean_object* v_value_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
v_index_365_ = lean_ctor_get(v___x_364_, 0);
v_key_366_ = lean_ctor_get(v___x_364_, 1);
v_value_367_ = lean_ctor_get(v___x_364_, 2);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_364_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_value_367_);
lean_inc(v_key_366_);
lean_inc(v_index_365_);
lean_dec(v___x_364_);
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
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_index_365_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_key_366_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_value_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
else
{
lean_object* v___x_375_; 
lean_dec(v___x_364_);
v___x_375_ = lean_box(1);
return v___x_375_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg___boxed(lean_object* v_m_376_, lean_object* v_query_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_m_376_, v_query_377_);
lean_dec_ref(v_query_377_);
lean_dec_ref(v_m_376_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(lean_object* v_m_379_, lean_object* v_a_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_m_379_, v_a_380_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_value_382_; lean_object* v___x_383_; 
v_value_382_ = lean_ctor_get(v___x_381_, 2);
lean_inc(v_value_382_);
lean_dec_ref_known(v___x_381_, 3);
v___x_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_383_, 0, v_value_382_);
return v___x_383_;
}
else
{
lean_object* v___x_384_; 
v___x_384_ = lean_box(0);
return v___x_384_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg___boxed(lean_object* v_m_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_m_385_, v_a_386_);
lean_dec_ref(v_a_386_);
lean_dec_ref(v_m_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(lean_object* v_e_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_op_391_; lean_object* v_exprToVarIndex_392_; lean_object* v_varToExpr_393_; lean_object* v___x_394_; 
v_op_391_ = lean_ctor_get(v_a_389_, 0);
v_exprToVarIndex_392_ = lean_ctor_get(v_a_389_, 1);
v_varToExpr_393_ = lean_ctor_get(v_a_389_, 2);
v___x_394_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_exprToVarIndex_392_, v_e_388_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_467_; 
lean_inc_ref(v_varToExpr_393_);
lean_inc_ref(v_exprToVarIndex_392_);
lean_inc_ref(v_op_391_);
v_isSharedCheck_467_ = !lean_is_exclusive(v_a_389_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; lean_object* v_unused_469_; lean_object* v_unused_470_; 
v_unused_468_ = lean_ctor_get(v_a_389_, 2);
lean_dec(v_unused_468_);
v_unused_469_ = lean_ctor_get(v_a_389_, 1);
lean_dec(v_unused_469_);
v_unused_470_ = lean_ctor_get(v_a_389_, 0);
lean_dec(v_unused_470_);
v___x_396_ = v_a_389_;
v_isShared_397_ = v_isSharedCheck_467_;
goto v_resetjp_395_;
}
else
{
lean_dec(v_a_389_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_467_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v_size_398_; lean_object* v_keyArray_399_; lean_object* v___y_401_; lean_object* v___y_409_; lean_object* v_i_410_; lean_object* v___y_416_; lean_object* v___y_426_; lean_object* v_i_427_; lean_object* v___x_442_; 
v_size_398_ = lean_ctor_get(v_exprToVarIndex_392_, 0);
lean_inc(v_size_398_);
v_keyArray_399_ = lean_ctor_get(v_exprToVarIndex_392_, 1);
v___x_442_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(v_exprToVarIndex_392_, v_e_388_);
switch(lean_obj_tag(v___x_442_))
{
case 0:
{
lean_object* v_index_443_; lean_object* v___x_444_; 
v_index_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_index_443_);
lean_dec_ref_known(v___x_442_, 3);
lean_inc_ref(v_e_388_);
lean_inc_n(v_size_398_, 2);
v___x_444_ = l_Std_DHashMap_Raw_setEntry___redArg(v_exprToVarIndex_392_, v_size_398_, v_index_443_, v_e_388_, v_size_398_);
lean_dec(v_index_443_);
v___y_401_ = v___x_444_;
goto v___jp_400_;
}
case 1:
{
lean_object* v_index_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v_index_445_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_index_445_);
lean_dec_ref_known(v___x_442_, 1);
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = lean_nat_add(v_size_398_, v___x_446_);
v___x_448_ = lean_array_get_size(v_keyArray_399_);
v___x_449_ = lean_nat_dec_lt(v___x_447_, v___x_448_);
if (v___x_449_ == 0)
{
lean_dec(v___x_447_);
lean_dec(v_index_445_);
goto v___jp_432_;
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_450_ = lean_unsigned_to_nat(4u);
v___x_451_ = lean_nat_mul(v___x_447_, v___x_450_);
v___x_452_ = lean_unsigned_to_nat(3u);
v___x_453_ = lean_nat_mul(v___x_448_, v___x_452_);
v___x_454_ = lean_nat_dec_le(v___x_451_, v___x_453_);
lean_dec(v___x_453_);
lean_dec(v___x_451_);
if (v___x_454_ == 0)
{
lean_dec(v___x_447_);
lean_dec(v_index_445_);
goto v___jp_432_;
}
else
{
lean_object* v___x_455_; 
lean_inc(v_size_398_);
lean_inc_ref(v_e_388_);
v___x_455_ = l_Std_DHashMap_Raw_setEntry___redArg(v_exprToVarIndex_392_, v___x_447_, v_index_445_, v_e_388_, v_size_398_);
lean_dec(v_index_445_);
v___y_401_ = v___x_455_;
goto v___jp_400_;
}
}
}
default: 
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = lean_nat_add(v_size_398_, v___x_456_);
v___x_458_ = lean_array_get_size(v_keyArray_399_);
v___x_459_ = lean_nat_dec_lt(v___x_457_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
lean_dec(v___x_457_);
v___x_460_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2___redArg(v_exprToVarIndex_392_);
lean_dec_ref(v_exprToVarIndex_392_);
v___y_416_ = v___x_460_;
goto v___jp_415_;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_461_ = lean_unsigned_to_nat(4u);
v___x_462_ = lean_nat_mul(v___x_457_, v___x_461_);
lean_dec(v___x_457_);
v___x_463_ = lean_unsigned_to_nat(3u);
v___x_464_ = lean_nat_mul(v___x_458_, v___x_463_);
v___x_465_ = lean_nat_dec_le(v___x_462_, v___x_464_);
lean_dec(v___x_464_);
lean_dec(v___x_462_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; 
v___x_466_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2___redArg(v_exprToVarIndex_392_);
lean_dec_ref(v_exprToVarIndex_392_);
v___y_416_ = v___x_466_;
goto v___jp_415_;
}
else
{
v___y_416_ = v_exprToVarIndex_392_;
goto v___jp_415_;
}
}
}
}
v___jp_400_:
{
lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_402_ = lean_array_push(v_varToExpr_393_, v_e_388_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 2, v___x_402_);
lean_ctor_set(v___x_396_, 1, v___y_401_);
v___x_404_ = v___x_396_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_op_391_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v___y_401_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v___x_402_);
v___x_404_ = v_reuseFailAlloc_407_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v_size_398_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
v___jp_408_:
{
lean_object* v_size_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_size_411_ = lean_ctor_get(v___y_409_, 0);
v___x_412_ = lean_unsigned_to_nat(1u);
v___x_413_ = lean_nat_add(v_size_411_, v___x_412_);
lean_inc(v_size_398_);
lean_inc_ref(v_e_388_);
v___x_414_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_409_, v___x_413_, v_i_410_, v_e_388_, v_size_398_);
lean_dec(v_i_410_);
v___y_401_ = v___x_414_;
goto v___jp_400_;
}
v___jp_415_:
{
lean_object* v___x_417_; 
v___x_417_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(v___y_416_, v_e_388_);
switch(lean_obj_tag(v___x_417_))
{
case 0:
{
lean_object* v_index_418_; lean_object* v_size_419_; lean_object* v___x_420_; 
v_index_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_index_418_);
lean_dec_ref_known(v___x_417_, 3);
v_size_419_ = lean_ctor_get(v___y_416_, 0);
lean_inc(v_size_419_);
lean_inc(v_size_398_);
lean_inc_ref(v_e_388_);
v___x_420_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_416_, v_size_419_, v_index_418_, v_e_388_, v_size_398_);
lean_dec(v_index_418_);
v___y_401_ = v___x_420_;
goto v___jp_400_;
}
case 1:
{
lean_object* v_index_421_; 
v_index_421_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_index_421_);
lean_dec_ref_known(v___x_417_, 1);
v___y_409_ = v___y_416_;
v_i_410_ = v_index_421_;
goto v___jp_408_;
}
default: 
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_416_, v___x_422_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_index_424_; 
v_index_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_index_424_);
lean_dec_ref_known(v___x_423_, 1);
v___y_409_ = v___y_416_;
v_i_410_ = v_index_424_;
goto v___jp_408_;
}
else
{
v___y_401_ = v___y_416_;
goto v___jp_400_;
}
}
}
}
v___jp_425_:
{
lean_object* v_size_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v_size_428_ = lean_ctor_get(v___y_426_, 0);
v___x_429_ = lean_unsigned_to_nat(1u);
v___x_430_ = lean_nat_add(v_size_428_, v___x_429_);
lean_inc(v_size_398_);
lean_inc_ref(v_e_388_);
v___x_431_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_426_, v___x_430_, v_i_427_, v_e_388_, v_size_398_);
lean_dec(v_i_427_);
v___y_401_ = v___x_431_;
goto v___jp_400_;
}
v___jp_432_:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2___redArg(v_exprToVarIndex_392_);
lean_dec_ref(v_exprToVarIndex_392_);
v___x_434_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(v___x_433_, v_e_388_);
switch(lean_obj_tag(v___x_434_))
{
case 0:
{
lean_object* v_index_435_; lean_object* v_size_436_; lean_object* v___x_437_; 
v_index_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_index_435_);
lean_dec_ref_known(v___x_434_, 3);
v_size_436_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_size_436_);
lean_inc(v_size_398_);
lean_inc_ref(v_e_388_);
v___x_437_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_433_, v_size_436_, v_index_435_, v_e_388_, v_size_398_);
lean_dec(v_index_435_);
v___y_401_ = v___x_437_;
goto v___jp_400_;
}
case 1:
{
lean_object* v_index_438_; 
v_index_438_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_index_438_);
lean_dec_ref_known(v___x_434_, 1);
v___y_426_ = v___x_433_;
v_i_427_ = v_index_438_;
goto v___jp_425_;
}
default: 
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_433_, v___x_439_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_index_441_; 
v_index_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_index_441_);
lean_dec_ref_known(v___x_440_, 1);
v___y_426_ = v___x_433_;
v_i_427_ = v_index_441_;
goto v___jp_425_;
}
else
{
v___y_401_ = v___x_433_;
goto v___jp_400_;
}
}
}
}
}
}
else
{
lean_object* v_val_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_479_; 
lean_dec_ref(v_e_388_);
v_val_471_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_479_ == 0)
{
v___x_473_ = v___x_394_;
v_isShared_474_ = v_isSharedCheck_479_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_val_471_);
lean_dec(v___x_394_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_479_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v_val_471_);
lean_ctor_set(v___x_475_, 1, v_a_389_);
if (v_isShared_474_ == 0)
{
lean_ctor_set_tag(v___x_473_, 0);
lean_ctor_set(v___x_473_, 0, v___x_475_);
v___x_477_ = v___x_473_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg___boxed(lean_object* v_e_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_480_, v_a_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar(lean_object* v_e_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_484_, v_a_485_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___boxed(lean_object* v_e_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar(v_e_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
lean_dec(v_a_499_);
lean_dec_ref(v_a_498_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0(lean_object* v_00_u03b2_504_, lean_object* v_m_505_, lean_object* v_a_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_m_505_, v_a_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___boxed(lean_object* v_00_u03b2_508_, lean_object* v_m_509_, lean_object* v_a_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0(v_00_u03b2_508_, v_m_509_, v_a_510_);
lean_dec_ref(v_a_510_);
lean_dec_ref(v_m_509_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1(lean_object* v_00_u03b2_512_, lean_object* v_m_513_, lean_object* v_query_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(v_m_513_, v_query_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___boxed(lean_object* v_00_u03b2_516_, lean_object* v_m_517_, lean_object* v_query_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1(v_00_u03b2_516_, v_m_517_, v_query_518_);
lean_dec_ref(v_query_518_);
lean_dec_ref(v_m_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2(lean_object* v_00_u03b2_520_, lean_object* v_m_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2___redArg(v_m_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2___boxed(lean_object* v_00_u03b2_523_, lean_object* v_m_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2(v_00_u03b2_523_, v_m_524_);
lean_dec_ref(v_m_524_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0(lean_object* v_00_u03b2_526_, lean_object* v_m_527_, lean_object* v_query_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_m_527_, v_query_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_530_, lean_object* v_m_531_, lean_object* v_query_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0(v_00_u03b2_530_, v_m_531_, v_query_532_);
lean_dec_ref(v_query_532_);
lean_dec_ref(v_m_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2(lean_object* v_00_u03b2_534_, lean_object* v_m_535_, lean_object* v_query_536_, lean_object* v_x_537_, lean_object* v_x_538_, lean_object* v_x_539_, lean_object* v_x_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_m_535_, v_query_536_, v_x_537_, v_x_538_, v_x_539_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_542_, lean_object* v_m_543_, lean_object* v_query_544_, lean_object* v_x_545_, lean_object* v_x_546_, lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2(v_00_u03b2_542_, v_m_543_, v_query_544_, v_x_545_, v_x_546_, v_x_547_, v_x_548_);
lean_dec_ref(v_query_544_);
lean_dec_ref(v_m_543_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4(lean_object* v_00_u03b2_550_, lean_object* v_init_551_, lean_object* v_b_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4___redArg(v_init_551_, v_b_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4___boxed(lean_object* v_00_u03b2_554_, lean_object* v_init_555_, lean_object* v_b_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4(v_00_u03b2_554_, v_init_555_, v_b_556_);
lean_dec_ref(v_b_556_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_558_, lean_object* v_b_559_, lean_object* v_acc_560_, lean_object* v_i_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4_spec__5___redArg(v_b_559_, v_acc_560_, v_i_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_563_, lean_object* v_b_564_, lean_object* v_acc_565_, lean_object* v_i_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__2_spec__4_spec__5(v_00_u03b2_563_, v_b_564_, v_acc_565_, v_i_566_);
lean_dec_ref(v_b_564_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(lean_object* v_msgData_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; lean_object* v_env_575_; lean_object* v___x_576_; lean_object* v_mctx_577_; lean_object* v_lctx_578_; lean_object* v_options_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_574_ = lean_st_ref_get(v___y_572_);
v_env_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc_ref(v_env_575_);
lean_dec(v___x_574_);
v___x_576_ = lean_st_ref_get(v___y_570_);
v_mctx_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc_ref(v_mctx_577_);
lean_dec(v___x_576_);
v_lctx_578_ = lean_ctor_get(v___y_569_, 2);
v_options_579_ = lean_ctor_get(v___y_571_, 2);
lean_inc_ref(v_options_579_);
lean_inc_ref(v_lctx_578_);
v___x_580_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_580_, 0, v_env_575_);
lean_ctor_set(v___x_580_, 1, v_mctx_577_);
lean_ctor_set(v___x_580_, 2, v_lctx_578_);
lean_ctor_set(v___x_580_, 3, v_options_579_);
v___x_581_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v_msgData_568_);
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1___boxed(lean_object* v_msgData_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msgData_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(lean_object* v_msg_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_ref_596_; lean_object* v___x_597_; lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_606_; 
v_ref_596_ = lean_ctor_get(v___y_593_, 5);
v___x_597_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_606_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_606_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_606_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_604_; 
lean_inc(v_ref_596_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v_ref_596_);
lean_ctor_set(v___x_602_, 1, v_a_598_);
if (v_isShared_601_ == 0)
{
lean_ctor_set_tag(v___x_600_, 1);
lean_ctor_set(v___x_600_, 0, v___x_602_);
v___x_604_ = v___x_600_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg___boxed(lean_object* v_msg_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__0(lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
if (lean_obj_tag(v_a_614_) == 0)
{
lean_object* v___x_616_; 
v___x_616_ = l_List_reverse___redArg(v_a_615_);
return v___x_616_;
}
else
{
lean_object* v_head_617_; lean_object* v_tail_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_627_; 
v_head_617_ = lean_ctor_get(v_a_614_, 0);
v_tail_618_ = lean_ctor_get(v_a_614_, 1);
v_isSharedCheck_627_ = !lean_is_exclusive(v_a_614_);
if (v_isSharedCheck_627_ == 0)
{
v___x_620_ = v_a_614_;
v_isShared_621_ = v_isSharedCheck_627_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_tail_618_);
lean_inc(v_head_617_);
lean_dec(v_a_614_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_627_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_622_ = l_Lean_MessageData_ofExpr(v_head_617_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 1, v_a_615_);
lean_ctor_set(v___x_620_, 0, v___x_622_);
v___x_624_ = v___x_620_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_a_615_);
v___x_624_ = v_reuseFailAlloc_626_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
v_a_614_ = v_tail_618_;
v_a_615_ = v___x_624_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__0));
v___x_630_ = l_Lean_stringToMessageData(v___x_629_);
return v___x_630_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__2));
v___x_633_ = l_Lean_stringToMessageData(v___x_632_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__4));
v___x_636_ = l_Lean_stringToMessageData(v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(lean_object* v_idx_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_varToExpr_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v_varToExpr_646_ = lean_ctor_get(v_a_638_, 2);
v___x_647_ = lean_array_get_size(v_varToExpr_646_);
v___x_648_ = lean_nat_dec_lt(v_idx_637_, v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
lean_inc_ref(v_varToExpr_646_);
lean_dec_ref(v_a_638_);
v___x_649_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1);
v___x_650_ = l_Nat_reprFast(v_idx_637_);
v___x_651_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
v___x_652_ = l_Lean_MessageData_ofFormat(v___x_651_);
v___x_653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_649_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3);
v___x_655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_653_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = l_Nat_reprFast(v___x_647_);
v___x_657_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
v___x_658_ = l_Lean_MessageData_ofFormat(v___x_657_);
v___x_659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_655_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5);
v___x_661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = lean_array_to_list(v_varToExpr_646_);
v___x_663_ = lean_box(0);
v___x_664_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__0(v___x_662_, v___x_663_);
v___x_665_ = l_Lean_MessageData_ofList(v___x_664_);
v___x_666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_661_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v___x_666_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
return v___x_667_;
}
else
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = lean_array_fget(v_varToExpr_646_, v_idx_637_);
lean_dec(v_idx_637_);
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
lean_ctor_set(v___x_669_, 1, v_a_638_);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___boxed(lean_object* v_idx_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(v_idx_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(lean_object* v_00_u03b1_681_, lean_object* v_msg_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_682_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___boxed(lean_object* v_00_u03b1_692_, lean_object* v_msg_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(v_00_u03b1_692_, v_msg_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec_ref(v___y_694_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___lam__0(lean_object* v_c_703_){
_start:
{
lean_object* v___y_705_; 
if (lean_obj_tag(v_c_703_) == 0)
{
lean_object* v___x_709_; 
v___x_709_ = lean_unsigned_to_nat(0u);
v___y_705_ = v___x_709_;
goto v___jp_704_;
}
else
{
lean_object* v_val_710_; 
v_val_710_ = lean_ctor_get(v_c_703_, 0);
v___y_705_ = v_val_710_;
goto v___jp_704_;
}
v___jp_704_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_706_ = lean_unsigned_to_nat(1u);
v___x_707_ = lean_nat_add(v___y_705_, v___x_706_);
v___x_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___lam__0___boxed(lean_object* v_c_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___lam__0(v_c_711_);
lean_dec(v_c_711_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(lean_object* v_m_713_, lean_object* v_query_714_, lean_object* v_x_715_, lean_object* v_x_716_, lean_object* v_x_717_){
_start:
{
lean_object* v_zero_718_; uint8_t v_isZero_719_; 
v_zero_718_ = lean_unsigned_to_nat(0u);
v_isZero_719_ = lean_nat_dec_eq(v_x_716_, v_zero_718_);
if (v_isZero_719_ == 1)
{
lean_dec(v_x_717_);
lean_dec(v_x_716_);
if (lean_obj_tag(v_x_715_) == 0)
{
lean_object* v___x_720_; 
v___x_720_ = lean_box(2);
return v___x_720_;
}
else
{
lean_object* v_val_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
v_val_721_ = lean_ctor_get(v_x_715_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v_x_715_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v_x_715_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_val_721_);
lean_dec(v_x_715_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_val_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
else
{
lean_object* v_keyArray_729_; lean_object* v_valueArray_730_; lean_object* v___x_731_; uint8_t v_isSome_732_; 
v_keyArray_729_ = lean_ctor_get(v_m_713_, 1);
v_valueArray_730_ = lean_ctor_get(v_m_713_, 2);
v___x_731_ = lean_array_fget_borrowed(v_keyArray_729_, v_x_717_);
v_isSome_732_ = lean_noption_is_some(v___x_731_);
if (v_isSome_732_ == 0)
{
lean_dec(v_x_716_);
if (lean_obj_tag(v_x_715_) == 0)
{
lean_object* v___x_733_; 
v___x_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_733_, 0, v_x_717_);
return v___x_733_;
}
else
{
lean_object* v_val_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec(v_x_717_);
v_val_734_ = lean_ctor_get(v_x_715_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v_x_715_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v_x_715_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_val_734_);
lean_dec(v_x_715_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_val_734_);
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
else
{
lean_object* v_one_742_; lean_object* v_n_743_; lean_object* v___y_745_; 
v_one_742_ = lean_unsigned_to_nat(1u);
v_n_743_ = lean_nat_sub(v_x_716_, v_one_742_);
lean_dec(v_x_716_);
if (v_isSome_732_ == 0)
{
goto v___jp_751_;
}
else
{
lean_object* v___x_753_; uint8_t v_isSome_754_; 
v___x_753_ = lean_array_fget_borrowed(v_valueArray_730_, v_x_717_);
v_isSome_754_ = lean_noption_is_some(v___x_753_);
if (v_isSome_754_ == 0)
{
goto v___jp_751_;
}
else
{
lean_object* v_val_755_; uint8_t v___x_756_; 
lean_inc(v___x_731_);
v_val_755_ = lean_noption_get(v___x_731_);
v___x_756_ = lean_nat_dec_eq(v_val_755_, v_query_714_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
lean_dec(v_val_755_);
v___x_757_ = lean_array_get_size(v_keyArray_729_);
v___x_758_ = lean_nat_add(v_x_717_, v_one_742_);
lean_dec(v_x_717_);
v___x_759_ = lean_nat_dec_lt(v___x_758_, v___x_757_);
if (v___x_759_ == 0)
{
lean_dec(v___x_758_);
v_x_716_ = v_n_743_;
v_x_717_ = v_zero_718_;
goto _start;
}
else
{
v_x_716_ = v_n_743_;
v_x_717_ = v___x_758_;
goto _start;
}
}
else
{
lean_object* v_val_762_; lean_object* v___x_763_; 
lean_dec(v_n_743_);
lean_dec(v_x_715_);
lean_inc(v___x_753_);
v_val_762_ = lean_noption_get(v___x_753_);
v___x_763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_763_, 0, v_x_717_);
lean_ctor_set(v___x_763_, 1, v_val_755_);
lean_ctor_set(v___x_763_, 2, v_val_762_);
return v___x_763_;
}
}
}
v___jp_744_:
{
lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_746_ = lean_array_get_size(v_keyArray_729_);
v___x_747_ = lean_nat_add(v_x_717_, v_one_742_);
lean_dec(v_x_717_);
v___x_748_ = lean_nat_dec_lt(v___x_747_, v___x_746_);
if (v___x_748_ == 0)
{
lean_dec(v___x_747_);
v_x_715_ = v___y_745_;
v_x_716_ = v_n_743_;
v_x_717_ = v_zero_718_;
goto _start;
}
else
{
v_x_715_ = v___y_745_;
v_x_716_ = v_n_743_;
v_x_717_ = v___x_747_;
goto _start;
}
}
v___jp_751_:
{
if (lean_obj_tag(v_x_715_) == 0)
{
lean_object* v___x_752_; 
lean_inc(v_x_717_);
v___x_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_752_, 0, v_x_717_);
v___y_745_ = v___x_752_;
goto v___jp_744_;
}
else
{
v___y_745_ = v_x_715_;
goto v___jp_744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg___boxed(lean_object* v_m_764_, lean_object* v_query_765_, lean_object* v_x_766_, lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_m_764_, v_query_765_, v_x_766_, v_x_767_, v_x_768_);
lean_dec(v_query_765_);
lean_dec_ref(v_m_764_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0___redArg(lean_object* v_m_770_, lean_object* v_query_771_){
_start:
{
lean_object* v_keyArray_772_; lean_object* v___x_773_; uint64_t v___x_774_; uint64_t v___x_775_; uint64_t v___x_776_; uint64_t v_fold_777_; uint64_t v___x_778_; uint64_t v___x_779_; uint64_t v___x_780_; size_t v___x_781_; size_t v___x_782_; size_t v___x_783_; size_t v___x_784_; size_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v_keyArray_772_ = lean_ctor_get(v_m_770_, 1);
v___x_773_ = lean_array_get_size(v_keyArray_772_);
v___x_774_ = lean_uint64_of_nat(v_query_771_);
v___x_775_ = 32ULL;
v___x_776_ = lean_uint64_shift_right(v___x_774_, v___x_775_);
v_fold_777_ = lean_uint64_xor(v___x_774_, v___x_776_);
v___x_778_ = 16ULL;
v___x_779_ = lean_uint64_shift_right(v_fold_777_, v___x_778_);
v___x_780_ = lean_uint64_xor(v_fold_777_, v___x_779_);
v___x_781_ = lean_uint64_to_usize(v___x_780_);
v___x_782_ = lean_usize_of_nat(v___x_773_);
v___x_783_ = ((size_t)1ULL);
v___x_784_ = lean_usize_sub(v___x_782_, v___x_783_);
v___x_785_ = lean_usize_land(v___x_781_, v___x_784_);
v___x_786_ = lean_usize_to_nat(v___x_785_);
v___x_787_ = lean_box(0);
v___x_788_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_m_770_, v_query_771_, v___x_787_, v___x_773_, v___x_786_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0___redArg___boxed(lean_object* v_m_789_, lean_object* v_query_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0___redArg(v_m_789_, v_query_790_);
lean_dec(v_query_790_);
lean_dec_ref(v_m_789_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2_spec__3___redArg(lean_object* v_b_792_, lean_object* v_acc_793_, lean_object* v_i_794_){
_start:
{
lean_object* v___y_796_; lean_object* v_keyArray_804_; lean_object* v_valueArray_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v_keyArray_804_ = lean_ctor_get(v_b_792_, 1);
v_valueArray_805_ = lean_ctor_get(v_b_792_, 2);
v___x_806_ = lean_array_get_size(v_keyArray_804_);
v___x_807_ = lean_nat_dec_lt(v_i_794_, v___x_806_);
if (v___x_807_ == 0)
{
lean_dec(v_i_794_);
return v_acc_793_;
}
else
{
lean_object* v___x_808_; uint8_t v_isSome_809_; 
v___x_808_ = lean_array_fget_borrowed(v_keyArray_804_, v_i_794_);
v_isSome_809_ = lean_noption_is_some(v___x_808_);
if (v_isSome_809_ == 0)
{
goto v___jp_800_;
}
else
{
lean_object* v___x_810_; uint8_t v_isSome_811_; 
v___x_810_ = lean_array_fget_borrowed(v_valueArray_805_, v_i_794_);
v_isSome_811_ = lean_noption_is_some(v___x_810_);
if (v_isSome_811_ == 0)
{
goto v___jp_800_;
}
else
{
lean_object* v_val_812_; lean_object* v_val_813_; lean_object* v_i_815_; lean_object* v___x_820_; 
lean_inc(v___x_808_);
v_val_812_ = lean_noption_get(v___x_808_);
lean_inc(v___x_810_);
v_val_813_ = lean_noption_get(v___x_810_);
v___x_820_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0___redArg(v_acc_793_, v_val_812_);
switch(lean_obj_tag(v___x_820_))
{
case 0:
{
lean_object* v_index_821_; lean_object* v_size_822_; lean_object* v___x_823_; 
v_index_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_index_821_);
lean_dec_ref_known(v___x_820_, 3);
v_size_822_ = lean_ctor_get(v_acc_793_, 0);
lean_inc(v_size_822_);
v___x_823_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_793_, v_size_822_, v_index_821_, v_val_812_, v_val_813_);
lean_dec(v_index_821_);
v___y_796_ = v___x_823_;
goto v___jp_795_;
}
case 1:
{
lean_object* v_index_824_; 
v_index_824_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_index_824_);
lean_dec_ref_known(v___x_820_, 1);
v_i_815_ = v_index_824_;
goto v___jp_814_;
}
default: 
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_793_, v___x_825_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_index_827_; 
v_index_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_index_827_);
lean_dec_ref_known(v___x_826_, 1);
v_i_815_ = v_index_827_;
goto v___jp_814_;
}
else
{
lean_dec(v_val_813_);
lean_dec(v_val_812_);
v___y_796_ = v_acc_793_;
goto v___jp_795_;
}
}
}
v___jp_814_:
{
lean_object* v_size_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v_size_816_ = lean_ctor_get(v_acc_793_, 0);
v___x_817_ = lean_unsigned_to_nat(1u);
v___x_818_ = lean_nat_add(v_size_816_, v___x_817_);
v___x_819_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_793_, v___x_818_, v_i_815_, v_val_812_, v_val_813_);
lean_dec(v_i_815_);
v___y_796_ = v___x_819_;
goto v___jp_795_;
}
}
}
}
v___jp_795_:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_unsigned_to_nat(1u);
v___x_798_ = lean_nat_add(v_i_794_, v___x_797_);
lean_dec(v_i_794_);
v_acc_793_ = v___y_796_;
v_i_794_ = v___x_798_;
goto _start;
}
v___jp_800_:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_unsigned_to_nat(1u);
v___x_802_ = lean_nat_add(v_i_794_, v___x_801_);
lean_dec(v_i_794_);
v_i_794_ = v___x_802_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_828_, lean_object* v_acc_829_, lean_object* v_i_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2_spec__3___redArg(v_b_828_, v_acc_829_, v_i_830_);
lean_dec_ref(v_b_828_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2___redArg(lean_object* v_init_832_, lean_object* v_b_833_){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2_spec__3___redArg(v_b_833_, v_init_832_, v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2___redArg___boxed(lean_object* v_init_836_, lean_object* v_b_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2___redArg(v_init_836_, v_b_837_);
lean_dec_ref(v_b_837_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1___redArg(lean_object* v_m_839_){
_start:
{
lean_object* v_keyArray_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v_cellCount_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v_target_847_; lean_object* v___x_848_; 
v_keyArray_840_ = lean_ctor_get(v_m_839_, 1);
v___x_841_ = lean_array_get_size(v_keyArray_840_);
v___x_842_ = lean_unsigned_to_nat(2u);
v_cellCount_843_ = lean_nat_mul(v___x_841_, v___x_842_);
v___x_844_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_843_);
v___x_845_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_843_);
v___x_846_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_843_);
v_target_847_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_847_, 0, v___x_844_);
lean_ctor_set(v_target_847_, 1, v___x_845_);
lean_ctor_set(v_target_847_, 2, v___x_846_);
v___x_848_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2___redArg(v_target_847_, v_m_839_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1___redArg___boxed(lean_object* v_m_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1___redArg(v_m_849_);
lean_dec_ref(v_m_849_);
return v_res_850_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___closed__0(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_box(0);
v___x_852_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___lam__0(v___x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(lean_object* v_coeff_853_, lean_object* v_e_854_, lean_object* v_a_855_){
_start:
{
lean_object* v___x_857_; lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_948_; 
v___x_857_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_854_, v_a_855_);
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_948_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_948_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_948_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v_fst_862_; lean_object* v_snd_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_947_; 
v_fst_862_ = lean_ctor_get(v_a_858_, 0);
v_snd_863_ = lean_ctor_get(v_a_858_, 1);
v_isSharedCheck_947_ = !lean_is_exclusive(v_a_858_);
if (v_isSharedCheck_947_ == 0)
{
v___x_865_ = v_a_858_;
v_isShared_866_ = v_isSharedCheck_947_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_snd_863_);
lean_inc(v_fst_862_);
lean_dec(v_a_858_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_947_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___y_868_; lean_object* v___x_875_; 
v___x_875_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0___redArg(v_coeff_853_, v_fst_862_);
switch(lean_obj_tag(v___x_875_))
{
case 0:
{
lean_object* v_index_876_; lean_object* v_value_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v_val_880_; lean_object* v_size_881_; lean_object* v___x_882_; 
v_index_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_index_876_);
v_value_877_ = lean_ctor_get(v___x_875_, 2);
lean_inc(v_value_877_);
lean_dec_ref_known(v___x_875_, 3);
v___x_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_878_, 0, v_value_877_);
v___x_879_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___lam__0(v___x_878_);
lean_dec_ref_known(v___x_878_, 1);
v_val_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_val_880_);
lean_dec(v___x_879_);
v_size_881_ = lean_ctor_get(v_coeff_853_, 0);
lean_inc(v_size_881_);
v___x_882_ = l_Std_DHashMap_Raw_setEntry___redArg(v_coeff_853_, v_size_881_, v_index_876_, v_fst_862_, v_val_880_);
lean_dec(v_index_876_);
v___y_868_ = v___x_882_;
goto v___jp_867_;
}
case 1:
{
lean_object* v_index_883_; lean_object* v___x_884_; lean_object* v_val_885_; lean_object* v___y_887_; lean_object* v_i_888_; lean_object* v_size_903_; lean_object* v_keyArray_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v_index_883_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_index_883_);
lean_dec_ref_known(v___x_875_, 1);
v___x_884_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___closed__0);
v_val_885_ = lean_ctor_get(v___x_884_, 0);
v_size_903_ = lean_ctor_get(v_coeff_853_, 0);
v_keyArray_904_ = lean_ctor_get(v_coeff_853_, 1);
v___x_905_ = lean_unsigned_to_nat(1u);
v___x_906_ = lean_nat_add(v_size_903_, v___x_905_);
v___x_907_ = lean_array_get_size(v_keyArray_904_);
v___x_908_ = lean_nat_dec_lt(v___x_906_, v___x_907_);
if (v___x_908_ == 0)
{
lean_dec(v___x_906_);
lean_dec(v_index_883_);
goto v___jp_893_;
}
else
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_909_ = lean_unsigned_to_nat(4u);
v___x_910_ = lean_nat_mul(v___x_906_, v___x_909_);
v___x_911_ = lean_unsigned_to_nat(3u);
v___x_912_ = lean_nat_mul(v___x_907_, v___x_911_);
v___x_913_ = lean_nat_dec_le(v___x_910_, v___x_912_);
lean_dec(v___x_912_);
lean_dec(v___x_910_);
if (v___x_913_ == 0)
{
lean_dec(v___x_906_);
lean_dec(v_index_883_);
goto v___jp_893_;
}
else
{
lean_object* v___x_914_; 
lean_inc(v_val_885_);
v___x_914_ = l_Std_DHashMap_Raw_setEntry___redArg(v_coeff_853_, v___x_906_, v_index_883_, v_fst_862_, v_val_885_);
lean_dec(v_index_883_);
v___y_868_ = v___x_914_;
goto v___jp_867_;
}
}
v___jp_886_:
{
lean_object* v_size_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_size_889_ = lean_ctor_get(v___y_887_, 0);
v___x_890_ = lean_unsigned_to_nat(1u);
v___x_891_ = lean_nat_add(v_size_889_, v___x_890_);
lean_inc(v_val_885_);
v___x_892_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_887_, v___x_891_, v_i_888_, v_fst_862_, v_val_885_);
lean_dec(v_i_888_);
v___y_868_ = v___x_892_;
goto v___jp_867_;
}
v___jp_893_:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1___redArg(v_coeff_853_);
lean_dec_ref(v_coeff_853_);
v___x_895_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0___redArg(v___x_894_, v_fst_862_);
switch(lean_obj_tag(v___x_895_))
{
case 0:
{
lean_object* v_index_896_; lean_object* v_size_897_; lean_object* v___x_898_; 
v_index_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_index_896_);
lean_dec_ref_known(v___x_895_, 3);
v_size_897_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_size_897_);
lean_inc(v_val_885_);
v___x_898_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_894_, v_size_897_, v_index_896_, v_fst_862_, v_val_885_);
lean_dec(v_index_896_);
v___y_868_ = v___x_898_;
goto v___jp_867_;
}
case 1:
{
lean_object* v_index_899_; 
v_index_899_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_index_899_);
lean_dec_ref_known(v___x_895_, 1);
v___y_887_ = v___x_894_;
v_i_888_ = v_index_899_;
goto v___jp_886_;
}
default: 
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = lean_unsigned_to_nat(0u);
v___x_901_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_894_, v___x_900_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_index_902_; 
v_index_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_index_902_);
lean_dec_ref_known(v___x_901_, 1);
v___y_887_ = v___x_894_;
v_i_888_ = v_index_902_;
goto v___jp_886_;
}
else
{
lean_dec(v_fst_862_);
v___y_868_ = v___x_894_;
goto v___jp_867_;
}
}
}
}
}
default: 
{
lean_object* v___x_915_; lean_object* v_val_916_; lean_object* v___y_918_; lean_object* v_i_919_; lean_object* v___y_925_; lean_object* v_size_934_; lean_object* v_keyArray_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_915_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___closed__0);
v_val_916_ = lean_ctor_get(v___x_915_, 0);
v_size_934_ = lean_ctor_get(v_coeff_853_, 0);
v_keyArray_935_ = lean_ctor_get(v_coeff_853_, 1);
v___x_936_ = lean_unsigned_to_nat(1u);
v___x_937_ = lean_nat_add(v_size_934_, v___x_936_);
v___x_938_ = lean_array_get_size(v_keyArray_935_);
v___x_939_ = lean_nat_dec_lt(v___x_937_, v___x_938_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; 
lean_dec(v___x_937_);
v___x_940_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1___redArg(v_coeff_853_);
lean_dec_ref(v_coeff_853_);
v___y_925_ = v___x_940_;
goto v___jp_924_;
}
else
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_941_ = lean_unsigned_to_nat(4u);
v___x_942_ = lean_nat_mul(v___x_937_, v___x_941_);
lean_dec(v___x_937_);
v___x_943_ = lean_unsigned_to_nat(3u);
v___x_944_ = lean_nat_mul(v___x_938_, v___x_943_);
v___x_945_ = lean_nat_dec_le(v___x_942_, v___x_944_);
lean_dec(v___x_944_);
lean_dec(v___x_942_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; 
v___x_946_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1___redArg(v_coeff_853_);
lean_dec_ref(v_coeff_853_);
v___y_925_ = v___x_946_;
goto v___jp_924_;
}
else
{
v___y_925_ = v_coeff_853_;
goto v___jp_924_;
}
}
v___jp_917_:
{
lean_object* v_size_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v_size_920_ = lean_ctor_get(v___y_918_, 0);
v___x_921_ = lean_unsigned_to_nat(1u);
v___x_922_ = lean_nat_add(v_size_920_, v___x_921_);
lean_inc(v_val_916_);
v___x_923_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_918_, v___x_922_, v_i_919_, v_fst_862_, v_val_916_);
lean_dec(v_i_919_);
v___y_868_ = v___x_923_;
goto v___jp_867_;
}
v___jp_924_:
{
lean_object* v___x_926_; 
v___x_926_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0___redArg(v___y_925_, v_fst_862_);
switch(lean_obj_tag(v___x_926_))
{
case 0:
{
lean_object* v_index_927_; lean_object* v_size_928_; lean_object* v___x_929_; 
v_index_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_index_927_);
lean_dec_ref_known(v___x_926_, 3);
v_size_928_ = lean_ctor_get(v___y_925_, 0);
lean_inc(v_size_928_);
lean_inc(v_val_916_);
v___x_929_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_925_, v_size_928_, v_index_927_, v_fst_862_, v_val_916_);
lean_dec(v_index_927_);
v___y_868_ = v___x_929_;
goto v___jp_867_;
}
case 1:
{
lean_object* v_index_930_; 
v_index_930_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_index_930_);
lean_dec_ref_known(v___x_926_, 1);
v___y_918_ = v___y_925_;
v_i_919_ = v_index_930_;
goto v___jp_917_;
}
default: 
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = lean_unsigned_to_nat(0u);
v___x_932_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_925_, v___x_931_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_index_933_; 
v_index_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_index_933_);
lean_dec_ref_known(v___x_932_, 1);
v___y_918_ = v___y_925_;
v_i_919_ = v_index_933_;
goto v___jp_917_;
}
else
{
lean_dec(v_fst_862_);
v___y_868_ = v___y_925_;
goto v___jp_867_;
}
}
}
}
}
}
v___jp_867_:
{
lean_object* v___x_870_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___y_868_);
v___x_870_ = v___x_865_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___y_868_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_snd_863_);
v___x_870_ = v_reuseFailAlloc_874_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_872_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_870_);
v___x_872_ = v___x_860_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___boxed(lean_object* v_coeff_949_, lean_object* v_e_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_949_, v_e_950_, v_a_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(lean_object* v_coeff_954_, lean_object* v_e_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_954_, v_e_955_, v_a_956_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___boxed(lean_object* v_coeff_965_, lean_object* v_e_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(v_coeff_965_, v_e_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
lean_dec(v_a_969_);
lean_dec_ref(v_a_968_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(lean_object* v_00_u03b2_976_, lean_object* v_m_977_, lean_object* v_query_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0___redArg(v_m_977_, v_query_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0___boxed(lean_object* v_00_u03b2_980_, lean_object* v_m_981_, lean_object* v_query_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(v_00_u03b2_980_, v_m_981_, v_query_982_);
lean_dec(v_query_982_);
lean_dec_ref(v_m_981_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1(lean_object* v_00_u03b2_984_, lean_object* v_m_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1___redArg(v_m_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1___boxed(lean_object* v_00_u03b2_987_, lean_object* v_m_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1(v_00_u03b2_987_, v_m_988_);
lean_dec_ref(v_m_988_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(lean_object* v_00_u03b2_990_, lean_object* v_m_991_, lean_object* v_query_992_, lean_object* v_x_993_, lean_object* v_x_994_, lean_object* v_x_995_, lean_object* v_x_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_m_991_, v_query_992_, v_x_993_, v_x_994_, v_x_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_998_, lean_object* v_m_999_, lean_object* v_query_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(v_00_u03b2_998_, v_m_999_, v_query_1000_, v_x_1001_, v_x_1002_, v_x_1003_, v_x_1004_);
lean_dec(v_query_1000_);
lean_dec_ref(v_m_999_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2(lean_object* v_00_u03b2_1006_, lean_object* v_init_1007_, lean_object* v_b_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2___redArg(v_init_1007_, v_b_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1010_, lean_object* v_init_1011_, lean_object* v_b_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2(v_00_u03b2_1010_, v_init_1011_, v_b_1012_);
lean_dec_ref(v_b_1012_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1014_, lean_object* v_b_1015_, lean_object* v_acc_1016_, lean_object* v_i_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2_spec__3___redArg(v_b_1015_, v_acc_1016_, v_i_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1019_, lean_object* v_b_1020_, lean_object* v_acc_1021_, lean_object* v_i_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1_spec__2_spec__3(v_00_u03b2_1019_, v_b_1020_, v_acc_1021_, v_i_1022_);
lean_dec_ref(v_b_1020_);
return v_res_1023_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1024_; double v___x_1025_; 
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = lean_float_of_nat(v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(lean_object* v_cls_1029_, lean_object* v_msg_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_ref_1037_; lean_object* v___x_1038_; lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1084_; 
v_ref_1037_ = lean_ctor_get(v___y_1034_, 5);
v___x_1038_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_1030_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1041_ = v___x_1038_;
v_isShared_1042_ = v_isSharedCheck_1084_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1084_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v_traceState_1044_; lean_object* v_env_1045_; lean_object* v_nextMacroScope_1046_; lean_object* v_ngen_1047_; lean_object* v_auxDeclNGen_1048_; lean_object* v_cache_1049_; lean_object* v_messages_1050_; lean_object* v_infoState_1051_; lean_object* v_snapshotTasks_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1083_; 
v___x_1043_ = lean_st_ref_take(v___y_1035_);
v_traceState_1044_ = lean_ctor_get(v___x_1043_, 4);
v_env_1045_ = lean_ctor_get(v___x_1043_, 0);
v_nextMacroScope_1046_ = lean_ctor_get(v___x_1043_, 1);
v_ngen_1047_ = lean_ctor_get(v___x_1043_, 2);
v_auxDeclNGen_1048_ = lean_ctor_get(v___x_1043_, 3);
v_cache_1049_ = lean_ctor_get(v___x_1043_, 5);
v_messages_1050_ = lean_ctor_get(v___x_1043_, 6);
v_infoState_1051_ = lean_ctor_get(v___x_1043_, 7);
v_snapshotTasks_1052_ = lean_ctor_get(v___x_1043_, 8);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1054_ = v___x_1043_;
v_isShared_1055_ = v_isSharedCheck_1083_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_snapshotTasks_1052_);
lean_inc(v_infoState_1051_);
lean_inc(v_messages_1050_);
lean_inc(v_cache_1049_);
lean_inc(v_traceState_1044_);
lean_inc(v_auxDeclNGen_1048_);
lean_inc(v_ngen_1047_);
lean_inc(v_nextMacroScope_1046_);
lean_inc(v_env_1045_);
lean_dec(v___x_1043_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1083_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
uint64_t v_tid_1056_; lean_object* v_traces_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1082_; 
v_tid_1056_ = lean_ctor_get_uint64(v_traceState_1044_, sizeof(void*)*1);
v_traces_1057_ = lean_ctor_get(v_traceState_1044_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_traceState_1044_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1059_ = v_traceState_1044_;
v_isShared_1060_ = v_isSharedCheck_1082_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_traces_1057_);
lean_dec(v_traceState_1044_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1082_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; double v___x_1062_; uint8_t v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1061_ = lean_box(0);
v___x_1062_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_1063_ = 0;
v___x_1064_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_1065_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1065_, 0, v_cls_1029_);
lean_ctor_set(v___x_1065_, 1, v___x_1061_);
lean_ctor_set(v___x_1065_, 2, v___x_1064_);
lean_ctor_set_float(v___x_1065_, sizeof(void*)*3, v___x_1062_);
lean_ctor_set_float(v___x_1065_, sizeof(void*)*3 + 8, v___x_1062_);
lean_ctor_set_uint8(v___x_1065_, sizeof(void*)*3 + 16, v___x_1063_);
v___x_1066_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_1067_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v_a_1039_);
lean_ctor_set(v___x_1067_, 2, v___x_1066_);
lean_inc(v_ref_1037_);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v_ref_1037_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = l_Lean_PersistentArray_push___redArg(v_traces_1057_, v___x_1068_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v___x_1069_);
v___x_1071_ = v___x_1059_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1069_);
lean_ctor_set_uint64(v_reuseFailAlloc_1081_, sizeof(void*)*1, v_tid_1056_);
v___x_1071_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1073_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 4, v___x_1071_);
v___x_1073_ = v___x_1054_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_env_1045_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_nextMacroScope_1046_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v_ngen_1047_);
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v_auxDeclNGen_1048_);
lean_ctor_set(v_reuseFailAlloc_1080_, 4, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1080_, 5, v_cache_1049_);
lean_ctor_set(v_reuseFailAlloc_1080_, 6, v_messages_1050_);
lean_ctor_set(v_reuseFailAlloc_1080_, 7, v_infoState_1051_);
lean_ctor_set(v_reuseFailAlloc_1080_, 8, v_snapshotTasks_1052_);
v___x_1073_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1074_ = lean_st_ref_put(v___y_1035_, v___x_1073_);
v___x_1075_ = lean_box(0);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
lean_ctor_set(v___x_1076_, 1, v___y_1031_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v___x_1076_);
v___x_1078_ = v___x_1041_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___boxed(lean_object* v_cls_1085_, lean_object* v_msg_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_1085_, v_msg_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
return v_res_1093_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6(void){
_start:
{
lean_object* v_cls_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v_cls_1104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_1105_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_1106_ = l_Lean_Name_append(v___x_1105_, v_cls_1104_);
return v___x_1106_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__7));
v___x_1109_ = l_Lean_stringToMessageData(v___x_1108_);
return v___x_1109_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__9));
v___x_1112_ = l_Lean_stringToMessageData(v___x_1111_);
return v___x_1112_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__11));
v___x_1115_ = l_Lean_stringToMessageData(v___x_1114_);
return v___x_1115_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__13));
v___x_1118_ = l_Lean_stringToMessageData(v___x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(lean_object* v_op_1119_, lean_object* v_coeff_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
if (lean_obj_tag(v_a_1121_) == 5)
{
lean_object* v_fn_1130_; 
v_fn_1130_ = lean_ctor_get(v_a_1121_, 0);
if (lean_obj_tag(v_fn_1130_) == 5)
{
lean_object* v_arg_1131_; lean_object* v_fn_1132_; lean_object* v_arg_1133_; uint8_t v___x_1134_; 
v_arg_1131_ = lean_ctor_get(v_a_1121_, 1);
v_fn_1132_ = lean_ctor_get(v_fn_1130_, 0);
v_arg_1133_ = lean_ctor_get(v_fn_1130_, 1);
lean_inc_ref(v_fn_1132_);
v___x_1134_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(v_fn_1132_);
if (v___x_1134_ == 0)
{
lean_object* v_options_1135_; uint8_t v_hasTrace_1136_; 
v_options_1135_ = lean_ctor_get(v_a_1127_, 2);
v_hasTrace_1136_ = lean_ctor_get_uint8(v_options_1135_, sizeof(void*)*1);
if (v_hasTrace_1136_ == 0)
{
lean_object* v___x_1137_; 
lean_dec_ref(v_op_1119_);
v___x_1137_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_1120_, v_a_1121_, v_a_1122_);
return v___x_1137_;
}
else
{
lean_object* v_inheritedTraceOptions_1138_; lean_object* v_cls_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v_inheritedTraceOptions_1138_ = lean_ctor_get(v_a_1127_, 13);
v_cls_1139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_1140_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_1141_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1138_, v_options_1135_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; 
lean_dec_ref(v_op_1119_);
v___x_1142_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_1120_, v_a_1121_, v_a_1122_);
return v___x_1142_;
}
else
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1143_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8);
lean_inc_ref(v_fn_1132_);
v___x_1144_ = l_Lean_MessageData_ofExpr(v_fn_1132_);
v___x_1145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1143_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
lean_inc_ref(v_arg_1133_);
v___x_1148_ = l_Lean_MessageData_ofExpr(v_arg_1133_);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
lean_ctor_set(v___x_1150_, 1, v___x_1146_);
lean_inc_ref(v_arg_1131_);
v___x_1151_ = l_Lean_MessageData_ofExpr(v_arg_1131_);
v___x_1152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_1119_);
v___x_1156_ = l_Lean_MessageData_ofExpr(v___x_1155_);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1154_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_1139_, v___x_1159_, v_a_1122_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v_snd_1162_; lean_object* v___x_1163_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1161_);
lean_dec_ref_known(v___x_1160_, 1);
v_snd_1162_ = lean_ctor_get(v_a_1161_, 1);
lean_inc(v_snd_1162_);
lean_dec(v_a_1161_);
v___x_1163_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_1120_, v_a_1121_, v_snd_1162_);
return v___x_1163_;
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec_ref_known(v_a_1121_, 2);
lean_dec_ref(v_coeff_1120_);
v_a_1164_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1160_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1160_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
}
else
{
lean_object* v___x_1172_; 
lean_inc_ref(v_arg_1133_);
lean_inc_ref(v_arg_1131_);
lean_dec_ref_known(v_a_1121_, 2);
lean_inc_ref(v_op_1119_);
v___x_1172_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_1119_, v_coeff_1120_, v_arg_1133_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v_fst_1174_; lean_object* v_snd_1175_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___x_1172_, 1);
v_fst_1174_ = lean_ctor_get(v_a_1173_, 0);
lean_inc(v_fst_1174_);
v_snd_1175_ = lean_ctor_get(v_a_1173_, 1);
lean_inc(v_snd_1175_);
lean_dec(v_a_1173_);
v_coeff_1120_ = v_fst_1174_;
v_a_1121_ = v_arg_1131_;
v_a_1122_ = v_snd_1175_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1131_);
lean_dec_ref(v_op_1119_);
return v___x_1172_;
}
}
}
else
{
lean_object* v___x_1177_; 
lean_dec_ref(v_op_1119_);
v___x_1177_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_1120_, v_a_1121_, v_a_1122_);
return v___x_1177_;
}
}
else
{
lean_object* v___x_1178_; 
lean_dec_ref(v_op_1119_);
v___x_1178_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_1120_, v_a_1121_, v_a_1122_);
return v___x_1178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___boxed(lean_object* v_op_1179_, lean_object* v_coeff_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_1179_, v_coeff_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(lean_object* v_cls_1191_, lean_object* v_msg_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_1191_, v_msg_1192_, v___y_1193_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___boxed(lean_object* v_cls_1202_, lean_object* v_msg_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(v_cls_1202_, v_msg_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
return v_res_1212_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0(void){
_start:
{
lean_object* v_cellCount_1213_; lean_object* v___x_1214_; 
v_cellCount_1213_ = lean_unsigned_to_nat(16u);
v___x_1214_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1213_);
return v___x_1214_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1(void){
_start:
{
lean_object* v_cellCount_1215_; lean_object* v___x_1216_; 
v_cellCount_1215_ = lean_unsigned_to_nat(16u);
v___x_1216_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1215_);
return v___x_1216_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__2(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1217_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1218_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1219_ = lean_unsigned_to_nat(0u);
v___x_1220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
lean_ctor_set(v___x_1220_, 1, v___x_1218_);
lean_ctor_set(v___x_1220_, 2, v___x_1217_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(lean_object* v_op_1221_, lean_object* v_e_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__2);
v___x_1232_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_1221_, v___x_1231_, v_e_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___boxed(lean_object* v_op_1233_, lean_object* v_e_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_op_1233_, v_e_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0___redArg(lean_object* v_m_1244_, lean_object* v_query_1245_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0___redArg(v_m_1244_, v_query_1245_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_index_1247_; lean_object* v_key_1248_; lean_object* v_value_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
v_index_1247_ = lean_ctor_get(v___x_1246_, 0);
v_key_1248_ = lean_ctor_get(v___x_1246_, 1);
v_value_1249_ = lean_ctor_get(v___x_1246_, 2);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1246_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_value_1249_);
lean_inc(v_key_1248_);
lean_inc(v_index_1247_);
lean_dec(v___x_1246_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_index_1247_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_key_1248_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v_value_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
else
{
lean_object* v___x_1257_; 
lean_dec(v___x_1246_);
v___x_1257_ = lean_box(1);
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0___redArg___boxed(lean_object* v_m_1258_, lean_object* v_query_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0___redArg(v_m_1258_, v_query_1259_);
lean_dec(v_query_1259_);
lean_dec_ref(v_m_1258_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0___redArg(lean_object* v_m_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0___redArg(v_m_1261_, v_a_1262_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_value_1264_; lean_object* v___x_1265_; 
v_value_1264_ = lean_ctor_get(v___x_1263_, 2);
lean_inc(v_value_1264_);
lean_dec_ref_known(v___x_1263_, 3);
v___x_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1265_, 0, v_value_1264_);
return v___x_1265_;
}
else
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_box(0);
return v___x_1266_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0___redArg___boxed(lean_object* v_m_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0___redArg(v_m_1267_, v_a_1268_);
lean_dec(v_a_1268_);
lean_dec_ref(v_m_1267_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(lean_object* v_snd_1270_, lean_object* v_b_1271_, lean_object* v_acc_1272_, lean_object* v_i_1273_){
_start:
{
lean_object* v___y_1275_; lean_object* v_keyArray_1283_; lean_object* v_valueArray_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v_keyArray_1283_ = lean_ctor_get(v_b_1271_, 1);
v_valueArray_1284_ = lean_ctor_get(v_b_1271_, 2);
v___x_1285_ = lean_array_get_size(v_keyArray_1283_);
v___x_1286_ = lean_nat_dec_lt(v_i_1273_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_dec(v_i_1273_);
return v_acc_1272_;
}
else
{
lean_object* v___x_1287_; uint8_t v_isSome_1288_; 
v___x_1287_ = lean_array_fget_borrowed(v_keyArray_1283_, v_i_1273_);
v_isSome_1288_ = lean_noption_is_some(v___x_1287_);
if (v_isSome_1288_ == 0)
{
goto v___jp_1279_;
}
else
{
lean_object* v___x_1289_; uint8_t v_isSome_1290_; 
v___x_1289_ = lean_array_fget_borrowed(v_valueArray_1284_, v_i_1273_);
v_isSome_1290_ = lean_noption_is_some(v___x_1289_);
if (v_isSome_1290_ == 0)
{
goto v___jp_1279_;
}
else
{
lean_object* v_val_1291_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v_i_1295_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v_i_1314_; lean_object* v___y_1320_; lean_object* v___y_1331_; lean_object* v___x_1362_; 
lean_inc(v___x_1287_);
v_val_1291_ = lean_noption_get(v___x_1287_);
v___x_1362_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0___redArg(v_snd_1270_, v_val_1291_);
if (lean_obj_tag(v___x_1362_) == 1)
{
lean_object* v_val_1363_; lean_object* v_val_1364_; uint8_t v___x_1365_; 
v_val_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_val_1363_);
lean_dec_ref_known(v___x_1362_, 1);
lean_inc(v___x_1289_);
v_val_1364_ = lean_noption_get(v___x_1289_);
v___x_1365_ = lean_nat_dec_le(v_val_1364_, v_val_1363_);
if (v___x_1365_ == 0)
{
lean_dec(v_val_1364_);
v___y_1331_ = v_val_1363_;
goto v___jp_1330_;
}
else
{
lean_dec(v_val_1363_);
v___y_1331_ = v_val_1364_;
goto v___jp_1330_;
}
}
else
{
lean_dec(v___x_1362_);
lean_dec(v_val_1291_);
v___y_1275_ = v_acc_1272_;
goto v___jp_1274_;
}
v___jp_1292_:
{
lean_object* v_size_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v_size_1296_ = lean_ctor_get(v___y_1294_, 0);
v___x_1297_ = lean_unsigned_to_nat(1u);
v___x_1298_ = lean_nat_add(v_size_1296_, v___x_1297_);
v___x_1299_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1294_, v___x_1298_, v_i_1295_, v_val_1291_, v___y_1293_);
lean_dec(v_i_1295_);
v___y_1275_ = v___x_1299_;
goto v___jp_1274_;
}
v___jp_1300_:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0___redArg(v___y_1302_, v_val_1291_);
switch(lean_obj_tag(v___x_1303_))
{
case 0:
{
lean_object* v_index_1304_; lean_object* v_size_1305_; lean_object* v___x_1306_; 
v_index_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_index_1304_);
lean_dec_ref_known(v___x_1303_, 3);
v_size_1305_ = lean_ctor_get(v___y_1302_, 0);
lean_inc(v_size_1305_);
v___x_1306_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1302_, v_size_1305_, v_index_1304_, v_val_1291_, v___y_1301_);
lean_dec(v_index_1304_);
v___y_1275_ = v___x_1306_;
goto v___jp_1274_;
}
case 1:
{
lean_object* v_index_1307_; 
v_index_1307_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_index_1307_);
lean_dec_ref_known(v___x_1303_, 1);
v___y_1293_ = v___y_1301_;
v___y_1294_ = v___y_1302_;
v_i_1295_ = v_index_1307_;
goto v___jp_1292_;
}
default: 
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1302_, v___x_1308_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_index_1310_; 
v_index_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_index_1310_);
lean_dec_ref_known(v___x_1309_, 1);
v___y_1293_ = v___y_1301_;
v___y_1294_ = v___y_1302_;
v_i_1295_ = v_index_1310_;
goto v___jp_1292_;
}
else
{
lean_dec(v___y_1301_);
lean_dec(v_val_1291_);
v___y_1275_ = v___y_1302_;
goto v___jp_1274_;
}
}
}
}
v___jp_1311_:
{
lean_object* v_size_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v_size_1315_ = lean_ctor_get(v___y_1313_, 0);
v___x_1316_ = lean_unsigned_to_nat(1u);
v___x_1317_ = lean_nat_add(v_size_1315_, v___x_1316_);
v___x_1318_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1313_, v___x_1317_, v_i_1314_, v_val_1291_, v___y_1312_);
lean_dec(v_i_1314_);
v___y_1275_ = v___x_1318_;
goto v___jp_1274_;
}
v___jp_1319_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1___redArg(v_acc_1272_);
lean_dec_ref(v_acc_1272_);
v___x_1322_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0___redArg(v___x_1321_, v_val_1291_);
switch(lean_obj_tag(v___x_1322_))
{
case 0:
{
lean_object* v_index_1323_; lean_object* v_size_1324_; lean_object* v___x_1325_; 
v_index_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_index_1323_);
lean_dec_ref_known(v___x_1322_, 3);
v_size_1324_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_size_1324_);
v___x_1325_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1321_, v_size_1324_, v_index_1323_, v_val_1291_, v___y_1320_);
lean_dec(v_index_1323_);
v___y_1275_ = v___x_1325_;
goto v___jp_1274_;
}
case 1:
{
lean_object* v_index_1326_; 
v_index_1326_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_index_1326_);
lean_dec_ref_known(v___x_1322_, 1);
v___y_1312_ = v___y_1320_;
v___y_1313_ = v___x_1321_;
v_i_1314_ = v_index_1326_;
goto v___jp_1311_;
}
default: 
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1321_, v___x_1327_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_index_1329_; 
v_index_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_index_1329_);
lean_dec_ref_known(v___x_1328_, 1);
v___y_1312_ = v___y_1320_;
v___y_1313_ = v___x_1321_;
v_i_1314_ = v_index_1329_;
goto v___jp_1311_;
}
else
{
lean_dec(v___y_1320_);
lean_dec(v_val_1291_);
v___y_1275_ = v___x_1321_;
goto v___jp_1274_;
}
}
}
}
v___jp_1330_:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0___redArg(v_acc_1272_, v_val_1291_);
switch(lean_obj_tag(v___x_1332_))
{
case 0:
{
lean_object* v_index_1333_; lean_object* v_size_1334_; lean_object* v___x_1335_; 
v_index_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_index_1333_);
lean_dec_ref_known(v___x_1332_, 3);
v_size_1334_ = lean_ctor_get(v_acc_1272_, 0);
lean_inc(v_size_1334_);
v___x_1335_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1272_, v_size_1334_, v_index_1333_, v_val_1291_, v___y_1331_);
lean_dec(v_index_1333_);
v___y_1275_ = v___x_1335_;
goto v___jp_1274_;
}
case 1:
{
lean_object* v_index_1336_; lean_object* v_size_1337_; lean_object* v_keyArray_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v_index_1336_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_index_1336_);
lean_dec_ref_known(v___x_1332_, 1);
v_size_1337_ = lean_ctor_get(v_acc_1272_, 0);
v_keyArray_1338_ = lean_ctor_get(v_acc_1272_, 1);
v___x_1339_ = lean_unsigned_to_nat(1u);
v___x_1340_ = lean_nat_add(v_size_1337_, v___x_1339_);
v___x_1341_ = lean_array_get_size(v_keyArray_1338_);
v___x_1342_ = lean_nat_dec_lt(v___x_1340_, v___x_1341_);
if (v___x_1342_ == 0)
{
lean_dec(v___x_1340_);
lean_dec(v_index_1336_);
v___y_1320_ = v___y_1331_;
goto v___jp_1319_;
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1343_ = lean_unsigned_to_nat(4u);
v___x_1344_ = lean_nat_mul(v___x_1340_, v___x_1343_);
v___x_1345_ = lean_unsigned_to_nat(3u);
v___x_1346_ = lean_nat_mul(v___x_1341_, v___x_1345_);
v___x_1347_ = lean_nat_dec_le(v___x_1344_, v___x_1346_);
lean_dec(v___x_1346_);
lean_dec(v___x_1344_);
if (v___x_1347_ == 0)
{
lean_dec(v___x_1340_);
lean_dec(v_index_1336_);
v___y_1320_ = v___y_1331_;
goto v___jp_1319_;
}
else
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1272_, v___x_1340_, v_index_1336_, v_val_1291_, v___y_1331_);
lean_dec(v_index_1336_);
v___y_1275_ = v___x_1348_;
goto v___jp_1274_;
}
}
}
default: 
{
lean_object* v_size_1349_; lean_object* v_keyArray_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v_size_1349_ = lean_ctor_get(v_acc_1272_, 0);
v_keyArray_1350_ = lean_ctor_get(v_acc_1272_, 1);
v___x_1351_ = lean_unsigned_to_nat(1u);
v___x_1352_ = lean_nat_add(v_size_1349_, v___x_1351_);
v___x_1353_ = lean_array_get_size(v_keyArray_1350_);
v___x_1354_ = lean_nat_dec_lt(v___x_1352_, v___x_1353_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; 
lean_dec(v___x_1352_);
v___x_1355_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1___redArg(v_acc_1272_);
lean_dec_ref(v_acc_1272_);
v___y_1301_ = v___y_1331_;
v___y_1302_ = v___x_1355_;
goto v___jp_1300_;
}
else
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1356_ = lean_unsigned_to_nat(4u);
v___x_1357_ = lean_nat_mul(v___x_1352_, v___x_1356_);
lean_dec(v___x_1352_);
v___x_1358_ = lean_unsigned_to_nat(3u);
v___x_1359_ = lean_nat_mul(v___x_1353_, v___x_1358_);
v___x_1360_ = lean_nat_dec_le(v___x_1357_, v___x_1359_);
lean_dec(v___x_1359_);
lean_dec(v___x_1357_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__1___redArg(v_acc_1272_);
lean_dec_ref(v_acc_1272_);
v___y_1301_ = v___y_1331_;
v___y_1302_ = v___x_1361_;
goto v___jp_1300_;
}
else
{
v___y_1301_ = v___y_1331_;
v___y_1302_ = v_acc_1272_;
goto v___jp_1300_;
}
}
}
}
}
}
}
}
v___jp_1274_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_unsigned_to_nat(1u);
v___x_1277_ = lean_nat_add(v_i_1273_, v___x_1276_);
lean_dec(v_i_1273_);
v_acc_1272_ = v___y_1275_;
v_i_1273_ = v___x_1277_;
goto _start;
}
v___jp_1279_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_unsigned_to_nat(1u);
v___x_1281_ = lean_nat_add(v_i_1273_, v___x_1280_);
lean_dec(v_i_1273_);
v_i_1273_ = v___x_1281_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2___boxed(lean_object* v_snd_1366_, lean_object* v_b_1367_, lean_object* v_acc_1368_, lean_object* v_i_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(v_snd_1366_, v_b_1367_, v_acc_1368_, v_i_1369_);
lean_dec_ref(v_b_1367_);
lean_dec_ref(v_snd_1366_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(lean_object* v_snd_1371_, lean_object* v_init_1372_, lean_object* v_b_1373_){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_unsigned_to_nat(0u);
v___x_1375_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(v_snd_1371_, v_b_1373_, v_init_1372_, v___x_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1___boxed(lean_object* v_snd_1376_, lean_object* v_init_1377_, lean_object* v_b_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(v_snd_1376_, v_init_1377_, v_b_1378_);
lean_dec_ref(v_b_1378_);
lean_dec_ref(v_snd_1376_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2_spec__4(lean_object* v_b_1380_, lean_object* v_acc_1381_, lean_object* v_i_1382_){
_start:
{
lean_object* v___y_1388_; lean_object* v_keyArray_1392_; lean_object* v_valueArray_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v_keyArray_1392_ = lean_ctor_get(v_b_1380_, 1);
v_valueArray_1393_ = lean_ctor_get(v_b_1380_, 2);
v___x_1394_ = lean_array_get_size(v_keyArray_1392_);
v___x_1395_ = lean_nat_dec_lt(v_i_1382_, v___x_1394_);
if (v___x_1395_ == 0)
{
lean_dec(v_i_1382_);
return v_acc_1381_;
}
else
{
lean_object* v___x_1396_; uint8_t v_isSome_1397_; 
v___x_1396_ = lean_array_fget_borrowed(v_keyArray_1392_, v_i_1382_);
v_isSome_1397_ = lean_noption_is_some(v___x_1396_);
if (v_isSome_1397_ == 0)
{
goto v___jp_1383_;
}
else
{
lean_object* v___x_1398_; uint8_t v_isSome_1399_; 
v___x_1398_ = lean_array_fget_borrowed(v_valueArray_1393_, v_i_1382_);
v_isSome_1399_ = lean_noption_is_some(v___x_1398_);
if (v_isSome_1399_ == 0)
{
goto v___jp_1383_;
}
else
{
lean_object* v_val_1400_; lean_object* v___x_1401_; 
lean_inc(v___x_1396_);
v_val_1400_ = lean_noption_get(v___x_1396_);
v___x_1401_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0___redArg(v_acc_1381_, v_val_1400_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_index_1402_; lean_object* v_value_1403_; lean_object* v_size_1404_; lean_object* v_val_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v_index_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_index_1402_);
v_value_1403_ = lean_ctor_get(v___x_1401_, 2);
lean_inc(v_value_1403_);
lean_dec_ref_known(v___x_1401_, 3);
v_size_1404_ = lean_ctor_get(v_acc_1381_, 0);
lean_inc(v_size_1404_);
lean_inc(v___x_1398_);
v_val_1405_ = lean_noption_get(v___x_1398_);
v___x_1406_ = lean_nat_sub(v_value_1403_, v_val_1405_);
lean_dec(v_val_1405_);
lean_dec(v_value_1403_);
v___x_1407_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1381_, v_size_1404_, v_index_1402_, v_val_1400_, v___x_1406_);
lean_dec(v_index_1402_);
v___y_1388_ = v___x_1407_;
goto v___jp_1387_;
}
else
{
lean_dec(v___x_1401_);
lean_dec(v_val_1400_);
v___y_1388_ = v_acc_1381_;
goto v___jp_1387_;
}
}
}
}
v___jp_1383_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_unsigned_to_nat(1u);
v___x_1385_ = lean_nat_add(v_i_1382_, v___x_1384_);
lean_dec(v_i_1382_);
v_i_1382_ = v___x_1385_;
goto _start;
}
v___jp_1387_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = lean_unsigned_to_nat(1u);
v___x_1390_ = lean_nat_add(v_i_1382_, v___x_1389_);
lean_dec(v_i_1382_);
v_acc_1381_ = v___y_1388_;
v_i_1382_ = v___x_1390_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2_spec__4___boxed(lean_object* v_b_1408_, lean_object* v_acc_1409_, lean_object* v_i_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2_spec__4(v_b_1408_, v_acc_1409_, v_i_1410_);
lean_dec_ref(v_b_1408_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(lean_object* v_init_1412_, lean_object* v_b_1413_){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_unsigned_to_nat(0u);
v___x_1415_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2_spec__4(v_b_1413_, v_init_1412_, v___x_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2___boxed(lean_object* v_init_1416_, lean_object* v_b_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_init_1416_, v_b_1417_);
lean_dec_ref(v_b_1417_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(lean_object* v_x_1419_, lean_object* v_y_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v___y_1424_; lean_object* v_fst_1425_; lean_object* v_snd_1426_; lean_object* v_size_1430_; lean_object* v_size_1431_; lean_object* v_fst_1433_; lean_object* v_snd_1434_; uint8_t v___x_1440_; 
v_size_1430_ = lean_ctor_get(v_y_1420_, 0);
lean_inc(v_size_1430_);
v_size_1431_ = lean_ctor_get(v_x_1419_, 0);
lean_inc(v_size_1431_);
v___x_1440_ = lean_nat_dec_lt(v_size_1430_, v_size_1431_);
if (v___x_1440_ == 0)
{
v_fst_1433_ = v_x_1419_;
v_snd_1434_ = v_y_1420_;
goto v___jp_1432_;
}
else
{
v_fst_1433_ = v_y_1420_;
v_snd_1434_ = v_x_1419_;
goto v___jp_1432_;
}
v___jp_1423_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1427_, 0, v___y_1424_);
lean_ctor_set(v___x_1427_, 1, v_fst_1425_);
lean_ctor_set(v___x_1427_, 2, v_snd_1426_);
v___x_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
lean_ctor_set(v___x_1428_, 1, v_a_1421_);
v___x_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
return v___x_1429_;
}
v___jp_1432_:
{
lean_object* v___x_1435_; lean_object* v_common_1436_; lean_object* v_x_1437_; lean_object* v_y_1438_; uint8_t v___x_1439_; 
v___x_1435_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__2);
v_common_1436_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(v_snd_1434_, v___x_1435_, v_fst_1433_);
v_x_1437_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_fst_1433_, v_common_1436_);
v_y_1438_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_snd_1434_, v_common_1436_);
v___x_1439_ = lean_nat_dec_lt(v_size_1430_, v_size_1431_);
lean_dec(v_size_1431_);
lean_dec(v_size_1430_);
if (v___x_1439_ == 0)
{
v___y_1424_ = v_common_1436_;
v_fst_1425_ = v_x_1437_;
v_snd_1426_ = v_y_1438_;
goto v___jp_1423_;
}
else
{
v___y_1424_ = v_common_1436_;
v_fst_1425_ = v_y_1438_;
v_snd_1426_ = v_x_1437_;
goto v___jp_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg___boxed(lean_object* v_x_1441_, lean_object* v_y_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1441_, v_y_1442_, v_a_1443_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(lean_object* v_x_1446_, lean_object* v_y_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1446_, v_y_1447_, v_a_1448_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___boxed(lean_object* v_x_1457_, lean_object* v_y_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(v_x_1457_, v_y_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1460_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(lean_object* v_00_u03b2_1468_, lean_object* v_m_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0___redArg(v_m_1469_, v_a_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0___boxed(lean_object* v_00_u03b2_1472_, lean_object* v_m_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_00_u03b2_1472_, v_m_1473_, v_a_1474_);
lean_dec(v_a_1474_);
lean_dec_ref(v_m_1473_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(lean_object* v_00_u03b2_1476_, lean_object* v_m_1477_, lean_object* v_query_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0___redArg(v_m_1477_, v_query_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1480_, lean_object* v_m_1481_, lean_object* v_query_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_00_u03b2_1480_, v_m_1481_, v_query_1482_);
lean_dec(v_query_1482_);
lean_dec_ref(v_m_1481_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(lean_object* v_b_1484_, lean_object* v_acc_1485_, lean_object* v_i_1486_){
_start:
{
lean_object* v_keyArray_1491_; lean_object* v_valueArray_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; 
v_keyArray_1491_ = lean_ctor_get(v_b_1484_, 1);
v_valueArray_1492_ = lean_ctor_get(v_b_1484_, 2);
v___x_1493_ = lean_array_get_size(v_keyArray_1491_);
v___x_1494_ = lean_nat_dec_lt(v_i_1486_, v___x_1493_);
if (v___x_1494_ == 0)
{
lean_dec(v_i_1486_);
return v_acc_1485_;
}
else
{
lean_object* v___x_1495_; uint8_t v_isSome_1496_; 
v___x_1495_ = lean_array_fget_borrowed(v_keyArray_1491_, v_i_1486_);
v_isSome_1496_ = lean_noption_is_some(v___x_1495_);
if (v_isSome_1496_ == 0)
{
goto v___jp_1487_;
}
else
{
lean_object* v___x_1497_; uint8_t v_isSome_1498_; 
v___x_1497_ = lean_array_fget_borrowed(v_valueArray_1492_, v_i_1486_);
v_isSome_1498_ = lean_noption_is_some(v___x_1497_);
if (v_isSome_1498_ == 0)
{
goto v___jp_1487_;
}
else
{
lean_object* v_val_1499_; lean_object* v_val_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_inc(v___x_1495_);
v_val_1499_ = lean_noption_get(v___x_1495_);
lean_inc(v___x_1497_);
v_val_1500_ = lean_noption_get(v___x_1497_);
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v_val_1499_);
lean_ctor_set(v___x_1501_, 1, v_val_1500_);
v___x_1502_ = lean_array_push(v_acc_1485_, v___x_1501_);
v___x_1503_ = lean_unsigned_to_nat(1u);
v___x_1504_ = lean_nat_add(v_i_1486_, v___x_1503_);
lean_dec(v_i_1486_);
v_acc_1485_ = v___x_1502_;
v_i_1486_ = v___x_1504_;
goto _start;
}
}
}
v___jp_1487_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_unsigned_to_nat(1u);
v___x_1489_ = lean_nat_add(v_i_1486_, v___x_1488_);
lean_dec(v_i_1486_);
v_i_1486_ = v___x_1489_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___boxed(lean_object* v_b_1506_, lean_object* v_acc_1507_, lean_object* v_i_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(v_b_1506_, v_acc_1507_, v_i_1508_);
lean_dec_ref(v_b_1506_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(lean_object* v_init_1510_, lean_object* v_b_1511_){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(v_b_1511_, v_init_1510_, v___x_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___boxed(lean_object* v_init_1514_, lean_object* v_b_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(v_init_1514_, v_b_1515_);
lean_dec_ref(v_b_1515_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(lean_object* v_upperBound_1517_, lean_object* v___x_1518_, lean_object* v_op_1519_, lean_object* v_a_1520_, lean_object* v_b_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v___y_1525_; uint8_t v___x_1529_; 
v___x_1529_ = lean_nat_dec_lt(v_a_1520_, v_upperBound_1517_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_dec(v_a_1520_);
lean_dec_ref(v_op_1519_);
lean_dec_ref(v___x_1518_);
v___x_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1530_, 0, v_b_1521_);
lean_ctor_set(v___x_1530_, 1, v___y_1522_);
v___x_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
return v___x_1531_;
}
else
{
if (lean_obj_tag(v_b_1521_) == 0)
{
lean_object* v___x_1532_; 
lean_inc_ref(v___x_1518_);
v___x_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1518_);
v___y_1525_ = v___x_1532_;
goto v___jp_1524_;
}
else
{
lean_object* v_val_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1542_; 
v_val_1533_ = lean_ctor_get(v_b_1521_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_b_1521_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1535_ = v_b_1521_;
v_isShared_1536_ = v_isSharedCheck_1542_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_val_1533_);
lean_dec(v_b_1521_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1542_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1540_; 
lean_inc_ref(v_op_1519_);
v___x_1537_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_1519_);
lean_inc_ref(v___x_1518_);
v___x_1538_ = l_Lean_mkAppB(v___x_1537_, v_val_1533_, v___x_1518_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v___x_1538_);
v___x_1540_ = v___x_1535_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
v___y_1525_ = v___x_1540_;
goto v___jp_1524_;
}
}
}
}
v___jp_1524_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = lean_unsigned_to_nat(1u);
v___x_1527_ = lean_nat_add(v_a_1520_, v___x_1526_);
lean_dec(v_a_1520_);
v_a_1520_ = v___x_1527_;
v_b_1521_ = v___y_1525_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg___boxed(lean_object* v_upperBound_1543_, lean_object* v___x_1544_, lean_object* v_op_1545_, lean_object* v_a_1546_, lean_object* v_b_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1543_, v___x_1544_, v_op_1545_, v_a_1546_, v_b_1547_, v___y_1548_);
lean_dec(v_upperBound_1543_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(lean_object* v_op_1551_, lean_object* v_as_1552_, size_t v_sz_1553_, size_t v_i_1554_, lean_object* v_b_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
uint8_t v___x_1564_; 
v___x_1564_ = lean_usize_dec_lt(v_i_1554_, v_sz_1553_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_dec_ref(v_op_1551_);
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v_b_1555_);
lean_ctor_set(v___x_1565_, 1, v___y_1556_);
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
return v___x_1566_;
}
else
{
lean_object* v_a_1567_; lean_object* v_fst_1568_; lean_object* v_snd_1569_; lean_object* v_varToExpr_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_a_1567_ = lean_array_uget_borrowed(v_as_1552_, v_i_1554_);
v_fst_1568_ = lean_ctor_get(v_a_1567_, 0);
v_snd_1569_ = lean_ctor_get(v_a_1567_, 1);
v_varToExpr_1570_ = lean_ctor_get(v___y_1556_, 2);
v___x_1571_ = l_Lean_instInhabitedExpr;
v___x_1572_ = lean_unsigned_to_nat(0u);
v___x_1573_ = lean_array_get(v___x_1571_, v_varToExpr_1570_, v_fst_1568_);
lean_inc_ref(v_op_1551_);
v___x_1574_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_snd_1569_, v___x_1573_, v_op_1551_, v___x_1572_, v_b_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v_fst_1576_; lean_object* v_snd_1577_; size_t v___x_1578_; size_t v___x_1579_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref_known(v___x_1574_, 1);
v_fst_1576_ = lean_ctor_get(v_a_1575_, 0);
lean_inc(v_fst_1576_);
v_snd_1577_ = lean_ctor_get(v_a_1575_, 1);
lean_inc(v_snd_1577_);
lean_dec(v_a_1575_);
v___x_1578_ = ((size_t)1ULL);
v___x_1579_ = lean_usize_add(v_i_1554_, v___x_1578_);
v_i_1554_ = v___x_1579_;
v_b_1555_ = v_fst_1576_;
v___y_1556_ = v_snd_1577_;
goto _start;
}
else
{
lean_dec_ref(v_op_1551_);
return v___x_1574_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1___boxed(lean_object* v_op_1581_, lean_object* v_as_1582_, lean_object* v_sz_1583_, lean_object* v_i_1584_, lean_object* v_b_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
size_t v_sz_boxed_1594_; size_t v_i_boxed_1595_; lean_object* v_res_1596_; 
v_sz_boxed_1594_ = lean_unbox_usize(v_sz_1583_);
lean_dec(v_sz_1583_);
v_i_boxed_1595_ = lean_unbox_usize(v_i_1584_);
lean_dec(v_i_1584_);
v_res_1596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1581_, v_as_1582_, v_sz_boxed_1594_, v_i_boxed_1595_, v_b_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec_ref(v_as_1582_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3_spec__4___redArg(lean_object* v_hi_1597_, lean_object* v_pivot_1598_, lean_object* v_as_1599_, lean_object* v_i_1600_, lean_object* v_k_1601_){
_start:
{
uint8_t v___x_1602_; 
v___x_1602_ = lean_nat_dec_lt(v_k_1601_, v_hi_1597_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec(v_k_1601_);
v___x_1603_ = lean_array_fswap(v_as_1599_, v_i_1600_, v_hi_1597_);
v___x_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1604_, 0, v_i_1600_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
return v___x_1604_;
}
else
{
lean_object* v___x_1605_; lean_object* v_fst_1606_; lean_object* v_fst_1607_; uint8_t v___x_1608_; 
v___x_1605_ = lean_array_fget_borrowed(v_as_1599_, v_k_1601_);
v_fst_1606_ = lean_ctor_get(v___x_1605_, 0);
v_fst_1607_ = lean_ctor_get(v_pivot_1598_, 0);
v___x_1608_ = lean_nat_dec_lt(v_fst_1606_, v_fst_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_unsigned_to_nat(1u);
v___x_1610_ = lean_nat_add(v_k_1601_, v___x_1609_);
lean_dec(v_k_1601_);
v_k_1601_ = v___x_1610_;
goto _start;
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1612_ = lean_array_fswap(v_as_1599_, v_i_1600_, v_k_1601_);
v___x_1613_ = lean_unsigned_to_nat(1u);
v___x_1614_ = lean_nat_add(v_i_1600_, v___x_1613_);
lean_dec(v_i_1600_);
v___x_1615_ = lean_nat_add(v_k_1601_, v___x_1613_);
lean_dec(v_k_1601_);
v_as_1599_ = v___x_1612_;
v_i_1600_ = v___x_1614_;
v_k_1601_ = v___x_1615_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1617_, lean_object* v_pivot_1618_, lean_object* v_as_1619_, lean_object* v_i_1620_, lean_object* v_k_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3_spec__4___redArg(v_hi_1617_, v_pivot_1618_, v_as_1619_, v_i_1620_, v_k_1621_);
lean_dec_ref(v_pivot_1618_);
lean_dec(v_hi_1617_);
return v_res_1622_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___redArg___lam__0(lean_object* v_x1_1623_, lean_object* v_x2_1624_){
_start:
{
lean_object* v_fst_1625_; lean_object* v_fst_1626_; uint8_t v___x_1627_; 
v_fst_1625_ = lean_ctor_get(v_x1_1623_, 0);
v_fst_1626_ = lean_ctor_get(v_x2_1624_, 0);
v___x_1627_ = lean_nat_dec_lt(v_fst_1625_, v_fst_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___redArg___lam__0___boxed(lean_object* v_x1_1628_, lean_object* v_x2_1629_){
_start:
{
uint8_t v_res_1630_; lean_object* v_r_1631_; 
v_res_1630_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___redArg___lam__0(v_x1_1628_, v_x2_1629_);
lean_dec_ref(v_x2_1629_);
lean_dec_ref(v_x1_1628_);
v_r_1631_ = lean_box(v_res_1630_);
return v_r_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___redArg(lean_object* v_n_1632_, lean_object* v_as_1633_, lean_object* v_lo_1634_, lean_object* v_hi_1635_){
_start:
{
lean_object* v___y_1637_; uint8_t v___x_1647_; 
v___x_1647_ = lean_nat_dec_lt(v_lo_1634_, v_hi_1635_);
if (v___x_1647_ == 0)
{
lean_dec(v_lo_1634_);
return v_as_1633_;
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v_mid_1650_; lean_object* v___y_1652_; lean_object* v___y_1658_; lean_object* v___x_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___x_1648_ = lean_nat_add(v_lo_1634_, v_hi_1635_);
v___x_1649_ = lean_unsigned_to_nat(1u);
v_mid_1650_ = lean_nat_shiftr(v___x_1648_, v___x_1649_);
lean_dec(v___x_1648_);
v___x_1663_ = lean_array_fget_borrowed(v_as_1633_, v_mid_1650_);
v___x_1664_ = lean_array_fget_borrowed(v_as_1633_, v_lo_1634_);
v___x_1665_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___redArg___lam__0(v___x_1663_, v___x_1664_);
if (v___x_1665_ == 0)
{
v___y_1658_ = v_as_1633_;
goto v___jp_1657_;
}
else
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_array_fswap(v_as_1633_, v_lo_1634_, v_mid_1650_);
v___y_1658_ = v___x_1666_;
goto v___jp_1657_;
}
v___jp_1651_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1653_ = lean_array_fget_borrowed(v___y_1652_, v_mid_1650_);
v___x_1654_ = lean_array_fget_borrowed(v___y_1652_, v_hi_1635_);
v___x_1655_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___redArg___lam__0(v___x_1653_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_dec(v_mid_1650_);
v___y_1637_ = v___y_1652_;
goto v___jp_1636_;
}
else
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_array_fswap(v___y_1652_, v_mid_1650_, v_hi_1635_);
lean_dec(v_mid_1650_);
v___y_1637_ = v___x_1656_;
goto v___jp_1636_;
}
}
v___jp_1657_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
v___x_1659_ = lean_array_fget_borrowed(v___y_1658_, v_hi_1635_);
v___x_1660_ = lean_array_fget_borrowed(v___y_1658_, v_lo_1634_);
v___x_1661_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___redArg___lam__0(v___x_1659_, v___x_1660_);
if (v___x_1661_ == 0)
{
v___y_1652_ = v___y_1658_;
goto v___jp_1651_;
}
else
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_array_fswap(v___y_1658_, v_lo_1634_, v_hi_1635_);
v___y_1652_ = v___x_1662_;
goto v___jp_1651_;
}
}
}
v___jp_1636_:
{
lean_object* v_pivot_1638_; lean_object* v___x_1639_; lean_object* v_fst_1640_; lean_object* v_snd_1641_; uint8_t v___x_1642_; 
v_pivot_1638_ = lean_array_fget(v___y_1637_, v_hi_1635_);
lean_inc_n(v_lo_1634_, 2);
v___x_1639_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3_spec__4___redArg(v_hi_1635_, v_pivot_1638_, v___y_1637_, v_lo_1634_, v_lo_1634_);
lean_dec(v_pivot_1638_);
v_fst_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_fst_1640_);
v_snd_1641_ = lean_ctor_get(v___x_1639_, 1);
lean_inc(v_snd_1641_);
lean_dec_ref(v___x_1639_);
v___x_1642_ = lean_nat_dec_le(v_hi_1635_, v_fst_1640_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1643_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___redArg(v_n_1632_, v_snd_1641_, v_lo_1634_, v_fst_1640_);
v___x_1644_ = lean_unsigned_to_nat(1u);
v___x_1645_ = lean_nat_add(v_fst_1640_, v___x_1644_);
lean_dec(v_fst_1640_);
v_as_1633_ = v___x_1643_;
v_lo_1634_ = v___x_1645_;
goto _start;
}
else
{
lean_dec(v_fst_1640_);
lean_dec(v_lo_1634_);
return v_snd_1641_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___redArg___boxed(lean_object* v_n_1667_, lean_object* v_as_1668_, lean_object* v_lo_1669_, lean_object* v_hi_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___redArg(v_n_1667_, v_as_1668_, v_lo_1669_, v_hi_1670_);
lean_dec(v_hi_1670_);
lean_dec(v_n_1667_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(lean_object* v_coeff_1672_, lean_object* v_op_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v___y_1683_; lean_object* v_size_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v_size_1688_ = lean_ctor_get(v_coeff_1672_, 0);
v___x_1689_ = lean_mk_empty_array_with_capacity(v_size_1688_);
v___x_1690_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(v___x_1689_, v_coeff_1672_);
v___x_1691_ = lean_array_get_size(v___x_1690_);
v___x_1696_ = lean_unsigned_to_nat(0u);
v___x_1697_ = lean_nat_dec_eq(v___x_1691_, v___x_1696_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___y_1701_; uint8_t v___x_1703_; 
v___x_1698_ = lean_unsigned_to_nat(1u);
v___x_1699_ = lean_nat_sub(v___x_1691_, v___x_1698_);
v___x_1703_ = lean_nat_dec_le(v___x_1696_, v___x_1699_);
if (v___x_1703_ == 0)
{
lean_inc(v___x_1699_);
v___y_1701_ = v___x_1699_;
goto v___jp_1700_;
}
else
{
v___y_1701_ = v___x_1696_;
goto v___jp_1700_;
}
v___jp_1700_:
{
uint8_t v___x_1702_; 
v___x_1702_ = lean_nat_dec_le(v___y_1701_, v___x_1699_);
if (v___x_1702_ == 0)
{
lean_dec(v___x_1699_);
lean_inc(v___y_1701_);
v___y_1693_ = v___y_1701_;
v___y_1694_ = v___y_1701_;
goto v___jp_1692_;
}
else
{
v___y_1693_ = v___y_1701_;
v___y_1694_ = v___x_1699_;
goto v___jp_1692_;
}
}
}
else
{
v___y_1683_ = v___x_1690_;
goto v___jp_1682_;
}
v___jp_1682_:
{
lean_object* v_acc_1684_; size_t v_sz_1685_; size_t v___x_1686_; lean_object* v___x_1687_; 
v_acc_1684_ = lean_box(0);
v_sz_1685_ = lean_array_size(v___y_1683_);
v___x_1686_ = ((size_t)0ULL);
v___x_1687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1673_, v___y_1683_, v_sz_1685_, v___x_1686_, v_acc_1684_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_);
lean_dec_ref(v___y_1683_);
return v___x_1687_;
}
v___jp_1692_:
{
lean_object* v___x_1695_; 
v___x_1695_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___redArg(v___x_1691_, v___x_1690_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
v___y_1683_ = v___x_1695_;
goto v___jp_1682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr___boxed(lean_object* v_coeff_1704_, lean_object* v_op_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_coeff_1704_, v_op_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
lean_dec_ref(v_coeff_1704_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(lean_object* v_upperBound_1715_, lean_object* v___x_1716_, lean_object* v_op_1717_, lean_object* v_inst_1718_, lean_object* v_R_1719_, lean_object* v_a_1720_, lean_object* v_b_1721_, lean_object* v_c_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1715_, v___x_1716_, v_op_1717_, v_a_1720_, v_b_1721_, v___y_1723_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___boxed(lean_object* v_upperBound_1732_, lean_object* v___x_1733_, lean_object* v_op_1734_, lean_object* v_inst_1735_, lean_object* v_R_1736_, lean_object* v_a_1737_, lean_object* v_b_1738_, lean_object* v_c_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(v_upperBound_1732_, v___x_1733_, v_op_1734_, v_inst_1735_, v_R_1736_, v_a_1737_, v_b_1738_, v_c_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v_upperBound_1732_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(lean_object* v_n_1749_, lean_object* v_as_1750_, lean_object* v_lo_1751_, lean_object* v_hi_1752_, lean_object* v_w_1753_, lean_object* v_hlo_1754_, lean_object* v_hhi_1755_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___redArg(v_n_1749_, v_as_1750_, v_lo_1751_, v_hi_1752_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___boxed(lean_object* v_n_1757_, lean_object* v_as_1758_, lean_object* v_lo_1759_, lean_object* v_hi_1760_, lean_object* v_w_1761_, lean_object* v_hlo_1762_, lean_object* v_hhi_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(v_n_1757_, v_as_1758_, v_lo_1759_, v_hi_1760_, v_w_1761_, v_hlo_1762_, v_hhi_1763_);
lean_dec(v_hi_1760_);
lean_dec(v_n_1757_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3_spec__4(lean_object* v_n_1765_, lean_object* v_lo_1766_, lean_object* v_hi_1767_, lean_object* v_hhi_1768_, lean_object* v_pivot_1769_, lean_object* v_as_1770_, lean_object* v_i_1771_, lean_object* v_k_1772_, lean_object* v_ilo_1773_, lean_object* v_ik_1774_, lean_object* v_w_1775_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3_spec__4___redArg(v_hi_1767_, v_pivot_1769_, v_as_1770_, v_i_1771_, v_k_1772_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3_spec__4___boxed(lean_object* v_n_1777_, lean_object* v_lo_1778_, lean_object* v_hi_1779_, lean_object* v_hhi_1780_, lean_object* v_pivot_1781_, lean_object* v_as_1782_, lean_object* v_i_1783_, lean_object* v_k_1784_, lean_object* v_ilo_1785_, lean_object* v_ik_1786_, lean_object* v_w_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3_spec__4(v_n_1777_, v_lo_1778_, v_hi_1779_, v_hhi_1780_, v_pivot_1781_, v_as_1782_, v_i_1783_, v_k_1784_, v_ilo_1785_, v_ik_1786_, v_w_1787_);
lean_dec_ref(v_pivot_1781_);
lean_dec(v_hi_1779_);
lean_dec(v_lo_1778_);
lean_dec(v_n_1777_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(lean_object* v_e_1789_, lean_object* v___y_1790_){
_start:
{
uint8_t v___x_1792_; 
v___x_1792_ = l_Lean_Expr_hasMVar(v_e_1789_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; 
v___x_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1793_, 0, v_e_1789_);
return v___x_1793_;
}
else
{
lean_object* v___x_1794_; lean_object* v_mctx_1795_; lean_object* v___x_1796_; lean_object* v_fst_1797_; lean_object* v_snd_1798_; lean_object* v___x_1799_; lean_object* v_cache_1800_; lean_object* v_zetaDeltaFVarIds_1801_; lean_object* v_postponed_1802_; lean_object* v_diag_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1812_; 
v___x_1794_ = lean_st_ref_get(v___y_1790_);
v_mctx_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc_ref(v_mctx_1795_);
lean_dec(v___x_1794_);
v___x_1796_ = l_Lean_instantiateMVarsCore(v_mctx_1795_, v_e_1789_);
v_fst_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_fst_1797_);
v_snd_1798_ = lean_ctor_get(v___x_1796_, 1);
lean_inc(v_snd_1798_);
lean_dec_ref(v___x_1796_);
v___x_1799_ = lean_st_ref_take(v___y_1790_);
v_cache_1800_ = lean_ctor_get(v___x_1799_, 1);
v_zetaDeltaFVarIds_1801_ = lean_ctor_get(v___x_1799_, 2);
v_postponed_1802_ = lean_ctor_get(v___x_1799_, 3);
v_diag_1803_ = lean_ctor_get(v___x_1799_, 4);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1812_ == 0)
{
lean_object* v_unused_1813_; 
v_unused_1813_ = lean_ctor_get(v___x_1799_, 0);
lean_dec(v_unused_1813_);
v___x_1805_ = v___x_1799_;
v_isShared_1806_ = v_isSharedCheck_1812_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_diag_1803_);
lean_inc(v_postponed_1802_);
lean_inc(v_zetaDeltaFVarIds_1801_);
lean_inc(v_cache_1800_);
lean_dec(v___x_1799_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1812_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v_snd_1798_);
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_snd_1798_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_cache_1800_);
lean_ctor_set(v_reuseFailAlloc_1811_, 2, v_zetaDeltaFVarIds_1801_);
lean_ctor_set(v_reuseFailAlloc_1811_, 3, v_postponed_1802_);
lean_ctor_set(v_reuseFailAlloc_1811_, 4, v_diag_1803_);
v___x_1808_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = lean_st_ref_put(v___y_1790_, v___x_1808_);
v___x_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1810_, 0, v_fst_1797_);
return v___x_1810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg___boxed(lean_object* v_e_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1814_, v___y_1815_);
lean_dec(v___y_1815_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(lean_object* v_e_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1818_, v___y_1820_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___boxed(lean_object* v_e_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(v_e_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(lean_object* v_x_1832_, lean_object* v_y_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Lean_Meta_mkEq(v_x_1832_, v_y_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1862_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1862_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1862_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
lean_ctor_set_tag(v___x_1842_, 1);
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
uint8_t v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = 0;
v___x_1847_ = lean_box(0);
v___x_1848_ = l_Lean_Meta_mkFreshExprMVar(v___x_1845_, v___x_1846_, v___x_1847_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref_known(v___x_1848_, 1);
v___x_1850_ = l_Lean_Expr_mvarId_x21(v_a_1849_);
v___x_1851_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v___x_1850_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v___x_1852_; 
lean_dec_ref_known(v___x_1851_, 1);
v___x_1852_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_a_1849_, v_a_1835_);
return v___x_1852_;
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec(v_a_1849_);
v_a_1853_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1851_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1851_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
else
{
return v___x_1848_;
}
}
}
}
else
{
return v___x_1839_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC___boxed(lean_object* v_x_1863_, lean_object* v_y_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v_x_1863_, v_y_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
lean_dec(v_a_1868_);
lean_dec_ref(v_a_1867_);
lean_dec(v_a_1866_);
lean_dec_ref(v_a_1865_);
return v_res_1870_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1871_ = lean_unsigned_to_nat(32u);
v___x_1872_ = lean_mk_empty_array_with_capacity(v___x_1871_);
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
return v___x_1873_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1874_ = ((size_t)5ULL);
v___x_1875_ = lean_unsigned_to_nat(0u);
v___x_1876_ = lean_unsigned_to_nat(32u);
v___x_1877_ = lean_mk_empty_array_with_capacity(v___x_1876_);
v___x_1878_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0);
v___x_1879_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
lean_ctor_set(v___x_1879_, 1, v___x_1877_);
lean_ctor_set(v___x_1879_, 2, v___x_1875_);
lean_ctor_set(v___x_1879_, 3, v___x_1875_);
lean_ctor_set_usize(v___x_1879_, 4, v___x_1874_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(lean_object* v___y_1880_){
_start:
{
lean_object* v___x_1882_; lean_object* v_traceState_1883_; lean_object* v_traces_1884_; lean_object* v___x_1885_; lean_object* v_traceState_1886_; lean_object* v_env_1887_; lean_object* v_nextMacroScope_1888_; lean_object* v_ngen_1889_; lean_object* v_auxDeclNGen_1890_; lean_object* v_cache_1891_; lean_object* v_messages_1892_; lean_object* v_infoState_1893_; lean_object* v_snapshotTasks_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1913_; 
v___x_1882_ = lean_st_ref_get(v___y_1880_);
v_traceState_1883_ = lean_ctor_get(v___x_1882_, 4);
lean_inc_ref(v_traceState_1883_);
lean_dec(v___x_1882_);
v_traces_1884_ = lean_ctor_get(v_traceState_1883_, 0);
lean_inc_ref(v_traces_1884_);
lean_dec_ref(v_traceState_1883_);
v___x_1885_ = lean_st_ref_take(v___y_1880_);
v_traceState_1886_ = lean_ctor_get(v___x_1885_, 4);
v_env_1887_ = lean_ctor_get(v___x_1885_, 0);
v_nextMacroScope_1888_ = lean_ctor_get(v___x_1885_, 1);
v_ngen_1889_ = lean_ctor_get(v___x_1885_, 2);
v_auxDeclNGen_1890_ = lean_ctor_get(v___x_1885_, 3);
v_cache_1891_ = lean_ctor_get(v___x_1885_, 5);
v_messages_1892_ = lean_ctor_get(v___x_1885_, 6);
v_infoState_1893_ = lean_ctor_get(v___x_1885_, 7);
v_snapshotTasks_1894_ = lean_ctor_get(v___x_1885_, 8);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1896_ = v___x_1885_;
v_isShared_1897_ = v_isSharedCheck_1913_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_snapshotTasks_1894_);
lean_inc(v_infoState_1893_);
lean_inc(v_messages_1892_);
lean_inc(v_cache_1891_);
lean_inc(v_traceState_1886_);
lean_inc(v_auxDeclNGen_1890_);
lean_inc(v_ngen_1889_);
lean_inc(v_nextMacroScope_1888_);
lean_inc(v_env_1887_);
lean_dec(v___x_1885_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1913_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
uint64_t v_tid_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1911_; 
v_tid_1898_ = lean_ctor_get_uint64(v_traceState_1886_, sizeof(void*)*1);
v_isSharedCheck_1911_ = !lean_is_exclusive(v_traceState_1886_);
if (v_isSharedCheck_1911_ == 0)
{
lean_object* v_unused_1912_; 
v_unused_1912_ = lean_ctor_get(v_traceState_1886_, 0);
lean_dec(v_unused_1912_);
v___x_1900_ = v_traceState_1886_;
v_isShared_1901_ = v_isSharedCheck_1911_;
goto v_resetjp_1899_;
}
else
{
lean_dec(v_traceState_1886_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1911_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1902_; lean_object* v___x_1904_; 
v___x_1902_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 0, v___x_1902_);
v___x_1904_ = v___x_1900_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1902_);
lean_ctor_set_uint64(v_reuseFailAlloc_1910_, sizeof(void*)*1, v_tid_1898_);
v___x_1904_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
lean_object* v___x_1906_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 4, v___x_1904_);
v___x_1906_ = v___x_1896_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_env_1887_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v_nextMacroScope_1888_);
lean_ctor_set(v_reuseFailAlloc_1909_, 2, v_ngen_1889_);
lean_ctor_set(v_reuseFailAlloc_1909_, 3, v_auxDeclNGen_1890_);
lean_ctor_set(v_reuseFailAlloc_1909_, 4, v___x_1904_);
lean_ctor_set(v_reuseFailAlloc_1909_, 5, v_cache_1891_);
lean_ctor_set(v_reuseFailAlloc_1909_, 6, v_messages_1892_);
lean_ctor_set(v_reuseFailAlloc_1909_, 7, v_infoState_1893_);
lean_ctor_set(v_reuseFailAlloc_1909_, 8, v_snapshotTasks_1894_);
v___x_1906_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_st_ref_put(v___y_1880_, v___x_1906_);
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v_traces_1884_);
return v___x_1908_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___boxed(lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1914_);
lean_dec(v___y_1914_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1925_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
return v_res_1938_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(lean_object* v_opts_1939_, lean_object* v_opt_1940_){
_start:
{
lean_object* v_name_1941_; lean_object* v_defValue_1942_; lean_object* v_map_1943_; lean_object* v___x_1944_; 
v_name_1941_ = lean_ctor_get(v_opt_1940_, 0);
v_defValue_1942_ = lean_ctor_get(v_opt_1940_, 1);
v_map_1943_ = lean_ctor_get(v_opts_1939_, 0);
v___x_1944_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1943_, v_name_1941_);
if (lean_obj_tag(v___x_1944_) == 0)
{
uint8_t v___x_1945_; 
v___x_1945_ = lean_unbox(v_defValue_1942_);
return v___x_1945_;
}
else
{
lean_object* v_val_1946_; 
v_val_1946_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_val_1946_);
lean_dec_ref_known(v___x_1944_, 1);
if (lean_obj_tag(v_val_1946_) == 1)
{
uint8_t v_v_1947_; 
v_v_1947_ = lean_ctor_get_uint8(v_val_1946_, 0);
lean_dec_ref_known(v_val_1946_, 0);
return v_v_1947_;
}
else
{
uint8_t v___x_1948_; 
lean_dec(v_val_1946_);
v___x_1948_ = lean_unbox(v_defValue_1942_);
return v___x_1948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object* v_opts_1949_, lean_object* v_opt_1950_){
_start:
{
uint8_t v_res_1951_; lean_object* v_r_1952_; 
v_res_1951_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_1949_, v_opt_1950_);
lean_dec_ref(v_opt_1950_);
lean_dec_ref(v_opts_1949_);
v_r_1952_ = lean_box(v_res_1951_);
return v_r_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(lean_object* v_cls_1953_, lean_object* v_____do__lift_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_options_1965_; uint8_t v_hasTrace_1966_; 
v_options_1965_ = lean_ctor_get(v___y_1962_, 2);
v_hasTrace_1966_ = lean_ctor_get_uint8(v_options_1965_, sizeof(void*)*1);
if (v_hasTrace_1966_ == 0)
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
lean_dec(v_cls_1953_);
v___x_1967_ = lean_box(v_hasTrace_1966_);
v___x_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
return v___x_1968_;
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1969_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_1970_ = l_Lean_Name_append(v___x_1969_, v_cls_1953_);
v___x_1971_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_1954_, v_options_1965_, v___x_1970_);
lean_dec(v___x_1970_);
v___x_1972_ = lean_box(v___x_1971_);
v___x_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1972_);
return v___x_1973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0___boxed(lean_object* v_cls_1974_, lean_object* v_____do__lift_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_1974_, v_____do__lift_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v_____do__lift_1975_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1(lean_object* v___x_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = l_Lean_mkAppB(v___x_1987_, v___y_1988_, v___y_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(lean_object* v_val_1991_, lean_object* v_lhs_1992_, lean_object* v_rhs_1993_, lean_object* v_P_1994_, uint8_t v___x_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___x_2004_; 
lean_inc_ref(v_lhs_1992_);
lean_inc_ref(v_val_1991_);
v___x_2004_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1991_, v_lhs_1992_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v_fst_2006_; lean_object* v_snd_2007_; lean_object* v___x_2008_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_2004_, 1);
v_fst_2006_ = lean_ctor_get(v_a_2005_, 0);
lean_inc(v_fst_2006_);
v_snd_2007_ = lean_ctor_get(v_a_2005_, 1);
lean_inc(v_snd_2007_);
lean_dec(v_a_2005_);
lean_inc_ref(v_rhs_1993_);
lean_inc_ref(v_val_1991_);
v___x_2008_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1991_, v_rhs_1993_, v_snd_2007_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v_fst_2010_; lean_object* v_snd_2011_; lean_object* v___x_2012_; lean_object* v_a_2013_; lean_object* v_fst_2014_; lean_object* v_snd_2015_; lean_object* v_common_2016_; lean_object* v_x_2017_; lean_object* v_y_2018_; lean_object* v___x_2019_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref_known(v___x_2008_, 1);
v_fst_2010_ = lean_ctor_get(v_a_2009_, 0);
lean_inc(v_fst_2010_);
v_snd_2011_ = lean_ctor_get(v_a_2009_, 1);
lean_inc(v_snd_2011_);
lean_dec(v_a_2009_);
v___x_2012_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_2006_, v_fst_2010_, v_snd_2011_);
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref(v___x_2012_);
v_fst_2014_ = lean_ctor_get(v_a_2013_, 0);
lean_inc(v_fst_2014_);
v_snd_2015_ = lean_ctor_get(v_a_2013_, 1);
lean_inc(v_snd_2015_);
lean_dec(v_a_2013_);
v_common_2016_ = lean_ctor_get(v_fst_2014_, 0);
lean_inc_ref(v_common_2016_);
v_x_2017_ = lean_ctor_get(v_fst_2014_, 1);
lean_inc_ref(v_x_2017_);
v_y_2018_ = lean_ctor_get(v_fst_2014_, 2);
lean_inc_ref(v_y_2018_);
lean_dec(v_fst_2014_);
lean_inc_ref(v_val_1991_);
v___x_2019_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_2016_, v_val_1991_, v_snd_2015_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec_ref(v_common_2016_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v_fst_2021_; lean_object* v_snd_2022_; lean_object* v___x_2023_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2019_, 1);
v_fst_2021_ = lean_ctor_get(v_a_2020_, 0);
lean_inc(v_fst_2021_);
v_snd_2022_ = lean_ctor_get(v_a_2020_, 1);
lean_inc(v_snd_2022_);
lean_dec(v_a_2020_);
lean_inc_ref(v_val_1991_);
v___x_2023_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_2017_, v_val_1991_, v_snd_2022_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec_ref(v_x_2017_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v_fst_2025_; lean_object* v_snd_2026_; lean_object* v___x_2027_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
v_fst_2025_ = lean_ctor_get(v_a_2024_, 0);
lean_inc(v_fst_2025_);
v_snd_2026_ = lean_ctor_get(v_a_2024_, 1);
lean_inc(v_snd_2026_);
lean_dec(v_a_2024_);
lean_inc_ref(v_val_1991_);
v___x_2027_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_2018_, v_val_1991_, v_snd_2026_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec_ref(v_y_2018_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2092_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2092_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2092_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v_fst_2032_; lean_object* v_snd_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2091_; 
v_fst_2032_ = lean_ctor_get(v_a_2028_, 0);
v_snd_2033_ = lean_ctor_get(v_a_2028_, 1);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_a_2028_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2035_ = v_a_2028_;
v_isShared_2036_ = v_isSharedCheck_2091_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_snd_2033_);
lean_inc(v_fst_2032_);
lean_dec(v_a_2028_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2091_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___x_2081_; lean_object* v___f_2082_; lean_object* v___y_2084_; lean_object* v___x_2088_; 
lean_inc_ref(v_val_1991_);
v___x_2081_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_1991_);
v___f_2082_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_2082_, 0, v___x_2081_);
lean_inc(v_fst_2021_);
lean_inc_ref(v___f_2082_);
v___x_2088_ = l_Option_merge___redArg(v___f_2082_, v_fst_2021_, v_fst_2025_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v___x_2089_; 
lean_inc_ref(v_val_1991_);
v___x_2089_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1991_);
v___y_2084_ = v___x_2089_;
goto v___jp_2083_;
}
else
{
lean_object* v_val_2090_; 
v_val_2090_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_val_2090_);
lean_dec_ref_known(v___x_2088_, 1);
v___y_2084_ = v_val_2090_;
goto v___jp_2083_;
}
v___jp_2037_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
lean_inc_ref(v_P_1994_);
v___x_2040_ = l_Lean_mkAppB(v_P_1994_, v_lhs_1992_, v_rhs_1993_);
v___x_2041_ = l_Lean_mkAppB(v_P_1994_, v___y_2038_, v___y_2039_);
v___x_2042_ = lean_expr_eqv(v___x_2040_, v___x_2041_);
if (v___x_2042_ == 0)
{
lean_object* v___x_2043_; 
lean_del_object(v___x_2030_);
lean_inc_ref(v___x_2041_);
v___x_2043_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_2040_, v___x_2041_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2045_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v___x_2045_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2041_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2057_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2048_ = v___x_2045_;
v_isShared_2049_ = v_isSharedCheck_2057_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2057_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2050_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2050_, 0, v_a_2046_);
lean_ctor_set(v___x_2050_, 1, v_a_2044_);
lean_ctor_set_uint8(v___x_2050_, sizeof(void*)*2, v___x_2042_);
lean_ctor_set_uint8(v___x_2050_, sizeof(void*)*2 + 1, v___x_2042_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2050_);
v___x_2052_ = v___x_2035_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2050_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_snd_2033_);
v___x_2052_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
lean_object* v___x_2054_; 
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v___x_2052_);
v___x_2054_ = v___x_2048_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec(v_a_2044_);
lean_del_object(v___x_2035_);
lean_dec(v_snd_2033_);
v_a_2058_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2045_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2045_);
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
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec_ref(v___x_2041_);
lean_del_object(v___x_2035_);
lean_dec(v_snd_2033_);
v_a_2066_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2043_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2043_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
lean_dec_ref(v___x_2041_);
lean_dec_ref(v___x_2040_);
v___x_2074_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2074_, 0, v___x_1995_);
lean_ctor_set_uint8(v___x_2074_, 1, v___x_1995_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2074_);
v___x_2076_ = v___x_2035_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v___x_2074_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v_snd_2033_);
v___x_2076_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
lean_object* v___x_2078_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2076_);
v___x_2078_ = v___x_2030_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2076_);
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
v___jp_2083_:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Option_merge___redArg(v___f_2082_, v_fst_2021_, v_fst_2032_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1991_);
v___y_2038_ = v___y_2084_;
v___y_2039_ = v___x_2086_;
goto v___jp_2037_;
}
else
{
lean_object* v_val_2087_; 
lean_dec_ref(v_val_1991_);
v_val_2087_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_val_2087_);
lean_dec_ref_known(v___x_2085_, 1);
v___y_2038_ = v___y_2084_;
v___y_2039_ = v_val_2087_;
goto v___jp_2037_;
}
}
}
}
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
lean_dec(v_fst_2025_);
lean_dec(v_fst_2021_);
lean_dec_ref(v_P_1994_);
lean_dec_ref(v_rhs_1993_);
lean_dec_ref(v_lhs_1992_);
lean_dec_ref(v_val_1991_);
v_a_2093_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2027_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2027_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec(v_fst_2021_);
lean_dec_ref(v_y_2018_);
lean_dec_ref(v_P_1994_);
lean_dec_ref(v_rhs_1993_);
lean_dec_ref(v_lhs_1992_);
lean_dec_ref(v_val_1991_);
v_a_2101_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_2023_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2023_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec_ref(v_y_2018_);
lean_dec_ref(v_x_2017_);
lean_dec_ref(v_P_1994_);
lean_dec_ref(v_rhs_1993_);
lean_dec_ref(v_lhs_1992_);
lean_dec_ref(v_val_1991_);
v_a_2109_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2019_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2019_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec(v_fst_2006_);
lean_dec_ref(v_P_1994_);
lean_dec_ref(v_rhs_1993_);
lean_dec_ref(v_lhs_1992_);
lean_dec_ref(v_val_1991_);
v_a_2117_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2008_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2008_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec_ref(v_P_1994_);
lean_dec_ref(v_rhs_1993_);
lean_dec_ref(v_lhs_1992_);
lean_dec_ref(v_val_1991_);
v_a_2125_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2004_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2004_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object* v_val_2133_, lean_object* v_lhs_2134_, lean_object* v_rhs_2135_, lean_object* v_P_2136_, lean_object* v___x_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
uint8_t v___x_209484__boxed_2146_; lean_object* v_res_2147_; 
v___x_209484__boxed_2146_ = lean_unbox(v___x_2137_);
v_res_2147_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(v_val_2133_, v_lhs_2134_, v_rhs_2135_, v_P_2136_, v___x_209484__boxed_2146_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
return v_res_2147_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_2150_ = l_Lean_stringToMessageData(v___x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(lean_object* v_x_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1);
v___x_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object* v_x_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(v_x_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v_x_2164_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(lean_object* v_val_2176_, lean_object* v_lhs_2177_, lean_object* v_rhs_2178_, lean_object* v_P_2179_, uint8_t v___x_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v___x_2189_; 
lean_inc_ref(v_lhs_2177_);
lean_inc_ref(v_val_2176_);
v___x_2189_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_2176_, v_lhs_2177_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v_fst_2191_; lean_object* v_snd_2192_; lean_object* v___x_2193_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2189_, 1);
v_fst_2191_ = lean_ctor_get(v_a_2190_, 0);
lean_inc(v_fst_2191_);
v_snd_2192_ = lean_ctor_get(v_a_2190_, 1);
lean_inc(v_snd_2192_);
lean_dec(v_a_2190_);
lean_inc_ref(v_rhs_2178_);
lean_inc_ref(v_val_2176_);
v___x_2193_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_2176_, v_rhs_2178_, v_snd_2192_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v_fst_2195_; lean_object* v_snd_2196_; lean_object* v___x_2197_; lean_object* v_a_2198_; lean_object* v_fst_2199_; lean_object* v_snd_2200_; lean_object* v_common_2201_; lean_object* v_x_2202_; lean_object* v_y_2203_; lean_object* v___x_2204_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
lean_dec_ref_known(v___x_2193_, 1);
v_fst_2195_ = lean_ctor_get(v_a_2194_, 0);
lean_inc(v_fst_2195_);
v_snd_2196_ = lean_ctor_get(v_a_2194_, 1);
lean_inc(v_snd_2196_);
lean_dec(v_a_2194_);
v___x_2197_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_2191_, v_fst_2195_, v_snd_2196_);
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref(v___x_2197_);
v_fst_2199_ = lean_ctor_get(v_a_2198_, 0);
lean_inc(v_fst_2199_);
v_snd_2200_ = lean_ctor_get(v_a_2198_, 1);
lean_inc(v_snd_2200_);
lean_dec(v_a_2198_);
v_common_2201_ = lean_ctor_get(v_fst_2199_, 0);
lean_inc_ref(v_common_2201_);
v_x_2202_ = lean_ctor_get(v_fst_2199_, 1);
lean_inc_ref(v_x_2202_);
v_y_2203_ = lean_ctor_get(v_fst_2199_, 2);
lean_inc_ref(v_y_2203_);
lean_dec(v_fst_2199_);
lean_inc_ref(v_val_2176_);
v___x_2204_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_2201_, v_val_2176_, v_snd_2200_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec_ref(v_common_2201_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v_fst_2206_; lean_object* v_snd_2207_; lean_object* v___x_2208_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec_ref_known(v___x_2204_, 1);
v_fst_2206_ = lean_ctor_get(v_a_2205_, 0);
lean_inc(v_fst_2206_);
v_snd_2207_ = lean_ctor_get(v_a_2205_, 1);
lean_inc(v_snd_2207_);
lean_dec(v_a_2205_);
lean_inc_ref(v_val_2176_);
v___x_2208_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_2202_, v_val_2176_, v_snd_2207_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec_ref(v_x_2202_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v_fst_2210_; lean_object* v_snd_2211_; lean_object* v___x_2212_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref_known(v___x_2208_, 1);
v_fst_2210_ = lean_ctor_get(v_a_2209_, 0);
lean_inc(v_fst_2210_);
v_snd_2211_ = lean_ctor_get(v_a_2209_, 1);
lean_inc(v_snd_2211_);
lean_dec(v_a_2209_);
lean_inc_ref(v_val_2176_);
v___x_2212_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_2203_, v_val_2176_, v_snd_2211_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec_ref(v_y_2203_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2277_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2215_ = v___x_2212_;
v_isShared_2216_ = v_isSharedCheck_2277_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2212_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2277_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v_fst_2217_; lean_object* v_snd_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2276_; 
v_fst_2217_ = lean_ctor_get(v_a_2213_, 0);
v_snd_2218_ = lean_ctor_get(v_a_2213_, 1);
v_isSharedCheck_2276_ = !lean_is_exclusive(v_a_2213_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2220_ = v_a_2213_;
v_isShared_2221_ = v_isSharedCheck_2276_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_snd_2218_);
lean_inc(v_fst_2217_);
lean_dec(v_a_2213_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2276_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___x_2266_; lean_object* v___f_2267_; lean_object* v___y_2269_; lean_object* v___x_2273_; 
lean_inc_ref(v_val_2176_);
v___x_2266_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2176_);
v___f_2267_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_2267_, 0, v___x_2266_);
lean_inc(v_fst_2206_);
lean_inc_ref(v___f_2267_);
v___x_2273_ = l_Option_merge___redArg(v___f_2267_, v_fst_2206_, v_fst_2210_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v___x_2274_; 
lean_inc_ref(v_val_2176_);
v___x_2274_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_2176_);
v___y_2269_ = v___x_2274_;
goto v___jp_2268_;
}
else
{
lean_object* v_val_2275_; 
v_val_2275_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_val_2275_);
lean_dec_ref_known(v___x_2273_, 1);
v___y_2269_ = v_val_2275_;
goto v___jp_2268_;
}
v___jp_2222_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; 
lean_inc_ref(v_P_2179_);
v___x_2225_ = l_Lean_mkAppB(v_P_2179_, v_lhs_2177_, v_rhs_2178_);
v___x_2226_ = l_Lean_mkAppB(v_P_2179_, v___y_2223_, v___y_2224_);
v___x_2227_ = lean_expr_eqv(v___x_2225_, v___x_2226_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; 
lean_del_object(v___x_2215_);
lean_inc_ref(v___x_2226_);
v___x_2228_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_2225_, v___x_2226_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2230_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2229_);
lean_dec_ref_known(v___x_2228_, 1);
v___x_2230_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2226_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2242_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2233_ = v___x_2230_;
v_isShared_2234_ = v_isSharedCheck_2242_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2230_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2242_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2237_; 
v___x_2235_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2235_, 0, v_a_2231_);
lean_ctor_set(v___x_2235_, 1, v_a_2229_);
lean_ctor_set_uint8(v___x_2235_, sizeof(void*)*2, v___x_2180_);
lean_ctor_set_uint8(v___x_2235_, sizeof(void*)*2 + 1, v___x_2180_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v___x_2235_);
v___x_2237_ = v___x_2220_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2235_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_snd_2218_);
v___x_2237_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
lean_object* v___x_2239_; 
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2237_);
v___x_2239_ = v___x_2233_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec(v_a_2229_);
lean_del_object(v___x_2220_);
lean_dec(v_snd_2218_);
v_a_2243_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2230_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2230_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec_ref(v___x_2226_);
lean_del_object(v___x_2220_);
lean_dec(v_snd_2218_);
v_a_2251_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2228_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2228_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
else
{
lean_object* v___x_2259_; lean_object* v___x_2261_; 
lean_dec_ref(v___x_2226_);
lean_dec_ref(v___x_2225_);
v___x_2259_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2259_, 0, v___x_2180_);
lean_ctor_set_uint8(v___x_2259_, 1, v___x_2180_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v___x_2259_);
v___x_2261_ = v___x_2220_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_snd_2218_);
v___x_2261_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
lean_object* v___x_2263_; 
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2261_);
v___x_2263_ = v___x_2215_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
v___jp_2268_:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Option_merge___redArg(v___f_2267_, v_fst_2206_, v_fst_2217_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_2176_);
v___y_2223_ = v___y_2269_;
v___y_2224_ = v___x_2271_;
goto v___jp_2222_;
}
else
{
lean_object* v_val_2272_; 
lean_dec_ref(v_val_2176_);
v_val_2272_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_val_2272_);
lean_dec_ref_known(v___x_2270_, 1);
v___y_2223_ = v___y_2269_;
v___y_2224_ = v_val_2272_;
goto v___jp_2222_;
}
}
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec(v_fst_2210_);
lean_dec(v_fst_2206_);
lean_dec_ref(v_P_2179_);
lean_dec_ref(v_rhs_2178_);
lean_dec_ref(v_lhs_2177_);
lean_dec_ref(v_val_2176_);
v_a_2278_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2212_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2212_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec(v_fst_2206_);
lean_dec_ref(v_y_2203_);
lean_dec_ref(v_P_2179_);
lean_dec_ref(v_rhs_2178_);
lean_dec_ref(v_lhs_2177_);
lean_dec_ref(v_val_2176_);
v_a_2286_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2208_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2208_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec_ref(v_y_2203_);
lean_dec_ref(v_x_2202_);
lean_dec_ref(v_P_2179_);
lean_dec_ref(v_rhs_2178_);
lean_dec_ref(v_lhs_2177_);
lean_dec_ref(v_val_2176_);
v_a_2294_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2204_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2204_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_dec(v_fst_2191_);
lean_dec_ref(v_P_2179_);
lean_dec_ref(v_rhs_2178_);
lean_dec_ref(v_lhs_2177_);
lean_dec_ref(v_val_2176_);
v_a_2302_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2193_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2193_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec_ref(v_P_2179_);
lean_dec_ref(v_rhs_2178_);
lean_dec_ref(v_lhs_2177_);
lean_dec_ref(v_val_2176_);
v_a_2310_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2189_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2189_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed(lean_object* v_val_2318_, lean_object* v_lhs_2319_, lean_object* v_rhs_2320_, lean_object* v_P_2321_, lean_object* v___x_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
uint8_t v___x_209819__boxed_2331_; lean_object* v_res_2332_; 
v___x_209819__boxed_2331_ = lean_unbox(v___x_2322_);
v_res_2332_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(v_val_2318_, v_lhs_2319_, v_rhs_2320_, v_P_2321_, v___x_209819__boxed_2331_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object* v_cls_2333_, lean_object* v_msg_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v_ref_2340_; lean_object* v___x_2341_; lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2386_; 
v_ref_2340_ = lean_ctor_get(v___y_2337_, 5);
v___x_2341_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2344_ = v___x_2341_;
v_isShared_2345_ = v_isSharedCheck_2386_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2341_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2386_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2346_; lean_object* v_traceState_2347_; lean_object* v_env_2348_; lean_object* v_nextMacroScope_2349_; lean_object* v_ngen_2350_; lean_object* v_auxDeclNGen_2351_; lean_object* v_cache_2352_; lean_object* v_messages_2353_; lean_object* v_infoState_2354_; lean_object* v_snapshotTasks_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2385_; 
v___x_2346_ = lean_st_ref_take(v___y_2338_);
v_traceState_2347_ = lean_ctor_get(v___x_2346_, 4);
v_env_2348_ = lean_ctor_get(v___x_2346_, 0);
v_nextMacroScope_2349_ = lean_ctor_get(v___x_2346_, 1);
v_ngen_2350_ = lean_ctor_get(v___x_2346_, 2);
v_auxDeclNGen_2351_ = lean_ctor_get(v___x_2346_, 3);
v_cache_2352_ = lean_ctor_get(v___x_2346_, 5);
v_messages_2353_ = lean_ctor_get(v___x_2346_, 6);
v_infoState_2354_ = lean_ctor_get(v___x_2346_, 7);
v_snapshotTasks_2355_ = lean_ctor_get(v___x_2346_, 8);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2357_ = v___x_2346_;
v_isShared_2358_ = v_isSharedCheck_2385_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_snapshotTasks_2355_);
lean_inc(v_infoState_2354_);
lean_inc(v_messages_2353_);
lean_inc(v_cache_2352_);
lean_inc(v_traceState_2347_);
lean_inc(v_auxDeclNGen_2351_);
lean_inc(v_ngen_2350_);
lean_inc(v_nextMacroScope_2349_);
lean_inc(v_env_2348_);
lean_dec(v___x_2346_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2385_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
uint64_t v_tid_2359_; lean_object* v_traces_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2384_; 
v_tid_2359_ = lean_ctor_get_uint64(v_traceState_2347_, sizeof(void*)*1);
v_traces_2360_ = lean_ctor_get(v_traceState_2347_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v_traceState_2347_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2362_ = v_traceState_2347_;
v_isShared_2363_ = v_isSharedCheck_2384_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_traces_2360_);
lean_dec(v_traceState_2347_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2384_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2364_; double v___x_2365_; uint8_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2374_; 
v___x_2364_ = lean_box(0);
v___x_2365_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_2366_ = 0;
v___x_2367_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_2368_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2368_, 0, v_cls_2333_);
lean_ctor_set(v___x_2368_, 1, v___x_2364_);
lean_ctor_set(v___x_2368_, 2, v___x_2367_);
lean_ctor_set_float(v___x_2368_, sizeof(void*)*3, v___x_2365_);
lean_ctor_set_float(v___x_2368_, sizeof(void*)*3 + 8, v___x_2365_);
lean_ctor_set_uint8(v___x_2368_, sizeof(void*)*3 + 16, v___x_2366_);
v___x_2369_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_2370_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2368_);
lean_ctor_set(v___x_2370_, 1, v_a_2342_);
lean_ctor_set(v___x_2370_, 2, v___x_2369_);
lean_inc(v_ref_2340_);
v___x_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2371_, 0, v_ref_2340_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
v___x_2372_ = l_Lean_PersistentArray_push___redArg(v_traces_2360_, v___x_2371_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 0, v___x_2372_);
v___x_2374_ = v___x_2362_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2372_);
lean_ctor_set_uint64(v_reuseFailAlloc_2383_, sizeof(void*)*1, v_tid_2359_);
v___x_2374_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2376_; 
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 4, v___x_2374_);
v___x_2376_ = v___x_2357_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_env_2348_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v_nextMacroScope_2349_);
lean_ctor_set(v_reuseFailAlloc_2382_, 2, v_ngen_2350_);
lean_ctor_set(v_reuseFailAlloc_2382_, 3, v_auxDeclNGen_2351_);
lean_ctor_set(v_reuseFailAlloc_2382_, 4, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2382_, 5, v_cache_2352_);
lean_ctor_set(v_reuseFailAlloc_2382_, 6, v_messages_2353_);
lean_ctor_set(v_reuseFailAlloc_2382_, 7, v_infoState_2354_);
lean_ctor_set(v_reuseFailAlloc_2382_, 8, v_snapshotTasks_2355_);
v___x_2376_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2380_; 
v___x_2377_ = lean_st_ref_put(v___y_2338_, v___x_2376_);
v___x_2378_ = lean_box(0);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v___x_2378_);
v___x_2380_ = v___x_2344_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2378_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object* v_cls_2387_, lean_object* v_msg_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2387_, v_msg_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
return v_res_2394_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1(void){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2397_ = l_Lean_stringToMessageData(v___x_2396_);
return v___x_2397_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3(void){
_start:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__2));
v___x_2400_ = l_Lean_stringToMessageData(v___x_2399_);
return v___x_2400_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5(void){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__4));
v___x_2403_ = l_Lean_stringToMessageData(v___x_2402_);
return v___x_2403_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6(void){
_start:
{
lean_object* v_cellCount_2404_; lean_object* v___x_2405_; 
v_cellCount_2404_ = lean_unsigned_to_nat(16u);
v___x_2405_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2404_);
return v___x_2405_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7(void){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2406_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_2407_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6);
v___x_2408_ = lean_unsigned_to_nat(0u);
v___x_2409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
lean_ctor_set(v___x_2409_, 1, v___x_2407_);
lean_ctor_set(v___x_2409_, 2, v___x_2406_);
return v___x_2409_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10(void){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__9));
v___x_2414_ = l_Lean_stringToMessageData(v___x_2413_);
return v___x_2414_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12(void){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2416_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__11));
v___x_2417_ = l_Lean_stringToMessageData(v___x_2416_);
return v___x_2417_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14(void){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__13));
v___x_2420_ = l_Lean_stringToMessageData(v___x_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(lean_object* v_lhs_2421_, lean_object* v_rhs_2422_, uint8_t v___x_2423_, lean_object* v___f_2424_, lean_object* v_cls_2425_, lean_object* v_P_2426_, lean_object* v_____r_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v___x_2447_; 
lean_inc_ref(v_lhs_2421_);
v___x_2447_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2421_);
if (lean_obj_tag(v___x_2447_) == 1)
{
lean_object* v_val_2448_; lean_object* v___x_2449_; 
v_val_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_val_2448_);
lean_dec_ref_known(v___x_2447_, 1);
lean_inc_ref(v_rhs_2422_);
v___x_2449_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2422_);
if (lean_obj_tag(v___x_2449_) == 1)
{
lean_object* v_val_2450_; uint8_t v___x_2489_; 
v_val_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_val_2450_);
lean_dec_ref_known(v___x_2449_, 1);
v___x_2489_ = lean_expr_eqv(v_val_2448_, v_val_2450_);
if (v___x_2489_ == 0)
{
lean_dec_ref(v_P_2426_);
goto v___jp_2451_;
}
else
{
if (v___x_2423_ == 0)
{
lean_object* v_options_2490_; lean_object* v_inheritedTraceOptions_2491_; uint8_t v_hasTrace_2492_; lean_object* v___x_2493_; lean_object* v___f_2494_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; 
lean_dec(v_val_2450_);
lean_dec_ref(v___f_2424_);
v_options_2490_ = lean_ctor_get(v___y_2435_, 2);
v_inheritedTraceOptions_2491_ = lean_ctor_get(v___y_2435_, 13);
v_hasTrace_2492_ = lean_ctor_get_uint8(v_options_2490_, sizeof(void*)*1);
v___x_2493_ = lean_box(v___x_2423_);
lean_inc(v_val_2448_);
v___f_2494_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed), 13, 5);
lean_closure_set(v___f_2494_, 0, v_val_2448_);
lean_closure_set(v___f_2494_, 1, v_lhs_2421_);
lean_closure_set(v___f_2494_, 2, v_rhs_2422_);
lean_closure_set(v___f_2494_, 3, v_P_2426_);
lean_closure_set(v___f_2494_, 4, v___x_2493_);
if (v_hasTrace_2492_ == 0)
{
lean_dec(v_cls_2425_);
v___y_2496_ = v___y_2431_;
v___y_2497_ = v___y_2432_;
v___y_2498_ = v___y_2433_;
v___y_2499_ = v___y_2434_;
v___y_2500_ = v___y_2435_;
v___y_2501_ = v___y_2436_;
goto v___jp_2495_;
}
else
{
lean_object* v___x_2506_; lean_object* v___x_2507_; uint8_t v___x_2508_; 
v___x_2506_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2425_);
v___x_2507_ = l_Lean_Name_append(v___x_2506_, v_cls_2425_);
v___x_2508_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2491_, v_options_2490_, v___x_2507_);
lean_dec(v___x_2507_);
if (v___x_2508_ == 0)
{
lean_dec(v_cls_2425_);
v___y_2496_ = v___y_2431_;
v___y_2497_ = v___y_2432_;
v___y_2498_ = v___y_2433_;
v___y_2499_ = v___y_2434_;
v___y_2500_ = v___y_2435_;
v___y_2501_ = v___y_2436_;
goto v___jp_2495_;
}
else
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2509_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10);
lean_inc(v_val_2448_);
v___x_2510_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2448_);
v___x_2511_ = l_Lean_MessageData_ofExpr(v___x_2510_);
v___x_2512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2509_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
v___x_2513_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12);
v___x_2514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
v___x_2515_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2425_, v___x_2514_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_dec_ref_known(v___x_2515_, 1);
v___y_2496_ = v___y_2431_;
v___y_2497_ = v___y_2432_;
v___y_2498_ = v___y_2433_;
v___y_2499_ = v___y_2434_;
v___y_2500_ = v___y_2435_;
v___y_2501_ = v___y_2436_;
goto v___jp_2495_;
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec_ref(v___f_2494_);
lean_dec(v_val_2448_);
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
}
v___jp_2495_:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2502_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7);
v___x_2503_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8));
v___x_2504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2504_, 0, v_val_2448_);
lean_ctor_set(v___x_2504_, 1, v___x_2502_);
lean_ctor_set(v___x_2504_, 2, v___x_2503_);
v___x_2505_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___f_2494_, v___x_2504_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
return v___x_2505_;
}
}
else
{
lean_dec_ref(v_P_2426_);
goto v___jp_2451_;
}
}
v___jp_2451_:
{
lean_object* v_inheritedTraceOptions_2452_; lean_object* v___x_2453_; 
v_inheritedTraceOptions_2452_ = lean_ctor_get(v___y_2435_, 13);
lean_inc(v___y_2436_);
lean_inc_ref(v___y_2435_);
lean_inc(v___y_2434_);
lean_inc_ref(v___y_2433_);
lean_inc(v___y_2432_);
lean_inc_ref(v___y_2431_);
lean_inc(v___y_2430_);
lean_inc_ref(v___y_2429_);
lean_inc(v___y_2428_);
lean_inc_ref(v_inheritedTraceOptions_2452_);
v___x_2453_ = lean_apply_11(v___f_2424_, v_inheritedTraceOptions_2452_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, lean_box(0));
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; uint8_t v___x_2455_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2454_);
lean_dec_ref_known(v___x_2453_, 1);
v___x_2455_ = lean_unbox(v_a_2454_);
lean_dec(v_a_2454_);
if (v___x_2455_ == 0)
{
lean_dec(v_val_2450_);
lean_dec(v_val_2448_);
lean_dec(v_cls_2425_);
lean_dec_ref(v_rhs_2422_);
lean_dec_ref(v_lhs_2421_);
goto v___jp_2438_;
}
else
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2456_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1);
v___x_2457_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2448_);
v___x_2458_ = l_Lean_MessageData_ofExpr(v___x_2457_);
v___x_2459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2456_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
v___x_2460_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3);
v___x_2461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2459_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = l_Lean_indentExpr(v_lhs_2421_);
v___x_2463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2461_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5);
v___x_2465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2450_);
v___x_2467_ = l_Lean_MessageData_ofExpr(v___x_2466_);
v___x_2468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2465_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
v___x_2469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
lean_ctor_set(v___x_2469_, 1, v___x_2460_);
v___x_2470_ = l_Lean_indentExpr(v_rhs_2422_);
v___x_2471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2469_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
v___x_2472_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2425_, v___x_2471_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_dec_ref_known(v___x_2472_, 1);
goto v___jp_2438_;
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2472_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2472_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec(v_val_2450_);
lean_dec(v_val_2448_);
lean_dec(v_cls_2425_);
lean_dec_ref(v_rhs_2422_);
lean_dec_ref(v_lhs_2421_);
v_a_2481_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2453_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2453_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2524_; lean_object* v___x_2525_; 
lean_dec(v___x_2449_);
lean_dec(v_val_2448_);
lean_dec_ref(v_P_2426_);
lean_dec_ref(v_lhs_2421_);
v_inheritedTraceOptions_2524_ = lean_ctor_get(v___y_2435_, 13);
lean_inc(v___y_2436_);
lean_inc_ref(v___y_2435_);
lean_inc(v___y_2434_);
lean_inc_ref(v___y_2433_);
lean_inc(v___y_2432_);
lean_inc_ref(v___y_2431_);
lean_inc(v___y_2430_);
lean_inc_ref(v___y_2429_);
lean_inc(v___y_2428_);
lean_inc_ref(v_inheritedTraceOptions_2524_);
v___x_2525_ = lean_apply_11(v___f_2424_, v_inheritedTraceOptions_2524_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, lean_box(0));
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; uint8_t v___x_2527_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2525_, 1);
v___x_2527_ = lean_unbox(v_a_2526_);
lean_dec(v_a_2526_);
if (v___x_2527_ == 0)
{
lean_dec(v_cls_2425_);
lean_dec_ref(v_rhs_2422_);
goto v___jp_2441_;
}
else
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2528_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14);
v___x_2529_ = l_Lean_indentExpr(v_rhs_2422_);
v___x_2530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2528_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
v___x_2531_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2425_, v___x_2530_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_dec_ref_known(v___x_2531_, 1);
goto v___jp_2441_;
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_dec(v_cls_2425_);
lean_dec_ref(v_rhs_2422_);
v_a_2540_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2525_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2525_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2548_; lean_object* v___x_2549_; 
lean_dec(v___x_2447_);
lean_dec_ref(v_P_2426_);
lean_dec_ref(v_rhs_2422_);
v_inheritedTraceOptions_2548_ = lean_ctor_get(v___y_2435_, 13);
lean_inc(v___y_2436_);
lean_inc_ref(v___y_2435_);
lean_inc(v___y_2434_);
lean_inc_ref(v___y_2433_);
lean_inc(v___y_2432_);
lean_inc_ref(v___y_2431_);
lean_inc(v___y_2430_);
lean_inc_ref(v___y_2429_);
lean_inc(v___y_2428_);
lean_inc_ref(v_inheritedTraceOptions_2548_);
v___x_2549_ = lean_apply_11(v___f_2424_, v_inheritedTraceOptions_2548_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, lean_box(0));
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; uint8_t v___x_2551_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
lean_dec_ref_known(v___x_2549_, 1);
v___x_2551_ = lean_unbox(v_a_2550_);
lean_dec(v_a_2550_);
if (v___x_2551_ == 0)
{
lean_dec(v_cls_2425_);
lean_dec_ref(v_lhs_2421_);
goto v___jp_2444_;
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2552_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14);
v___x_2553_ = l_Lean_indentExpr(v_lhs_2421_);
v___x_2554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2552_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2425_, v___x_2554_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_dec_ref_known(v___x_2555_, 1);
goto v___jp_2444_;
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2555_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2555_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_dec(v_cls_2425_);
lean_dec_ref(v_lhs_2421_);
v_a_2564_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2549_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2549_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
v___jp_2438_:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2439_, 0, v___x_2423_);
lean_ctor_set_uint8(v___x_2439_, 1, v___x_2423_);
v___x_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
return v___x_2440_;
}
v___jp_2441_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2442_, 0, v___x_2423_);
lean_ctor_set_uint8(v___x_2442_, 1, v___x_2423_);
v___x_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
return v___x_2443_;
}
v___jp_2444_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2445_, 0, v___x_2423_);
lean_ctor_set_uint8(v___x_2445_, 1, v___x_2423_);
v___x_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
return v___x_2446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___boxed(lean_object** _args){
lean_object* v_lhs_2572_ = _args[0];
lean_object* v_rhs_2573_ = _args[1];
lean_object* v___x_2574_ = _args[2];
lean_object* v___f_2575_ = _args[3];
lean_object* v_cls_2576_ = _args[4];
lean_object* v_P_2577_ = _args[5];
lean_object* v_____r_2578_ = _args[6];
lean_object* v___y_2579_ = _args[7];
lean_object* v___y_2580_ = _args[8];
lean_object* v___y_2581_ = _args[9];
lean_object* v___y_2582_ = _args[10];
lean_object* v___y_2583_ = _args[11];
lean_object* v___y_2584_ = _args[12];
lean_object* v___y_2585_ = _args[13];
lean_object* v___y_2586_ = _args[14];
lean_object* v___y_2587_ = _args[15];
lean_object* v___y_2588_ = _args[16];
_start:
{
uint8_t v___x_210256__boxed_2589_; lean_object* v_res_2590_; 
v___x_210256__boxed_2589_ = lean_unbox(v___x_2574_);
v_res_2590_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2572_, v_rhs_2573_, v___x_210256__boxed_2589_, v___f_2575_, v_cls_2576_, v_P_2577_, v_____r_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(lean_object* v_val_2591_, lean_object* v_lhs_2592_, lean_object* v_rhs_2593_, lean_object* v_P_2594_, uint8_t v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v___x_2604_; 
lean_inc_ref(v_lhs_2592_);
lean_inc_ref(v_val_2591_);
v___x_2604_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_2591_, v_lhs_2592_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v_fst_2606_; lean_object* v_snd_2607_; lean_object* v___x_2608_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2604_, 1);
v_fst_2606_ = lean_ctor_get(v_a_2605_, 0);
lean_inc(v_fst_2606_);
v_snd_2607_ = lean_ctor_get(v_a_2605_, 1);
lean_inc(v_snd_2607_);
lean_dec(v_a_2605_);
lean_inc_ref(v_rhs_2593_);
lean_inc_ref(v_val_2591_);
v___x_2608_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_2591_, v_rhs_2593_, v_snd_2607_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v_fst_2610_; lean_object* v_snd_2611_; lean_object* v___x_2612_; lean_object* v_a_2613_; lean_object* v_fst_2614_; lean_object* v_snd_2615_; lean_object* v_common_2616_; lean_object* v_x_2617_; lean_object* v_y_2618_; lean_object* v___x_2619_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
lean_dec_ref_known(v___x_2608_, 1);
v_fst_2610_ = lean_ctor_get(v_a_2609_, 0);
lean_inc(v_fst_2610_);
v_snd_2611_ = lean_ctor_get(v_a_2609_, 1);
lean_inc(v_snd_2611_);
lean_dec(v_a_2609_);
v___x_2612_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_2606_, v_fst_2610_, v_snd_2611_);
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref(v___x_2612_);
v_fst_2614_ = lean_ctor_get(v_a_2613_, 0);
lean_inc(v_fst_2614_);
v_snd_2615_ = lean_ctor_get(v_a_2613_, 1);
lean_inc(v_snd_2615_);
lean_dec(v_a_2613_);
v_common_2616_ = lean_ctor_get(v_fst_2614_, 0);
lean_inc_ref(v_common_2616_);
v_x_2617_ = lean_ctor_get(v_fst_2614_, 1);
lean_inc_ref(v_x_2617_);
v_y_2618_ = lean_ctor_get(v_fst_2614_, 2);
lean_inc_ref(v_y_2618_);
lean_dec(v_fst_2614_);
lean_inc_ref(v_val_2591_);
v___x_2619_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_2616_, v_val_2591_, v_snd_2615_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec_ref(v_common_2616_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v_fst_2621_; lean_object* v_snd_2622_; lean_object* v___x_2623_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2620_);
lean_dec_ref_known(v___x_2619_, 1);
v_fst_2621_ = lean_ctor_get(v_a_2620_, 0);
lean_inc(v_fst_2621_);
v_snd_2622_ = lean_ctor_get(v_a_2620_, 1);
lean_inc(v_snd_2622_);
lean_dec(v_a_2620_);
lean_inc_ref(v_val_2591_);
v___x_2623_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_2617_, v_val_2591_, v_snd_2622_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec_ref(v_x_2617_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v_fst_2625_; lean_object* v_snd_2626_; lean_object* v___x_2627_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___x_2623_, 1);
v_fst_2625_ = lean_ctor_get(v_a_2624_, 0);
lean_inc(v_fst_2625_);
v_snd_2626_ = lean_ctor_get(v_a_2624_, 1);
lean_inc(v_snd_2626_);
lean_dec(v_a_2624_);
lean_inc_ref(v_val_2591_);
v___x_2627_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_2618_, v_val_2591_, v_snd_2626_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec_ref(v_y_2618_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2692_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2630_ = v___x_2627_;
v_isShared_2631_ = v_isSharedCheck_2692_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2627_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2692_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v_fst_2632_; lean_object* v_snd_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2691_; 
v_fst_2632_ = lean_ctor_get(v_a_2628_, 0);
v_snd_2633_ = lean_ctor_get(v_a_2628_, 1);
v_isSharedCheck_2691_ = !lean_is_exclusive(v_a_2628_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2635_ = v_a_2628_;
v_isShared_2636_ = v_isSharedCheck_2691_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_snd_2633_);
lean_inc(v_fst_2632_);
lean_dec(v_a_2628_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2691_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___x_2681_; lean_object* v___f_2682_; lean_object* v___y_2684_; lean_object* v___x_2688_; 
lean_inc_ref(v_val_2591_);
v___x_2681_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2591_);
v___f_2682_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_2682_, 0, v___x_2681_);
lean_inc(v_fst_2621_);
lean_inc_ref(v___f_2682_);
v___x_2688_ = l_Option_merge___redArg(v___f_2682_, v_fst_2621_, v_fst_2625_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v___x_2689_; 
lean_inc_ref(v_val_2591_);
v___x_2689_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_2591_);
v___y_2684_ = v___x_2689_;
goto v___jp_2683_;
}
else
{
lean_object* v_val_2690_; 
v_val_2690_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_val_2690_);
lean_dec_ref_known(v___x_2688_, 1);
v___y_2684_ = v_val_2690_;
goto v___jp_2683_;
}
v___jp_2637_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
lean_inc_ref(v_P_2594_);
v___x_2640_ = l_Lean_mkAppB(v_P_2594_, v_lhs_2592_, v_rhs_2593_);
v___x_2641_ = l_Lean_mkAppB(v_P_2594_, v___y_2638_, v___y_2639_);
v___x_2642_ = lean_expr_eqv(v___x_2640_, v___x_2641_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; 
lean_del_object(v___x_2630_);
lean_inc_ref(v___x_2641_);
v___x_2643_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_2640_, v___x_2641_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2645_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___x_2643_, 1);
v___x_2645_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2641_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2657_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2648_ = v___x_2645_;
v_isShared_2649_ = v_isSharedCheck_2657_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2645_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2657_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2650_; lean_object* v___x_2652_; 
v___x_2650_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2650_, 0, v_a_2646_);
lean_ctor_set(v___x_2650_, 1, v_a_2644_);
lean_ctor_set_uint8(v___x_2650_, sizeof(void*)*2, v___x_2642_);
lean_ctor_set_uint8(v___x_2650_, sizeof(void*)*2 + 1, v___x_2642_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 0, v___x_2650_);
v___x_2652_ = v___x_2635_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2650_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v_snd_2633_);
v___x_2652_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
lean_object* v___x_2654_; 
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v___x_2652_);
v___x_2654_ = v___x_2648_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_dec(v_a_2644_);
lean_del_object(v___x_2635_);
lean_dec(v_snd_2633_);
v_a_2658_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2645_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2645_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
else
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
lean_dec_ref(v___x_2641_);
lean_del_object(v___x_2635_);
lean_dec(v_snd_2633_);
v_a_2666_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2668_ = v___x_2643_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2643_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2666_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
else
{
lean_object* v___x_2674_; lean_object* v___x_2676_; 
lean_dec_ref(v___x_2641_);
lean_dec_ref(v___x_2640_);
v___x_2674_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2674_, 0, v___y_2595_);
lean_ctor_set_uint8(v___x_2674_, 1, v___y_2595_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 0, v___x_2674_);
v___x_2676_ = v___x_2635_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2674_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_snd_2633_);
v___x_2676_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2678_; 
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2676_);
v___x_2678_ = v___x_2630_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2676_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
v___jp_2683_:
{
lean_object* v___x_2685_; 
v___x_2685_ = l_Option_merge___redArg(v___f_2682_, v_fst_2621_, v_fst_2632_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v___x_2686_; 
v___x_2686_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_2591_);
v___y_2638_ = v___y_2684_;
v___y_2639_ = v___x_2686_;
goto v___jp_2637_;
}
else
{
lean_object* v_val_2687_; 
lean_dec_ref(v_val_2591_);
v_val_2687_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_val_2687_);
lean_dec_ref_known(v___x_2685_, 1);
v___y_2638_ = v___y_2684_;
v___y_2639_ = v_val_2687_;
goto v___jp_2637_;
}
}
}
}
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_dec(v_fst_2625_);
lean_dec(v_fst_2621_);
lean_dec_ref(v_P_2594_);
lean_dec_ref(v_rhs_2593_);
lean_dec_ref(v_lhs_2592_);
lean_dec_ref(v_val_2591_);
v_a_2693_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2627_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2627_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
lean_dec(v_fst_2621_);
lean_dec_ref(v_y_2618_);
lean_dec_ref(v_P_2594_);
lean_dec_ref(v_rhs_2593_);
lean_dec_ref(v_lhs_2592_);
lean_dec_ref(v_val_2591_);
v_a_2701_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2623_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2623_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
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
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_dec_ref(v_y_2618_);
lean_dec_ref(v_x_2617_);
lean_dec_ref(v_P_2594_);
lean_dec_ref(v_rhs_2593_);
lean_dec_ref(v_lhs_2592_);
lean_dec_ref(v_val_2591_);
v_a_2709_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2619_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2619_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_dec(v_fst_2606_);
lean_dec_ref(v_P_2594_);
lean_dec_ref(v_rhs_2593_);
lean_dec_ref(v_lhs_2592_);
lean_dec_ref(v_val_2591_);
v_a_2717_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2608_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2608_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec_ref(v_P_2594_);
lean_dec_ref(v_rhs_2593_);
lean_dec_ref(v_lhs_2592_);
lean_dec_ref(v_val_2591_);
v_a_2725_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2604_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2604_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7___boxed(lean_object* v_val_2733_, lean_object* v_lhs_2734_, lean_object* v_rhs_2735_, lean_object* v_P_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
uint8_t v___y_210584__boxed_2746_; lean_object* v_res_2747_; 
v___y_210584__boxed_2746_ = lean_unbox(v___y_2737_);
v_res_2747_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(v_val_2733_, v_lhs_2734_, v_rhs_2735_, v_P_2736_, v___y_210584__boxed_2746_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(lean_object* v_lhs_2748_, lean_object* v_rhs_2749_, lean_object* v_P_2750_, lean_object* v_cls_2751_, uint8_t v___x_2752_, lean_object* v___f_2753_, uint8_t v___x_2754_, lean_object* v_____r_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v___x_2772_; 
lean_inc_ref(v_lhs_2748_);
v___x_2772_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2748_);
if (lean_obj_tag(v___x_2772_) == 1)
{
lean_object* v_val_2773_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; uint8_t v___y_2787_; lean_object* v___x_2811_; 
v_val_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_val_2773_);
lean_dec_ref_known(v___x_2772_, 1);
lean_inc_ref(v_rhs_2749_);
v___x_2811_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2749_);
if (lean_obj_tag(v___x_2811_) == 1)
{
lean_object* v_val_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2859_; 
v_val_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_2859_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_val_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2859_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
uint8_t v___x_2816_; 
v___x_2816_ = lean_expr_eqv(v_val_2773_, v_val_2812_);
if (v___x_2816_ == 0)
{
if (v___x_2752_ == 0)
{
lean_del_object(v___x_2814_);
lean_dec(v_val_2812_);
lean_dec_ref(v___f_2753_);
v___y_2787_ = v___x_2752_;
goto v___jp_2786_;
}
else
{
lean_object* v_inheritedTraceOptions_2822_; lean_object* v___x_2823_; 
lean_dec_ref(v_P_2750_);
v_inheritedTraceOptions_2822_ = lean_ctor_get(v___y_2763_, 13);
lean_inc(v___y_2764_);
lean_inc_ref(v___y_2763_);
lean_inc(v___y_2762_);
lean_inc_ref(v___y_2761_);
lean_inc(v___y_2760_);
lean_inc_ref(v___y_2759_);
lean_inc(v___y_2758_);
lean_inc_ref(v___y_2757_);
lean_inc(v___y_2756_);
lean_inc_ref(v_inheritedTraceOptions_2822_);
v___x_2823_ = lean_apply_11(v___f_2753_, v_inheritedTraceOptions_2822_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, lean_box(0));
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; uint8_t v___x_2825_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2823_, 1);
v___x_2825_ = lean_unbox(v_a_2824_);
lean_dec(v_a_2824_);
if (v___x_2825_ == 0)
{
lean_dec(v_val_2812_);
lean_dec(v_val_2773_);
lean_dec(v_cls_2751_);
lean_dec_ref(v_rhs_2749_);
lean_dec_ref(v_lhs_2748_);
goto v___jp_2817_;
}
else
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2826_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1);
v___x_2827_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2773_);
v___x_2828_ = l_Lean_MessageData_ofExpr(v___x_2827_);
v___x_2829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2826_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
v___x_2830_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3);
v___x_2831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2829_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
v___x_2832_ = l_Lean_indentExpr(v_lhs_2748_);
v___x_2833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2831_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
v___x_2834_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5);
v___x_2835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2833_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2812_);
v___x_2837_ = l_Lean_MessageData_ofExpr(v___x_2836_);
v___x_2838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2835_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
lean_ctor_set(v___x_2839_, 1, v___x_2830_);
v___x_2840_ = l_Lean_indentExpr(v_rhs_2749_);
v___x_2841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2839_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
v___x_2842_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2751_, v___x_2841_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_dec_ref_known(v___x_2842_, 1);
goto v___jp_2817_;
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_del_object(v___x_2814_);
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2842_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2842_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_del_object(v___x_2814_);
lean_dec(v_val_2812_);
lean_dec(v_val_2773_);
lean_dec(v_cls_2751_);
lean_dec_ref(v_rhs_2749_);
lean_dec_ref(v_lhs_2748_);
v_a_2851_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2823_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2823_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
}
else
{
lean_del_object(v___x_2814_);
lean_dec(v_val_2812_);
lean_dec_ref(v___f_2753_);
v___y_2787_ = v___x_2754_;
goto v___jp_2786_;
}
v___jp_2817_:
{
lean_object* v___x_2818_; lean_object* v___x_2820_; 
v___x_2818_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2818_, 0, v___x_2816_);
lean_ctor_set_uint8(v___x_2818_, 1, v___x_2816_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set_tag(v___x_2814_, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2818_);
v___x_2820_ = v___x_2814_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2818_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2860_; lean_object* v___x_2861_; 
lean_dec(v___x_2811_);
lean_dec(v_val_2773_);
lean_dec_ref(v_P_2750_);
lean_dec_ref(v_lhs_2748_);
v_inheritedTraceOptions_2860_ = lean_ctor_get(v___y_2763_, 13);
lean_inc(v___y_2764_);
lean_inc_ref(v___y_2763_);
lean_inc(v___y_2762_);
lean_inc_ref(v___y_2761_);
lean_inc(v___y_2760_);
lean_inc_ref(v___y_2759_);
lean_inc(v___y_2758_);
lean_inc_ref(v___y_2757_);
lean_inc(v___y_2756_);
lean_inc_ref(v_inheritedTraceOptions_2860_);
v___x_2861_ = lean_apply_11(v___f_2753_, v_inheritedTraceOptions_2860_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, lean_box(0));
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; uint8_t v___x_2863_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
v___x_2863_ = lean_unbox(v_a_2862_);
lean_dec(v_a_2862_);
if (v___x_2863_ == 0)
{
lean_dec(v_cls_2751_);
lean_dec_ref(v_rhs_2749_);
goto v___jp_2766_;
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2864_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14);
v___x_2865_ = l_Lean_indentExpr(v_rhs_2749_);
v___x_2866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2864_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2751_, v___x_2866_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_dec_ref_known(v___x_2867_, 1);
goto v___jp_2766_;
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2867_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2867_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_dec(v_cls_2751_);
lean_dec_ref(v_rhs_2749_);
v_a_2876_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2861_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2861_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
v___jp_2774_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2782_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7);
v___x_2783_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8));
v___x_2784_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2784_, 0, v_val_2773_);
lean_ctor_set(v___x_2784_, 1, v___x_2782_);
lean_ctor_set(v___x_2784_, 2, v___x_2783_);
v___x_2785_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___y_2775_, v___x_2784_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
return v___x_2785_;
}
v___jp_2786_:
{
lean_object* v_options_2788_; lean_object* v_inheritedTraceOptions_2789_; uint8_t v_hasTrace_2790_; lean_object* v___x_2791_; lean_object* v___f_2792_; 
v_options_2788_ = lean_ctor_get(v___y_2763_, 2);
v_inheritedTraceOptions_2789_ = lean_ctor_get(v___y_2763_, 13);
v_hasTrace_2790_ = lean_ctor_get_uint8(v_options_2788_, sizeof(void*)*1);
v___x_2791_ = lean_box(v___y_2787_);
lean_inc(v_val_2773_);
v___f_2792_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7___boxed), 13, 5);
lean_closure_set(v___f_2792_, 0, v_val_2773_);
lean_closure_set(v___f_2792_, 1, v_lhs_2748_);
lean_closure_set(v___f_2792_, 2, v_rhs_2749_);
lean_closure_set(v___f_2792_, 3, v_P_2750_);
lean_closure_set(v___f_2792_, 4, v___x_2791_);
if (v_hasTrace_2790_ == 0)
{
lean_dec(v_cls_2751_);
v___y_2775_ = v___f_2792_;
v___y_2776_ = v___y_2759_;
v___y_2777_ = v___y_2760_;
v___y_2778_ = v___y_2761_;
v___y_2779_ = v___y_2762_;
v___y_2780_ = v___y_2763_;
v___y_2781_ = v___y_2764_;
goto v___jp_2774_;
}
else
{
lean_object* v___x_2793_; lean_object* v___x_2794_; uint8_t v___x_2795_; 
v___x_2793_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2751_);
v___x_2794_ = l_Lean_Name_append(v___x_2793_, v_cls_2751_);
v___x_2795_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2789_, v_options_2788_, v___x_2794_);
lean_dec(v___x_2794_);
if (v___x_2795_ == 0)
{
lean_dec(v_cls_2751_);
v___y_2775_ = v___f_2792_;
v___y_2776_ = v___y_2759_;
v___y_2777_ = v___y_2760_;
v___y_2778_ = v___y_2761_;
v___y_2779_ = v___y_2762_;
v___y_2780_ = v___y_2763_;
v___y_2781_ = v___y_2764_;
goto v___jp_2774_;
}
else
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2796_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10);
lean_inc(v_val_2773_);
v___x_2797_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2773_);
v___x_2798_ = l_Lean_MessageData_ofExpr(v___x_2797_);
v___x_2799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2796_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
v___x_2800_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12);
v___x_2801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2799_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
v___x_2802_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2751_, v___x_2801_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_dec_ref_known(v___x_2802_, 1);
v___y_2775_ = v___f_2792_;
v___y_2776_ = v___y_2759_;
v___y_2777_ = v___y_2760_;
v___y_2778_ = v___y_2761_;
v___y_2779_ = v___y_2762_;
v___y_2780_ = v___y_2763_;
v___y_2781_ = v___y_2764_;
goto v___jp_2774_;
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_dec_ref(v___f_2792_);
lean_dec(v_val_2773_);
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2802_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2802_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2884_; lean_object* v___x_2885_; 
lean_dec(v___x_2772_);
lean_dec_ref(v_P_2750_);
lean_dec_ref(v_rhs_2749_);
v_inheritedTraceOptions_2884_ = lean_ctor_get(v___y_2763_, 13);
lean_inc(v___y_2764_);
lean_inc_ref(v___y_2763_);
lean_inc(v___y_2762_);
lean_inc_ref(v___y_2761_);
lean_inc(v___y_2760_);
lean_inc_ref(v___y_2759_);
lean_inc(v___y_2758_);
lean_inc_ref(v___y_2757_);
lean_inc(v___y_2756_);
lean_inc_ref(v_inheritedTraceOptions_2884_);
v___x_2885_ = lean_apply_11(v___f_2753_, v_inheritedTraceOptions_2884_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, lean_box(0));
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; uint8_t v___x_2887_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref_known(v___x_2885_, 1);
v___x_2887_ = lean_unbox(v_a_2886_);
lean_dec(v_a_2886_);
if (v___x_2887_ == 0)
{
lean_dec(v_cls_2751_);
lean_dec_ref(v_lhs_2748_);
goto v___jp_2769_;
}
else
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2888_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14);
v___x_2889_ = l_Lean_indentExpr(v_lhs_2748_);
v___x_2890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2888_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
v___x_2891_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2751_, v___x_2890_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_dec_ref_known(v___x_2891_, 1);
goto v___jp_2769_;
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2891_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2891_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec(v_cls_2751_);
lean_dec_ref(v_lhs_2748_);
v_a_2900_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2885_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2885_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
v___jp_2766_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2767_, 0, v___x_2754_);
lean_ctor_set_uint8(v___x_2767_, 1, v___x_2754_);
v___x_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
return v___x_2768_;
}
v___jp_2769_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2770_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2770_, 0, v___x_2754_);
lean_ctor_set_uint8(v___x_2770_, 1, v___x_2754_);
v___x_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2770_);
return v___x_2771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___boxed(lean_object** _args){
lean_object* v_lhs_2908_ = _args[0];
lean_object* v_rhs_2909_ = _args[1];
lean_object* v_P_2910_ = _args[2];
lean_object* v_cls_2911_ = _args[3];
lean_object* v___x_2912_ = _args[4];
lean_object* v___f_2913_ = _args[5];
lean_object* v___x_2914_ = _args[6];
lean_object* v_____r_2915_ = _args[7];
lean_object* v___y_2916_ = _args[8];
lean_object* v___y_2917_ = _args[9];
lean_object* v___y_2918_ = _args[10];
lean_object* v___y_2919_ = _args[11];
lean_object* v___y_2920_ = _args[12];
lean_object* v___y_2921_ = _args[13];
lean_object* v___y_2922_ = _args[14];
lean_object* v___y_2923_ = _args[15];
lean_object* v___y_2924_ = _args[16];
lean_object* v___y_2925_ = _args[17];
_start:
{
uint8_t v___x_210906__boxed_2926_; uint8_t v___x_210908__boxed_2927_; lean_object* v_res_2928_; 
v___x_210906__boxed_2926_ = lean_unbox(v___x_2912_);
v___x_210908__boxed_2927_ = lean_unbox(v___x_2914_);
v_res_2928_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2908_, v_rhs_2909_, v_P_2910_, v_cls_2911_, v___x_210906__boxed_2926_, v___f_2913_, v___x_210908__boxed_2927_, v_____r_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(lean_object* v_x_2929_){
_start:
{
if (lean_obj_tag(v_x_2929_) == 0)
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
v_a_2931_ = lean_ctor_get(v_x_2929_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v_x_2929_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v_x_2929_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v_x_2929_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
lean_ctor_set_tag(v___x_2933_, 1);
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
v_a_2939_ = lean_ctor_get(v_x_2929_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v_x_2929_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v_x_2929_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v_x_2929_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
lean_ctor_set_tag(v___x_2941_, 0);
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg___boxed(lean_object* v_x_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_2947_);
return v_res_2949_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(lean_object* v_e_2950_){
_start:
{
if (lean_obj_tag(v_e_2950_) == 0)
{
uint8_t v___x_2951_; 
v___x_2951_ = 2;
return v___x_2951_;
}
else
{
uint8_t v___x_2952_; 
v___x_2952_ = 0;
return v___x_2952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5___boxed(lean_object* v_e_2953_){
_start:
{
uint8_t v_res_2954_; lean_object* v_r_2955_; 
v_res_2954_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_e_2953_);
lean_dec_ref(v_e_2953_);
v_r_2955_ = lean_box(v_res_2954_);
return v_r_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(lean_object* v_opts_2956_, lean_object* v_opt_2957_){
_start:
{
lean_object* v_name_2958_; lean_object* v_defValue_2959_; lean_object* v_map_2960_; lean_object* v___x_2961_; 
v_name_2958_ = lean_ctor_get(v_opt_2957_, 0);
v_defValue_2959_ = lean_ctor_get(v_opt_2957_, 1);
v_map_2960_ = lean_ctor_get(v_opts_2956_, 0);
v___x_2961_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2960_, v_name_2958_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_inc(v_defValue_2959_);
return v_defValue_2959_;
}
else
{
lean_object* v_val_2962_; 
v_val_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_val_2962_);
lean_dec_ref_known(v___x_2961_, 1);
if (lean_obj_tag(v_val_2962_) == 3)
{
lean_object* v_v_2963_; 
v_v_2963_ = lean_ctor_get(v_val_2962_, 0);
lean_inc(v_v_2963_);
lean_dec_ref_known(v_val_2962_, 1);
return v_v_2963_;
}
else
{
lean_dec(v_val_2962_);
lean_inc(v_defValue_2959_);
return v_defValue_2959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6___boxed(lean_object* v_opts_2964_, lean_object* v_opt_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2964_, v_opt_2965_);
lean_dec_ref(v_opt_2965_);
lean_dec_ref(v_opts_2964_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(size_t v_sz_2967_, size_t v_i_2968_, lean_object* v_bs_2969_){
_start:
{
uint8_t v___x_2970_; 
v___x_2970_ = lean_usize_dec_lt(v_i_2968_, v_sz_2967_);
if (v___x_2970_ == 0)
{
return v_bs_2969_;
}
else
{
lean_object* v_v_2971_; lean_object* v_msg_2972_; lean_object* v___x_2973_; lean_object* v_bs_x27_2974_; size_t v___x_2975_; size_t v___x_2976_; lean_object* v___x_2977_; 
v_v_2971_ = lean_array_uget_borrowed(v_bs_2969_, v_i_2968_);
v_msg_2972_ = lean_ctor_get(v_v_2971_, 1);
lean_inc_ref(v_msg_2972_);
v___x_2973_ = lean_unsigned_to_nat(0u);
v_bs_x27_2974_ = lean_array_uset(v_bs_2969_, v_i_2968_, v___x_2973_);
v___x_2975_ = ((size_t)1ULL);
v___x_2976_ = lean_usize_add(v_i_2968_, v___x_2975_);
v___x_2977_ = lean_array_uset(v_bs_x27_2974_, v_i_2968_, v_msg_2972_);
v_i_2968_ = v___x_2976_;
v_bs_2969_ = v___x_2977_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2979_, lean_object* v_i_2980_, lean_object* v_bs_2981_){
_start:
{
size_t v_sz_boxed_2982_; size_t v_i_boxed_2983_; lean_object* v_res_2984_; 
v_sz_boxed_2982_ = lean_unbox_usize(v_sz_2979_);
lean_dec(v_sz_2979_);
v_i_boxed_2983_ = lean_unbox_usize(v_i_2980_);
lean_dec(v_i_2980_);
v_res_2984_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_boxed_2982_, v_i_boxed_2983_, v_bs_2981_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(lean_object* v_oldTraces_2985_, lean_object* v_data_2986_, lean_object* v_ref_2987_, lean_object* v_msg_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_fileName_2994_; lean_object* v_fileMap_2995_; lean_object* v_options_2996_; lean_object* v_currRecDepth_2997_; lean_object* v_maxRecDepth_2998_; lean_object* v_ref_2999_; lean_object* v_currNamespace_3000_; lean_object* v_openDecls_3001_; lean_object* v_initHeartbeats_3002_; lean_object* v_maxHeartbeats_3003_; lean_object* v_quotContext_3004_; lean_object* v_currMacroScope_3005_; uint8_t v_diag_3006_; lean_object* v_cancelTk_x3f_3007_; uint8_t v_suppressElabErrors_3008_; lean_object* v_inheritedTraceOptions_3009_; lean_object* v___x_3010_; lean_object* v_traceState_3011_; lean_object* v_traces_3012_; lean_object* v_ref_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; size_t v_sz_3016_; size_t v___x_3017_; lean_object* v___x_3018_; lean_object* v_msg_3019_; lean_object* v___x_3020_; lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3058_; 
v_fileName_2994_ = lean_ctor_get(v___y_2991_, 0);
v_fileMap_2995_ = lean_ctor_get(v___y_2991_, 1);
v_options_2996_ = lean_ctor_get(v___y_2991_, 2);
v_currRecDepth_2997_ = lean_ctor_get(v___y_2991_, 3);
v_maxRecDepth_2998_ = lean_ctor_get(v___y_2991_, 4);
v_ref_2999_ = lean_ctor_get(v___y_2991_, 5);
v_currNamespace_3000_ = lean_ctor_get(v___y_2991_, 6);
v_openDecls_3001_ = lean_ctor_get(v___y_2991_, 7);
v_initHeartbeats_3002_ = lean_ctor_get(v___y_2991_, 8);
v_maxHeartbeats_3003_ = lean_ctor_get(v___y_2991_, 9);
v_quotContext_3004_ = lean_ctor_get(v___y_2991_, 10);
v_currMacroScope_3005_ = lean_ctor_get(v___y_2991_, 11);
v_diag_3006_ = lean_ctor_get_uint8(v___y_2991_, sizeof(void*)*14);
v_cancelTk_x3f_3007_ = lean_ctor_get(v___y_2991_, 12);
v_suppressElabErrors_3008_ = lean_ctor_get_uint8(v___y_2991_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3009_ = lean_ctor_get(v___y_2991_, 13);
v___x_3010_ = lean_st_ref_get(v___y_2992_);
v_traceState_3011_ = lean_ctor_get(v___x_3010_, 4);
lean_inc_ref(v_traceState_3011_);
lean_dec(v___x_3010_);
v_traces_3012_ = lean_ctor_get(v_traceState_3011_, 0);
lean_inc_ref(v_traces_3012_);
lean_dec_ref(v_traceState_3011_);
v_ref_3013_ = l_Lean_replaceRef(v_ref_2987_, v_ref_2999_);
lean_inc_ref(v_inheritedTraceOptions_3009_);
lean_inc(v_cancelTk_x3f_3007_);
lean_inc(v_currMacroScope_3005_);
lean_inc(v_quotContext_3004_);
lean_inc(v_maxHeartbeats_3003_);
lean_inc(v_initHeartbeats_3002_);
lean_inc(v_openDecls_3001_);
lean_inc(v_currNamespace_3000_);
lean_inc(v_maxRecDepth_2998_);
lean_inc(v_currRecDepth_2997_);
lean_inc_ref(v_options_2996_);
lean_inc_ref(v_fileMap_2995_);
lean_inc_ref(v_fileName_2994_);
v___x_3014_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3014_, 0, v_fileName_2994_);
lean_ctor_set(v___x_3014_, 1, v_fileMap_2995_);
lean_ctor_set(v___x_3014_, 2, v_options_2996_);
lean_ctor_set(v___x_3014_, 3, v_currRecDepth_2997_);
lean_ctor_set(v___x_3014_, 4, v_maxRecDepth_2998_);
lean_ctor_set(v___x_3014_, 5, v_ref_3013_);
lean_ctor_set(v___x_3014_, 6, v_currNamespace_3000_);
lean_ctor_set(v___x_3014_, 7, v_openDecls_3001_);
lean_ctor_set(v___x_3014_, 8, v_initHeartbeats_3002_);
lean_ctor_set(v___x_3014_, 9, v_maxHeartbeats_3003_);
lean_ctor_set(v___x_3014_, 10, v_quotContext_3004_);
lean_ctor_set(v___x_3014_, 11, v_currMacroScope_3005_);
lean_ctor_set(v___x_3014_, 12, v_cancelTk_x3f_3007_);
lean_ctor_set(v___x_3014_, 13, v_inheritedTraceOptions_3009_);
lean_ctor_set_uint8(v___x_3014_, sizeof(void*)*14, v_diag_3006_);
lean_ctor_set_uint8(v___x_3014_, sizeof(void*)*14 + 1, v_suppressElabErrors_3008_);
v___x_3015_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3012_);
lean_dec_ref(v_traces_3012_);
v_sz_3016_ = lean_array_size(v___x_3015_);
v___x_3017_ = ((size_t)0ULL);
v___x_3018_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_3016_, v___x_3017_, v___x_3015_);
v_msg_3019_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3019_, 0, v_data_2986_);
lean_ctor_set(v_msg_3019_, 1, v_msg_2988_);
lean_ctor_set(v_msg_3019_, 2, v___x_3018_);
v___x_3020_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_3019_, v___y_2989_, v___y_2990_, v___x_3014_, v___y_2992_);
lean_dec_ref_known(v___x_3014_, 14);
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3023_ = v___x_3020_;
v_isShared_3024_ = v_isSharedCheck_3058_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_3020_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3058_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3025_; lean_object* v_traceState_3026_; lean_object* v_env_3027_; lean_object* v_nextMacroScope_3028_; lean_object* v_ngen_3029_; lean_object* v_auxDeclNGen_3030_; lean_object* v_cache_3031_; lean_object* v_messages_3032_; lean_object* v_infoState_3033_; lean_object* v_snapshotTasks_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3057_; 
v___x_3025_ = lean_st_ref_take(v___y_2992_);
v_traceState_3026_ = lean_ctor_get(v___x_3025_, 4);
v_env_3027_ = lean_ctor_get(v___x_3025_, 0);
v_nextMacroScope_3028_ = lean_ctor_get(v___x_3025_, 1);
v_ngen_3029_ = lean_ctor_get(v___x_3025_, 2);
v_auxDeclNGen_3030_ = lean_ctor_get(v___x_3025_, 3);
v_cache_3031_ = lean_ctor_get(v___x_3025_, 5);
v_messages_3032_ = lean_ctor_get(v___x_3025_, 6);
v_infoState_3033_ = lean_ctor_get(v___x_3025_, 7);
v_snapshotTasks_3034_ = lean_ctor_get(v___x_3025_, 8);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3036_ = v___x_3025_;
v_isShared_3037_ = v_isSharedCheck_3057_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_snapshotTasks_3034_);
lean_inc(v_infoState_3033_);
lean_inc(v_messages_3032_);
lean_inc(v_cache_3031_);
lean_inc(v_traceState_3026_);
lean_inc(v_auxDeclNGen_3030_);
lean_inc(v_ngen_3029_);
lean_inc(v_nextMacroScope_3028_);
lean_inc(v_env_3027_);
lean_dec(v___x_3025_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3057_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
uint64_t v_tid_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3055_; 
v_tid_3038_ = lean_ctor_get_uint64(v_traceState_3026_, sizeof(void*)*1);
v_isSharedCheck_3055_ = !lean_is_exclusive(v_traceState_3026_);
if (v_isSharedCheck_3055_ == 0)
{
lean_object* v_unused_3056_; 
v_unused_3056_ = lean_ctor_get(v_traceState_3026_, 0);
lean_dec(v_unused_3056_);
v___x_3040_ = v_traceState_3026_;
v_isShared_3041_ = v_isSharedCheck_3055_;
goto v_resetjp_3039_;
}
else
{
lean_dec(v_traceState_3026_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3055_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3045_; 
v___x_3042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3042_, 0, v_ref_2987_);
lean_ctor_set(v___x_3042_, 1, v_a_3021_);
v___x_3043_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2985_, v___x_3042_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v___x_3043_);
v___x_3045_ = v___x_3040_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3043_);
lean_ctor_set_uint64(v_reuseFailAlloc_3054_, sizeof(void*)*1, v_tid_3038_);
v___x_3045_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
lean_object* v___x_3047_; 
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 4, v___x_3045_);
v___x_3047_ = v___x_3036_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_env_3027_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v_nextMacroScope_3028_);
lean_ctor_set(v_reuseFailAlloc_3053_, 2, v_ngen_3029_);
lean_ctor_set(v_reuseFailAlloc_3053_, 3, v_auxDeclNGen_3030_);
lean_ctor_set(v_reuseFailAlloc_3053_, 4, v___x_3045_);
lean_ctor_set(v_reuseFailAlloc_3053_, 5, v_cache_3031_);
lean_ctor_set(v_reuseFailAlloc_3053_, 6, v_messages_3032_);
lean_ctor_set(v_reuseFailAlloc_3053_, 7, v_infoState_3033_);
lean_ctor_set(v_reuseFailAlloc_3053_, 8, v_snapshotTasks_3034_);
v___x_3047_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3051_; 
v___x_3048_ = lean_st_ref_put(v___y_2992_, v___x_3047_);
v___x_3049_ = lean_box(0);
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 0, v___x_3049_);
v___x_3051_ = v___x_3023_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3049_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_3059_, lean_object* v_data_3060_, lean_object* v_ref_3061_, lean_object* v_msg_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_3059_, v_data_3060_, v_ref_3061_, v_msg_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
return v_res_3068_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__0));
v___x_3071_ = l_Lean_stringToMessageData(v___x_3070_);
return v___x_3071_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3072_; double v___x_3073_; 
v___x_3072_ = lean_unsigned_to_nat(1000u);
v___x_3073_ = lean_float_of_nat(v___x_3072_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(lean_object* v_cls_3074_, uint8_t v_collapsed_3075_, lean_object* v_tag_3076_, lean_object* v_opts_3077_, uint8_t v_clsEnabled_3078_, lean_object* v_oldTraces_3079_, lean_object* v_msg_3080_, lean_object* v_resStartStop_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v_fst_3092_; lean_object* v_snd_3093_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v_data_3097_; lean_object* v_fst_3108_; lean_object* v_snd_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; lean_object* v___y_3113_; lean_object* v_a_3114_; uint8_t v___y_3129_; double v___y_3160_; 
v_fst_3092_ = lean_ctor_get(v_resStartStop_3081_, 0);
lean_inc(v_fst_3092_);
v_snd_3093_ = lean_ctor_get(v_resStartStop_3081_, 1);
lean_inc(v_snd_3093_);
lean_dec_ref(v_resStartStop_3081_);
v_fst_3108_ = lean_ctor_get(v_snd_3093_, 0);
lean_inc(v_fst_3108_);
v_snd_3109_ = lean_ctor_get(v_snd_3093_, 1);
lean_inc(v_snd_3109_);
lean_dec(v_snd_3093_);
v___x_3110_ = l_Lean_trace_profiler;
v___x_3111_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_3077_, v___x_3110_);
if (v___x_3111_ == 0)
{
v___y_3129_ = v___x_3111_;
goto v___jp_3128_;
}
else
{
lean_object* v___x_3165_; uint8_t v___x_3166_; 
v___x_3165_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3166_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_3077_, v___x_3165_);
if (v___x_3166_ == 0)
{
lean_object* v___x_3167_; lean_object* v___x_3168_; double v___x_3169_; double v___x_3170_; double v___x_3171_; 
v___x_3167_ = l_Lean_trace_profiler_threshold;
v___x_3168_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_3077_, v___x_3167_);
v___x_3169_ = lean_float_of_nat(v___x_3168_);
v___x_3170_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2);
v___x_3171_ = lean_float_div(v___x_3169_, v___x_3170_);
v___y_3160_ = v___x_3171_;
goto v___jp_3159_;
}
else
{
lean_object* v___x_3172_; lean_object* v___x_3173_; double v___x_3174_; 
v___x_3172_ = l_Lean_trace_profiler_threshold;
v___x_3173_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_3077_, v___x_3172_);
v___x_3174_ = lean_float_of_nat(v___x_3173_);
v___y_3160_ = v___x_3174_;
goto v___jp_3159_;
}
}
v___jp_3094_:
{
lean_object* v___x_3098_; 
lean_inc(v___y_3096_);
v___x_3098_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_3079_, v_data_3097_, v___y_3096_, v___y_3095_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_object* v___x_3099_; 
lean_dec_ref_known(v___x_3098_, 1);
v___x_3099_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_fst_3092_);
return v___x_3099_;
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
lean_dec(v_fst_3092_);
v_a_3100_ = lean_ctor_get(v___x_3098_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3098_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3098_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
v___jp_3112_:
{
uint8_t v_result_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; double v___x_3118_; lean_object* v_data_3119_; 
v_result_3115_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_fst_3092_);
v___x_3116_ = lean_box(v_result_3115_);
v___x_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3116_);
v___x_3118_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_3076_);
lean_inc_ref(v___x_3117_);
lean_inc(v_cls_3074_);
v_data_3119_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3119_, 0, v_cls_3074_);
lean_ctor_set(v_data_3119_, 1, v___x_3117_);
lean_ctor_set(v_data_3119_, 2, v_tag_3076_);
lean_ctor_set_float(v_data_3119_, sizeof(void*)*3, v___x_3118_);
lean_ctor_set_float(v_data_3119_, sizeof(void*)*3 + 8, v___x_3118_);
lean_ctor_set_uint8(v_data_3119_, sizeof(void*)*3 + 16, v_collapsed_3075_);
if (v___x_3111_ == 0)
{
lean_dec_ref_known(v___x_3117_, 1);
lean_dec(v_snd_3109_);
lean_dec(v_fst_3108_);
lean_dec_ref(v_tag_3076_);
lean_dec(v_cls_3074_);
v___y_3095_ = v_a_3114_;
v___y_3096_ = v___y_3113_;
v_data_3097_ = v_data_3119_;
goto v___jp_3094_;
}
else
{
lean_object* v_data_3120_; double v___x_3121_; double v___x_3122_; 
lean_dec_ref_known(v_data_3119_, 3);
v_data_3120_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3120_, 0, v_cls_3074_);
lean_ctor_set(v_data_3120_, 1, v___x_3117_);
lean_ctor_set(v_data_3120_, 2, v_tag_3076_);
v___x_3121_ = lean_unbox_float(v_fst_3108_);
lean_dec(v_fst_3108_);
lean_ctor_set_float(v_data_3120_, sizeof(void*)*3, v___x_3121_);
v___x_3122_ = lean_unbox_float(v_snd_3109_);
lean_dec(v_snd_3109_);
lean_ctor_set_float(v_data_3120_, sizeof(void*)*3 + 8, v___x_3122_);
lean_ctor_set_uint8(v_data_3120_, sizeof(void*)*3 + 16, v_collapsed_3075_);
v___y_3095_ = v_a_3114_;
v___y_3096_ = v___y_3113_;
v_data_3097_ = v_data_3120_;
goto v___jp_3094_;
}
}
v___jp_3123_:
{
lean_object* v_ref_3124_; lean_object* v___x_3125_; 
v_ref_3124_ = lean_ctor_get(v___y_3089_, 5);
lean_inc(v___y_3090_);
lean_inc_ref(v___y_3089_);
lean_inc(v___y_3088_);
lean_inc_ref(v___y_3087_);
lean_inc(v___y_3086_);
lean_inc_ref(v___y_3085_);
lean_inc(v___y_3084_);
lean_inc_ref(v___y_3083_);
lean_inc(v___y_3082_);
lean_inc(v_fst_3092_);
v___x_3125_ = lean_apply_11(v_msg_3080_, v_fst_3092_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, lean_box(0));
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v_a_3126_; 
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_a_3126_);
lean_dec_ref_known(v___x_3125_, 1);
v___y_3113_ = v_ref_3124_;
v_a_3114_ = v_a_3126_;
goto v___jp_3112_;
}
else
{
lean_object* v___x_3127_; 
lean_dec_ref_known(v___x_3125_, 1);
v___x_3127_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1);
v___y_3113_ = v_ref_3124_;
v_a_3114_ = v___x_3127_;
goto v___jp_3112_;
}
}
v___jp_3128_:
{
if (v_clsEnabled_3078_ == 0)
{
if (v___y_3129_ == 0)
{
lean_object* v___x_3130_; lean_object* v_traceState_3131_; lean_object* v_env_3132_; lean_object* v_nextMacroScope_3133_; lean_object* v_ngen_3134_; lean_object* v_auxDeclNGen_3135_; lean_object* v_cache_3136_; lean_object* v_messages_3137_; lean_object* v_infoState_3138_; lean_object* v_snapshotTasks_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3158_; 
lean_dec(v_snd_3109_);
lean_dec(v_fst_3108_);
lean_dec_ref(v_msg_3080_);
lean_dec_ref(v_tag_3076_);
lean_dec(v_cls_3074_);
v___x_3130_ = lean_st_ref_take(v___y_3090_);
v_traceState_3131_ = lean_ctor_get(v___x_3130_, 4);
v_env_3132_ = lean_ctor_get(v___x_3130_, 0);
v_nextMacroScope_3133_ = lean_ctor_get(v___x_3130_, 1);
v_ngen_3134_ = lean_ctor_get(v___x_3130_, 2);
v_auxDeclNGen_3135_ = lean_ctor_get(v___x_3130_, 3);
v_cache_3136_ = lean_ctor_get(v___x_3130_, 5);
v_messages_3137_ = lean_ctor_get(v___x_3130_, 6);
v_infoState_3138_ = lean_ctor_get(v___x_3130_, 7);
v_snapshotTasks_3139_ = lean_ctor_get(v___x_3130_, 8);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3141_ = v___x_3130_;
v_isShared_3142_ = v_isSharedCheck_3158_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_snapshotTasks_3139_);
lean_inc(v_infoState_3138_);
lean_inc(v_messages_3137_);
lean_inc(v_cache_3136_);
lean_inc(v_traceState_3131_);
lean_inc(v_auxDeclNGen_3135_);
lean_inc(v_ngen_3134_);
lean_inc(v_nextMacroScope_3133_);
lean_inc(v_env_3132_);
lean_dec(v___x_3130_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3158_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
uint64_t v_tid_3143_; lean_object* v_traces_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3157_; 
v_tid_3143_ = lean_ctor_get_uint64(v_traceState_3131_, sizeof(void*)*1);
v_traces_3144_ = lean_ctor_get(v_traceState_3131_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v_traceState_3131_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3146_ = v_traceState_3131_;
v_isShared_3147_ = v_isSharedCheck_3157_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_traces_3144_);
lean_dec(v_traceState_3131_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3157_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3148_; lean_object* v___x_3150_; 
v___x_3148_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3079_, v_traces_3144_);
lean_dec_ref(v_traces_3144_);
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 0, v___x_3148_);
v___x_3150_ = v___x_3146_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3148_);
lean_ctor_set_uint64(v_reuseFailAlloc_3156_, sizeof(void*)*1, v_tid_3143_);
v___x_3150_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
lean_object* v___x_3152_; 
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 4, v___x_3150_);
v___x_3152_ = v___x_3141_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_env_3132_);
lean_ctor_set(v_reuseFailAlloc_3155_, 1, v_nextMacroScope_3133_);
lean_ctor_set(v_reuseFailAlloc_3155_, 2, v_ngen_3134_);
lean_ctor_set(v_reuseFailAlloc_3155_, 3, v_auxDeclNGen_3135_);
lean_ctor_set(v_reuseFailAlloc_3155_, 4, v___x_3150_);
lean_ctor_set(v_reuseFailAlloc_3155_, 5, v_cache_3136_);
lean_ctor_set(v_reuseFailAlloc_3155_, 6, v_messages_3137_);
lean_ctor_set(v_reuseFailAlloc_3155_, 7, v_infoState_3138_);
lean_ctor_set(v_reuseFailAlloc_3155_, 8, v_snapshotTasks_3139_);
v___x_3152_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = lean_st_ref_put(v___y_3090_, v___x_3152_);
v___x_3154_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_fst_3092_);
return v___x_3154_;
}
}
}
}
}
else
{
goto v___jp_3123_;
}
}
else
{
goto v___jp_3123_;
}
}
v___jp_3159_:
{
double v___x_3161_; double v___x_3162_; double v___x_3163_; uint8_t v___x_3164_; 
v___x_3161_ = lean_unbox_float(v_snd_3109_);
v___x_3162_ = lean_unbox_float(v_fst_3108_);
v___x_3163_ = lean_float_sub(v___x_3161_, v___x_3162_);
v___x_3164_ = lean_float_decLt(v___y_3160_, v___x_3163_);
v___y_3129_ = v___x_3164_;
goto v___jp_3128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___boxed(lean_object** _args){
lean_object* v_cls_3175_ = _args[0];
lean_object* v_collapsed_3176_ = _args[1];
lean_object* v_tag_3177_ = _args[2];
lean_object* v_opts_3178_ = _args[3];
lean_object* v_clsEnabled_3179_ = _args[4];
lean_object* v_oldTraces_3180_ = _args[5];
lean_object* v_msg_3181_ = _args[6];
lean_object* v_resStartStop_3182_ = _args[7];
lean_object* v___y_3183_ = _args[8];
lean_object* v___y_3184_ = _args[9];
lean_object* v___y_3185_ = _args[10];
lean_object* v___y_3186_ = _args[11];
lean_object* v___y_3187_ = _args[12];
lean_object* v___y_3188_ = _args[13];
lean_object* v___y_3189_ = _args[14];
lean_object* v___y_3190_ = _args[15];
lean_object* v___y_3191_ = _args[16];
lean_object* v___y_3192_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3193_; uint8_t v_clsEnabled_boxed_3194_; lean_object* v_res_3195_; 
v_collapsed_boxed_3193_ = lean_unbox(v_collapsed_3176_);
v_clsEnabled_boxed_3194_ = lean_unbox(v_clsEnabled_3179_);
v_res_3195_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_3175_, v_collapsed_boxed_3193_, v_tag_3177_, v_opts_3178_, v_clsEnabled_boxed_3194_, v_oldTraces_3180_, v_msg_3181_, v_resStartStop_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v_opts_3178_);
return v_res_3195_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3(void){
_start:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3201_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2));
v___x_3202_ = l_Lean_stringToMessageData(v___x_3201_);
return v___x_3202_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5(void){
_start:
{
lean_object* v___x_3204_; double v___x_3205_; 
v___x_3204_ = lean_unsigned_to_nat(1000000000u);
v___x_3205_ = lean_float_of_nat(v___x_3204_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(lean_object* v_P_3206_, lean_object* v_lhs_3207_, lean_object* v_rhs_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_){
_start:
{
uint8_t v___y_3220_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v_options_3242_; lean_object* v_inheritedTraceOptions_3243_; uint8_t v_hasTrace_3244_; lean_object* v_cls_3245_; lean_object* v___f_3246_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; uint8_t v_____do__lift_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; 
v_options_3242_ = lean_ctor_get(v_a_3216_, 2);
v_inheritedTraceOptions_3243_ = lean_ctor_get(v_a_3216_, 13);
v_hasTrace_3244_ = lean_ctor_get_uint8(v_options_3242_, sizeof(void*)*1);
v_cls_3245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___f_3246_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1));
if (v_hasTrace_3244_ == 0)
{
lean_object* v___x_3370_; lean_object* v_a_3371_; uint8_t v___x_3372_; 
v___x_3370_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3245_, v_inheritedTraceOptions_3243_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_);
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_a_3371_);
lean_dec_ref(v___x_3370_);
v___x_3372_ = lean_unbox(v_a_3371_);
lean_dec(v_a_3371_);
v_____do__lift_3347_ = v___x_3372_;
v___y_3348_ = v_a_3209_;
v___y_3349_ = v_a_3210_;
v___y_3350_ = v_a_3211_;
v___y_3351_ = v_a_3212_;
v___y_3352_ = v_a_3213_;
v___y_3353_ = v_a_3214_;
v___y_3354_ = v_a_3215_;
v___y_3355_ = v_a_3216_;
v___y_3356_ = v_a_3217_;
goto v___jp_3346_;
}
else
{
lean_object* v___f_3373_; uint8_t v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; uint8_t v___x_3377_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v_a_3381_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v_a_3393_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v_a_3411_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v_a_3426_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; 
v___f_3373_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4));
v___x_3374_ = 0;
v___x_3375_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_3376_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3377_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3243_, v_options_3242_, v___x_3376_);
if (v___x_3377_ == 0)
{
lean_object* v___x_3474_; uint8_t v___x_3475_; 
v___x_3474_ = l_Lean_trace_profiler;
v___x_3475_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_3242_, v___x_3474_);
if (v___x_3475_ == 0)
{
lean_object* v___x_3476_; lean_object* v_a_3477_; uint8_t v___x_3478_; 
v___x_3476_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3245_, v_inheritedTraceOptions_3243_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_);
v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
lean_inc(v_a_3477_);
lean_dec_ref(v___x_3476_);
v___x_3478_ = lean_unbox(v_a_3477_);
lean_dec(v_a_3477_);
v_____do__lift_3347_ = v___x_3478_;
v___y_3348_ = v_a_3209_;
v___y_3349_ = v_a_3210_;
v___y_3350_ = v_a_3211_;
v___y_3351_ = v_a_3212_;
v___y_3352_ = v_a_3213_;
v___y_3353_ = v_a_3214_;
v___y_3354_ = v_a_3215_;
v___y_3355_ = v_a_3216_;
v___y_3356_ = v_a_3217_;
goto v___jp_3346_;
}
else
{
goto v___jp_3441_;
}
}
else
{
goto v___jp_3441_;
}
v___jp_3378_:
{
lean_object* v___x_3382_; double v___x_3383_; double v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3382_ = lean_io_get_num_heartbeats();
v___x_3383_ = lean_float_of_nat(v___y_3380_);
v___x_3384_ = lean_float_of_nat(v___x_3382_);
v___x_3385_ = lean_box_float(v___x_3383_);
v___x_3386_ = lean_box_float(v___x_3384_);
v___x_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3385_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
v___x_3388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3388_, 0, v_a_3381_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
v___x_3389_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_3245_, v___x_3374_, v___x_3375_, v_options_3242_, v___x_3377_, v___y_3379_, v___f_3373_, v___x_3388_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_);
return v___x_3389_;
}
v___jp_3390_:
{
lean_object* v___x_3394_; 
v___x_3394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3394_, 0, v_a_3393_);
v___y_3379_ = v___y_3391_;
v___y_3380_ = v___y_3392_;
v_a_3381_ = v___x_3394_;
goto v___jp_3378_;
}
v___jp_3395_:
{
if (lean_obj_tag(v___y_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
v_a_3399_ = lean_ctor_get(v___y_3398_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___y_3398_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___y_3398_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___y_3398_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
lean_ctor_set_tag(v___x_3401_, 1);
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
v___y_3379_ = v___y_3396_;
v___y_3380_ = v___y_3397_;
v_a_3381_ = v___x_3404_;
goto v___jp_3378_;
}
}
}
else
{
lean_object* v_a_3407_; 
v_a_3407_ = lean_ctor_get(v___y_3398_, 0);
lean_inc(v_a_3407_);
lean_dec_ref_known(v___y_3398_, 1);
v___y_3391_ = v___y_3396_;
v___y_3392_ = v___y_3397_;
v_a_3393_ = v_a_3407_;
goto v___jp_3390_;
}
}
v___jp_3408_:
{
lean_object* v___x_3412_; double v___x_3413_; double v___x_3414_; double v___x_3415_; double v___x_3416_; double v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3412_ = lean_io_mono_nanos_now();
v___x_3413_ = lean_float_of_nat(v___y_3409_);
v___x_3414_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5);
v___x_3415_ = lean_float_div(v___x_3413_, v___x_3414_);
v___x_3416_ = lean_float_of_nat(v___x_3412_);
v___x_3417_ = lean_float_div(v___x_3416_, v___x_3414_);
v___x_3418_ = lean_box_float(v___x_3415_);
v___x_3419_ = lean_box_float(v___x_3417_);
v___x_3420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3418_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3421_, 0, v_a_3411_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_3245_, v___x_3374_, v___x_3375_, v_options_3242_, v___x_3377_, v___y_3410_, v___f_3373_, v___x_3421_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_);
return v___x_3422_;
}
v___jp_3423_:
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3427_, 0, v_a_3426_);
v___y_3409_ = v___y_3424_;
v___y_3410_ = v___y_3425_;
v_a_3411_ = v___x_3427_;
goto v___jp_3408_;
}
v___jp_3428_:
{
if (lean_obj_tag(v___y_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
v_a_3432_ = lean_ctor_get(v___y_3431_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___y_3431_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3434_ = v___y_3431_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___y_3431_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set_tag(v___x_3434_, 1);
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3432_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
v___y_3409_ = v___y_3429_;
v___y_3410_ = v___y_3430_;
v_a_3411_ = v___x_3437_;
goto v___jp_3408_;
}
}
}
else
{
lean_object* v_a_3440_; 
v_a_3440_ = lean_ctor_get(v___y_3431_, 0);
lean_inc(v_a_3440_);
lean_dec_ref_known(v___y_3431_, 1);
v___y_3424_ = v___y_3429_;
v___y_3425_ = v___y_3430_;
v_a_3426_ = v_a_3440_;
goto v___jp_3423_;
}
}
v___jp_3441_:
{
lean_object* v___x_3442_; lean_object* v_a_3443_; lean_object* v___x_3444_; uint8_t v___x_3445_; 
v___x_3442_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v_a_3217_);
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_a_3443_);
lean_dec_ref(v___x_3442_);
v___x_3444_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3445_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_3242_, v___x_3444_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v_a_3448_; uint8_t v___x_3449_; 
v___x_3446_ = lean_io_mono_nanos_now();
v___x_3447_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3245_, v_inheritedTraceOptions_3243_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_);
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_a_3448_);
lean_dec_ref(v___x_3447_);
v___x_3449_ = lean_unbox(v_a_3448_);
lean_dec(v_a_3448_);
if (v___x_3449_ == 0)
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3450_ = lean_box(0);
v___x_3451_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_3207_, v_rhs_3208_, v___x_3445_, v___f_3246_, v_cls_3245_, v_P_3206_, v___x_3450_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_);
v___y_3429_ = v___x_3446_;
v___y_3430_ = v_a_3443_;
v___y_3431_ = v___x_3451_;
goto v___jp_3428_;
}
else
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3452_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_3208_);
lean_inc_ref(v_lhs_3207_);
lean_inc_ref(v_P_3206_);
v___x_3453_ = l_Lean_mkAppB(v_P_3206_, v_lhs_3207_, v_rhs_3208_);
v___x_3454_ = l_Lean_indentExpr(v___x_3453_);
v___x_3455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3452_);
lean_ctor_set(v___x_3455_, 1, v___x_3454_);
v___x_3456_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3245_, v___x_3455_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3458_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_a_3457_);
lean_dec_ref_known(v___x_3456_, 1);
v___x_3458_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_3207_, v_rhs_3208_, v___x_3445_, v___f_3246_, v_cls_3245_, v_P_3206_, v_a_3457_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_);
v___y_3429_ = v___x_3446_;
v___y_3430_ = v_a_3443_;
v___y_3431_ = v___x_3458_;
goto v___jp_3428_;
}
else
{
lean_object* v_a_3459_; 
lean_dec_ref(v_rhs_3208_);
lean_dec_ref(v_lhs_3207_);
lean_dec_ref(v_P_3206_);
v_a_3459_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_a_3459_);
lean_dec_ref_known(v___x_3456_, 1);
v___y_3424_ = v___x_3446_;
v___y_3425_ = v_a_3443_;
v_a_3426_ = v_a_3459_;
goto v___jp_3423_;
}
}
}
else
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v_a_3462_; uint8_t v___x_3463_; 
v___x_3460_ = lean_io_get_num_heartbeats();
v___x_3461_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3245_, v_inheritedTraceOptions_3243_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_);
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref(v___x_3461_);
v___x_3463_ = lean_unbox(v_a_3462_);
lean_dec(v_a_3462_);
if (v___x_3463_ == 0)
{
lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3464_ = lean_box(0);
v___x_3465_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_3207_, v_rhs_3208_, v_P_3206_, v_cls_3245_, v___x_3445_, v___f_3246_, v___x_3374_, v___x_3464_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_);
v___y_3396_ = v_a_3443_;
v___y_3397_ = v___x_3460_;
v___y_3398_ = v___x_3465_;
goto v___jp_3395_;
}
else
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3466_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_3208_);
lean_inc_ref(v_lhs_3207_);
lean_inc_ref(v_P_3206_);
v___x_3467_ = l_Lean_mkAppB(v_P_3206_, v_lhs_3207_, v_rhs_3208_);
v___x_3468_ = l_Lean_indentExpr(v___x_3467_);
v___x_3469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3466_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
v___x_3470_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3245_, v___x_3469_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3471_; lean_object* v___x_3472_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3471_);
lean_dec_ref_known(v___x_3470_, 1);
v___x_3472_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_3207_, v_rhs_3208_, v_P_3206_, v_cls_3245_, v___x_3445_, v___f_3246_, v___x_3374_, v_a_3471_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_);
v___y_3396_ = v_a_3443_;
v___y_3397_ = v___x_3460_;
v___y_3398_ = v___x_3472_;
goto v___jp_3395_;
}
else
{
lean_object* v_a_3473_; 
lean_dec_ref(v_rhs_3208_);
lean_dec_ref(v_lhs_3207_);
lean_dec_ref(v_P_3206_);
v_a_3473_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3473_);
lean_dec_ref_known(v___x_3470_, 1);
v___y_3391_ = v_a_3443_;
v___y_3392_ = v___x_3460_;
v_a_3393_ = v_a_3473_;
goto v___jp_3390_;
}
}
}
}
}
v___jp_3219_:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3221_, 0, v___y_3220_);
lean_ctor_set_uint8(v___x_3221_, 1, v___y_3220_);
v___x_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
return v___x_3222_;
}
v___jp_3223_:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
return v___x_3225_;
}
v___jp_3226_:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_3228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
return v___x_3228_;
}
v___jp_3229_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3238_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7);
v___x_3239_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8));
v___x_3240_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3240_, 0, v___y_3231_);
lean_ctor_set(v___x_3240_, 1, v___x_3238_);
lean_ctor_set(v___x_3240_, 2, v___x_3239_);
v___x_3241_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___y_3230_, v___x_3240_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3241_;
}
v___jp_3247_:
{
lean_object* v___x_3257_; 
lean_inc_ref(v_lhs_3207_);
v___x_3257_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_3207_);
if (lean_obj_tag(v___x_3257_) == 1)
{
lean_object* v_val_3258_; lean_object* v___x_3259_; 
v_val_3258_ = lean_ctor_get(v___x_3257_, 0);
lean_inc(v_val_3258_);
lean_dec_ref_known(v___x_3257_, 1);
lean_inc_ref(v_rhs_3208_);
v___x_3259_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_3208_);
if (lean_obj_tag(v___x_3259_) == 1)
{
lean_object* v_val_3260_; uint8_t v___x_3261_; 
v_val_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_val_3260_);
lean_dec_ref_known(v___x_3259_, 1);
v___x_3261_ = lean_expr_eqv(v_val_3258_, v_val_3260_);
if (v___x_3261_ == 0)
{
lean_object* v_inheritedTraceOptions_3262_; lean_object* v___x_3263_; lean_object* v_a_3264_; uint8_t v___x_3265_; 
lean_dec_ref(v_P_3206_);
v_inheritedTraceOptions_3262_ = lean_ctor_get(v___y_3255_, 13);
v___x_3263_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3245_, v_inheritedTraceOptions_3262_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_a_3264_);
lean_dec_ref(v___x_3263_);
v___x_3265_ = lean_unbox(v_a_3264_);
lean_dec(v_a_3264_);
if (v___x_3265_ == 0)
{
lean_dec(v_val_3260_);
lean_dec(v_val_3258_);
lean_dec_ref(v_rhs_3208_);
lean_dec_ref(v_lhs_3207_);
v___y_3220_ = v___x_3261_;
goto v___jp_3219_;
}
else
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3266_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1);
v___x_3267_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3258_);
v___x_3268_ = l_Lean_MessageData_ofExpr(v___x_3267_);
v___x_3269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3266_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
v___x_3270_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3);
v___x_3271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3269_);
lean_ctor_set(v___x_3271_, 1, v___x_3270_);
v___x_3272_ = l_Lean_indentExpr(v_lhs_3207_);
v___x_3273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3271_);
lean_ctor_set(v___x_3273_, 1, v___x_3272_);
v___x_3274_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5);
v___x_3275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3273_);
lean_ctor_set(v___x_3275_, 1, v___x_3274_);
v___x_3276_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3260_);
v___x_3277_ = l_Lean_MessageData_ofExpr(v___x_3276_);
v___x_3278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3275_);
lean_ctor_set(v___x_3278_, 1, v___x_3277_);
v___x_3279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
lean_ctor_set(v___x_3279_, 1, v___x_3270_);
v___x_3280_ = l_Lean_indentExpr(v_rhs_3208_);
v___x_3281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3279_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
v___x_3282_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3245_, v___x_3281_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_dec_ref_known(v___x_3282_, 1);
v___y_3220_ = v___x_3261_;
goto v___jp_3219_;
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3282_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3282_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
}
else
{
lean_object* v_options_3291_; lean_object* v_inheritedTraceOptions_3292_; uint8_t v_hasTrace_3293_; uint8_t v___x_3294_; lean_object* v___x_3295_; lean_object* v___f_3296_; 
lean_dec(v_val_3260_);
v_options_3291_ = lean_ctor_get(v___y_3255_, 2);
v_inheritedTraceOptions_3292_ = lean_ctor_get(v___y_3255_, 13);
v_hasTrace_3293_ = lean_ctor_get_uint8(v_options_3291_, sizeof(void*)*1);
v___x_3294_ = 0;
v___x_3295_ = lean_box(v___x_3294_);
lean_inc(v_val_3258_);
v___f_3296_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 13, 5);
lean_closure_set(v___f_3296_, 0, v_val_3258_);
lean_closure_set(v___f_3296_, 1, v_lhs_3207_);
lean_closure_set(v___f_3296_, 2, v_rhs_3208_);
lean_closure_set(v___f_3296_, 3, v_P_3206_);
lean_closure_set(v___f_3296_, 4, v___x_3295_);
if (v_hasTrace_3293_ == 0)
{
v___y_3230_ = v___f_3296_;
v___y_3231_ = v_val_3258_;
v___y_3232_ = v___y_3251_;
v___y_3233_ = v___y_3252_;
v___y_3234_ = v___y_3253_;
v___y_3235_ = v___y_3254_;
v___y_3236_ = v___y_3255_;
v___y_3237_ = v___y_3256_;
goto v___jp_3229_;
}
else
{
lean_object* v___x_3297_; uint8_t v___x_3298_; 
v___x_3297_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3298_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3292_, v_options_3291_, v___x_3297_);
if (v___x_3298_ == 0)
{
v___y_3230_ = v___f_3296_;
v___y_3231_ = v_val_3258_;
v___y_3232_ = v___y_3251_;
v___y_3233_ = v___y_3252_;
v___y_3234_ = v___y_3253_;
v___y_3235_ = v___y_3254_;
v___y_3236_ = v___y_3255_;
v___y_3237_ = v___y_3256_;
goto v___jp_3229_;
}
else
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3299_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10);
lean_inc(v_val_3258_);
v___x_3300_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3258_);
v___x_3301_ = l_Lean_MessageData_ofExpr(v___x_3300_);
v___x_3302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3299_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12);
v___x_3304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3302_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3245_, v___x_3304_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_dec_ref_known(v___x_3305_, 1);
v___y_3230_ = v___f_3296_;
v___y_3231_ = v_val_3258_;
v___y_3232_ = v___y_3251_;
v___y_3233_ = v___y_3252_;
v___y_3234_ = v___y_3253_;
v___y_3235_ = v___y_3254_;
v___y_3236_ = v___y_3255_;
v___y_3237_ = v___y_3256_;
goto v___jp_3229_;
}
else
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
lean_dec_ref(v___f_3296_);
lean_dec(v_val_3258_);
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3308_ = v___x_3305_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3305_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_3314_; lean_object* v___x_3315_; lean_object* v_a_3316_; uint8_t v___x_3317_; 
lean_dec(v___x_3259_);
lean_dec(v_val_3258_);
lean_dec_ref(v_lhs_3207_);
lean_dec_ref(v_P_3206_);
v_inheritedTraceOptions_3314_ = lean_ctor_get(v___y_3255_, 13);
v___x_3315_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3245_, v_inheritedTraceOptions_3314_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_a_3316_);
lean_dec_ref(v___x_3315_);
v___x_3317_ = lean_unbox(v_a_3316_);
lean_dec(v_a_3316_);
if (v___x_3317_ == 0)
{
lean_dec_ref(v_rhs_3208_);
goto v___jp_3226_;
}
else
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3318_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14);
v___x_3319_ = l_Lean_indentExpr(v_rhs_3208_);
v___x_3320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3318_);
lean_ctor_set(v___x_3320_, 1, v___x_3319_);
v___x_3321_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3245_, v___x_3320_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_dec_ref_known(v___x_3321_, 1);
goto v___jp_3226_;
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v___x_3321_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3321_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_3330_; lean_object* v___x_3331_; lean_object* v_a_3332_; uint8_t v___x_3333_; 
lean_dec(v___x_3257_);
lean_dec_ref(v_rhs_3208_);
lean_dec_ref(v_P_3206_);
v_inheritedTraceOptions_3330_ = lean_ctor_get(v___y_3255_, 13);
v___x_3331_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3245_, v_inheritedTraceOptions_3330_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
lean_inc(v_a_3332_);
lean_dec_ref(v___x_3331_);
v___x_3333_ = lean_unbox(v_a_3332_);
lean_dec(v_a_3332_);
if (v___x_3333_ == 0)
{
lean_dec_ref(v_lhs_3207_);
goto v___jp_3223_;
}
else
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3334_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14);
v___x_3335_ = l_Lean_indentExpr(v_lhs_3207_);
v___x_3336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3334_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
v___x_3337_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3245_, v___x_3336_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_dec_ref_known(v___x_3337_, 1);
goto v___jp_3223_;
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
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
}
}
v___jp_3346_:
{
if (v_____do__lift_3347_ == 0)
{
v___y_3248_ = v___y_3348_;
v___y_3249_ = v___y_3349_;
v___y_3250_ = v___y_3350_;
v___y_3251_ = v___y_3351_;
v___y_3252_ = v___y_3352_;
v___y_3253_ = v___y_3353_;
v___y_3254_ = v___y_3354_;
v___y_3255_ = v___y_3355_;
v___y_3256_ = v___y_3356_;
goto v___jp_3247_;
}
else
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3357_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_3208_);
lean_inc_ref(v_lhs_3207_);
lean_inc_ref(v_P_3206_);
v___x_3358_ = l_Lean_mkAppB(v_P_3206_, v_lhs_3207_, v_rhs_3208_);
v___x_3359_ = l_Lean_indentExpr(v___x_3358_);
v___x_3360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3357_);
lean_ctor_set(v___x_3360_, 1, v___x_3359_);
v___x_3361_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3245_, v___x_3360_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_dec_ref_known(v___x_3361_, 1);
v___y_3248_ = v___y_3348_;
v___y_3249_ = v___y_3349_;
v___y_3250_ = v___y_3350_;
v___y_3251_ = v___y_3351_;
v___y_3252_ = v___y_3352_;
v___y_3253_ = v___y_3353_;
v___y_3254_ = v___y_3354_;
v___y_3255_ = v___y_3355_;
v___y_3256_ = v___y_3356_;
goto v___jp_3247_;
}
else
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
lean_dec_ref(v_rhs_3208_);
lean_dec_ref(v_lhs_3207_);
lean_dec_ref(v_P_3206_);
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___x_3361_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3361_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___boxed(lean_object* v_P_3479_, lean_object* v_lhs_3480_, lean_object* v_rhs_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v_P_3479_, v_lhs_3480_, v_rhs_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
lean_dec(v_a_3490_);
lean_dec_ref(v_a_3489_);
lean_dec(v_a_3488_);
lean_dec_ref(v_a_3487_);
lean_dec(v_a_3486_);
lean_dec_ref(v_a_3485_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
lean_dec(v_a_3482_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(lean_object* v_cls_3493_, lean_object* v_msg_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3493_, v_msg_3494_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object* v_cls_3506_, lean_object* v_msg_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(v_cls_3506_, v_msg_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3508_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(lean_object* v_00_u03b1_3519_, lean_object* v_x_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v___x_3531_; 
v___x_3531_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_3520_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___boxed(lean_object* v_00_u03b1_3532_, lean_object* v_x_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(v_00_u03b1_3532_, v_x_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3534_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(lean_object* v_oldTraces_3545_, lean_object* v_data_3546_, lean_object* v_ref_3547_, lean_object* v_msg_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
lean_object* v___x_3559_; 
v___x_3559_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_3545_, v_data_3546_, v_ref_3547_, v_msg_3548_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___boxed(lean_object* v_oldTraces_3560_, lean_object* v_data_3561_, lean_object* v_ref_3562_, lean_object* v_msg_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(v_oldTraces_3560_, v_data_3561_, v_ref_3562_, v_msg_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v___y_3564_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(lean_object* v_x_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0___boxed(lean_object* v_x_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v_x_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(lean_object* v_arg_3605_, lean_object* v_arg_3606_, lean_object* v_arg_3607_, lean_object* v_arg_3608_, lean_object* v_____r_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
lean_object* v___x_3620_; 
lean_inc_ref(v_arg_3605_);
v___x_3620_ = l_Lean_Meta_getDecLevel(v_arg_3605_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_a_3621_);
lean_dec_ref_known(v___x_3620_, 1);
v___x_3622_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2));
v___x_3623_ = lean_box(0);
v___x_3624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3624_, 0, v_a_3621_);
lean_ctor_set(v___x_3624_, 1, v___x_3623_);
v___x_3625_ = l_Lean_Expr_const___override(v___x_3622_, v___x_3624_);
v___x_3626_ = l_Lean_mkAppB(v___x_3625_, v_arg_3605_, v_arg_3606_);
v___x_3627_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3626_, v_arg_3607_, v_arg_3608_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_);
return v___x_3627_;
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_dec_ref(v_arg_3608_);
lean_dec_ref(v_arg_3607_);
lean_dec_ref(v_arg_3606_);
lean_dec_ref(v_arg_3605_);
v_a_3628_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3620_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3620_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___boxed(lean_object* v_arg_3636_, lean_object* v_arg_3637_, lean_object* v_arg_3638_, lean_object* v_arg_3639_, lean_object* v_____r_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3636_, v_arg_3637_, v_arg_3638_, v_arg_3639_, v_____r_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec(v___y_3641_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(lean_object* v_arg_3655_, lean_object* v_arg_3656_, lean_object* v_arg_3657_, lean_object* v_____r_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_){
_start:
{
lean_object* v___x_3669_; 
lean_inc_ref(v_arg_3655_);
v___x_3669_ = l_Lean_Meta_getLevel(v_arg_3655_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_a_3670_);
lean_dec_ref_known(v___x_3669_, 1);
v___x_3671_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1));
v___x_3672_ = lean_box(0);
v___x_3673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3673_, 0, v_a_3670_);
lean_ctor_set(v___x_3673_, 1, v___x_3672_);
v___x_3674_ = l_Lean_Expr_const___override(v___x_3671_, v___x_3673_);
v___x_3675_ = l_Lean_Expr_app___override(v___x_3674_, v_arg_3655_);
v___x_3676_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3675_, v_arg_3656_, v_arg_3657_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
return v___x_3676_;
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
lean_dec_ref(v_arg_3657_);
lean_dec_ref(v_arg_3656_);
lean_dec_ref(v_arg_3655_);
v_a_3677_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3669_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3669_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___boxed(lean_object* v_arg_3685_, lean_object* v_arg_3686_, lean_object* v_arg_3687_, lean_object* v_____r_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3685_, v_arg_3686_, v_arg_3687_, v_____r_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec(v___y_3689_);
return v_res_3699_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1(void){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3701_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0));
v___x_3702_ = l_Lean_stringToMessageData(v___x_3701_);
return v___x_3702_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2(void){
_start:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3703_ = l_Lean_checkEmoji;
v___x_3704_ = l_Lean_stringToMessageData(v___x_3703_);
return v___x_3704_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3(void){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3705_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2);
v___x_3706_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1);
v___x_3707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3706_);
lean_ctor_set(v___x_3707_, 1, v___x_3705_);
return v___x_3707_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5(void){
_start:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3709_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4));
v___x_3710_ = l_Lean_stringToMessageData(v___x_3709_);
return v___x_3710_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6(void){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3711_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5);
v___x_3712_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3);
v___x_3713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
lean_ctor_set(v___x_3713_, 1, v___x_3711_);
return v___x_3713_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8(void){
_start:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3715_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7));
v___x_3716_ = l_Lean_stringToMessageData(v___x_3715_);
return v___x_3716_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9(void){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3717_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8);
v___x_3718_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3);
v___x_3719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3718_);
lean_ctor_set(v___x_3719_, 1, v___x_3717_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(lean_object* v_e_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_){
_start:
{
lean_object* v___y_3732_; lean_object* v___x_3764_; 
v___x_3764_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3720_, v_a_3727_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3765_; lean_object* v___x_3766_; uint8_t v___x_3767_; 
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
lean_inc(v_a_3765_);
lean_dec_ref_known(v___x_3764_, 1);
v___x_3766_ = l_Lean_Expr_cleanupAnnotations(v_a_3765_);
v___x_3767_ = l_Lean_Expr_isApp(v___x_3766_);
if (v___x_3767_ == 0)
{
lean_object* v___x_3768_; lean_object* v___x_3769_; 
lean_dec_ref(v___x_3766_);
v___x_3768_ = lean_box(0);
v___x_3769_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3768_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
v___y_3732_ = v___x_3769_;
goto v___jp_3731_;
}
else
{
lean_object* v_arg_3770_; lean_object* v___x_3771_; uint8_t v___x_3772_; 
v_arg_3770_ = lean_ctor_get(v___x_3766_, 1);
lean_inc_ref(v_arg_3770_);
v___x_3771_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3766_);
v___x_3772_ = l_Lean_Expr_isApp(v___x_3771_);
if (v___x_3772_ == 0)
{
lean_object* v___x_3773_; lean_object* v___x_3774_; 
lean_dec_ref(v___x_3771_);
lean_dec_ref(v_arg_3770_);
v___x_3773_ = lean_box(0);
v___x_3774_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3773_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
v___y_3732_ = v___x_3774_;
goto v___jp_3731_;
}
else
{
lean_object* v_arg_3775_; lean_object* v___x_3776_; uint8_t v___x_3777_; 
v_arg_3775_ = lean_ctor_get(v___x_3771_, 1);
lean_inc_ref(v_arg_3775_);
v___x_3776_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3771_);
v___x_3777_ = l_Lean_Expr_isApp(v___x_3776_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
lean_dec_ref(v___x_3776_);
lean_dec_ref(v_arg_3775_);
lean_dec_ref(v_arg_3770_);
v___x_3778_ = lean_box(0);
v___x_3779_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3778_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
v___y_3732_ = v___x_3779_;
goto v___jp_3731_;
}
else
{
lean_object* v_arg_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v_arg_3780_ = lean_ctor_get(v___x_3776_, 1);
lean_inc_ref(v_arg_3780_);
v___x_3781_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3776_);
v___x_3782_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1));
v___x_3783_ = l_Lean_Expr_isConstOf(v___x_3781_, v___x_3782_);
if (v___x_3783_ == 0)
{
uint8_t v___x_3784_; 
v___x_3784_ = l_Lean_Expr_isApp(v___x_3781_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
lean_dec_ref(v___x_3781_);
lean_dec_ref(v_arg_3780_);
lean_dec_ref(v_arg_3775_);
lean_dec_ref(v_arg_3770_);
v___x_3785_ = lean_box(0);
v___x_3786_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3785_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
v___y_3732_ = v___x_3786_;
goto v___jp_3731_;
}
else
{
lean_object* v_arg_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; uint8_t v___x_3790_; 
v_arg_3787_ = lean_ctor_get(v___x_3781_, 1);
lean_inc_ref(v_arg_3787_);
v___x_3788_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3781_);
v___x_3789_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2));
v___x_3790_ = l_Lean_Expr_isConstOf(v___x_3788_, v___x_3789_);
lean_dec_ref(v___x_3788_);
if (v___x_3790_ == 0)
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
lean_dec_ref(v_arg_3787_);
lean_dec_ref(v_arg_3780_);
lean_dec_ref(v_arg_3775_);
lean_dec_ref(v_arg_3770_);
v___x_3791_ = lean_box(0);
v___x_3792_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3791_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
v___y_3732_ = v___x_3792_;
goto v___jp_3731_;
}
else
{
lean_object* v_options_3793_; lean_object* v_inheritedTraceOptions_3794_; uint8_t v_hasTrace_3795_; 
v_options_3793_ = lean_ctor_get(v_a_3728_, 2);
v_inheritedTraceOptions_3794_ = lean_ctor_get(v_a_3728_, 13);
v_hasTrace_3795_ = lean_ctor_get_uint8(v_options_3793_, sizeof(void*)*1);
if (v_hasTrace_3795_ == 0)
{
goto v___jp_3796_;
}
else
{
lean_object* v___x_3799_; lean_object* v___x_3800_; uint8_t v___x_3801_; 
v___x_3799_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3800_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3801_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3794_, v_options_3793_, v___x_3800_);
if (v___x_3801_ == 0)
{
goto v___jp_3796_;
}
else
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3802_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6);
v___x_3803_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3799_, v___x_3802_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; lean_object* v___x_3805_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3804_);
lean_dec_ref_known(v___x_3803_, 1);
v___x_3805_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3787_, v_arg_3780_, v_arg_3775_, v_arg_3770_, v_a_3804_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
v___y_3732_ = v___x_3805_;
goto v___jp_3731_;
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_dec_ref(v_arg_3787_);
lean_dec_ref(v_arg_3780_);
lean_dec_ref(v_arg_3775_);
lean_dec_ref(v_arg_3770_);
v_a_3806_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3803_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3803_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
v___jp_3796_:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3797_ = lean_box(0);
v___x_3798_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3787_, v_arg_3780_, v_arg_3775_, v_arg_3770_, v___x_3797_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
v___y_3732_ = v___x_3798_;
goto v___jp_3731_;
}
}
}
}
else
{
lean_object* v_options_3814_; lean_object* v_inheritedTraceOptions_3815_; uint8_t v_hasTrace_3816_; 
lean_dec_ref(v___x_3781_);
v_options_3814_ = lean_ctor_get(v_a_3728_, 2);
v_inheritedTraceOptions_3815_ = lean_ctor_get(v_a_3728_, 13);
v_hasTrace_3816_ = lean_ctor_get_uint8(v_options_3814_, sizeof(void*)*1);
if (v_hasTrace_3816_ == 0)
{
goto v___jp_3817_;
}
else
{
lean_object* v___x_3820_; lean_object* v___x_3821_; uint8_t v___x_3822_; 
v___x_3820_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3821_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3822_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3815_, v_options_3814_, v___x_3821_);
if (v___x_3822_ == 0)
{
goto v___jp_3817_;
}
else
{
lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3823_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9);
v___x_3824_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3820_, v___x_3823_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; lean_object* v___x_3826_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3825_);
lean_dec_ref_known(v___x_3824_, 1);
v___x_3826_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3780_, v_arg_3775_, v_arg_3770_, v_a_3825_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
v___y_3732_ = v___x_3826_;
goto v___jp_3731_;
}
else
{
lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3834_; 
lean_dec_ref(v_arg_3780_);
lean_dec_ref(v_arg_3775_);
lean_dec_ref(v_arg_3770_);
v_a_3827_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3829_ = v___x_3824_;
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v___x_3824_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3832_; 
if (v_isShared_3830_ == 0)
{
v___x_3832_ = v___x_3829_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_a_3827_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
}
}
v___jp_3817_:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; 
v___x_3818_ = lean_box(0);
v___x_3819_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3780_, v_arg_3775_, v_arg_3770_, v___x_3818_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
v___y_3732_ = v___x_3819_;
goto v___jp_3731_;
}
}
}
}
}
}
else
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3842_; 
v_a_3835_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3837_ = v___x_3764_;
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3764_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3840_; 
if (v_isShared_3838_ == 0)
{
v___x_3840_ = v___x_3837_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3835_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
v___jp_3731_:
{
if (lean_obj_tag(v___y_3732_) == 0)
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3763_; 
v_a_3733_ = lean_ctor_get(v___y_3732_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___y_3732_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3735_ = v___y_3732_;
v_isShared_3736_ = v_isSharedCheck_3763_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___y_3732_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3763_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
if (lean_obj_tag(v_a_3733_) == 0)
{
uint8_t v_contextDependent_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3748_; 
v_contextDependent_3737_ = lean_ctor_get_uint8(v_a_3733_, 1);
v_isSharedCheck_3748_ = !lean_is_exclusive(v_a_3733_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3739_ = v_a_3733_;
v_isShared_3740_ = v_isSharedCheck_3748_;
goto v_resetjp_3738_;
}
else
{
lean_dec(v_a_3733_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3748_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
uint8_t v___x_3741_; lean_object* v___x_3743_; 
v___x_3741_ = 1;
if (v_isShared_3740_ == 0)
{
v___x_3743_ = v___x_3739_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, 1, v_contextDependent_3737_);
v___x_3743_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
lean_object* v___x_3745_; 
lean_ctor_set_uint8(v___x_3743_, 0, v___x_3741_);
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 0, v___x_3743_);
v___x_3745_ = v___x_3735_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3743_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
}
else
{
lean_object* v_e_x27_3749_; lean_object* v_proof_3750_; uint8_t v_contextDependent_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3762_; 
v_e_x27_3749_ = lean_ctor_get(v_a_3733_, 0);
v_proof_3750_ = lean_ctor_get(v_a_3733_, 1);
v_contextDependent_3751_ = lean_ctor_get_uint8(v_a_3733_, sizeof(void*)*2 + 1);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_a_3733_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3753_ = v_a_3733_;
v_isShared_3754_ = v_isSharedCheck_3762_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_proof_3750_);
lean_inc(v_e_x27_3749_);
lean_dec(v_a_3733_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3762_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
uint8_t v___x_3755_; lean_object* v___x_3757_; 
v___x_3755_ = 1;
if (v_isShared_3754_ == 0)
{
v___x_3757_ = v___x_3753_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_e_x27_3749_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_proof_3750_);
lean_ctor_set_uint8(v_reuseFailAlloc_3761_, sizeof(void*)*2 + 1, v_contextDependent_3751_);
v___x_3757_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
lean_object* v___x_3759_; 
lean_ctor_set_uint8(v___x_3757_, sizeof(void*)*2, v___x_3755_);
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 0, v___x_3757_);
v___x_3759_ = v___x_3735_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
}
}
else
{
return v___y_3732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed(lean_object* v_e_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_){
_start:
{
lean_object* v_res_3854_; 
v_res_3854_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(v_e_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_);
lean_dec(v_a_3852_);
lean_dec_ref(v_a_3851_);
lean_dec(v_a_3850_);
lean_dec_ref(v_a_3849_);
lean_dec(v_a_3848_);
lean_dec_ref(v_a_3847_);
lean_dec(v_a_3846_);
lean_dec_ref(v_a_3845_);
lean_dec(v_a_3844_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(lean_object* v_x_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v___x_3868_; 
lean_inc(v___y_3862_);
lean_inc_ref(v___y_3861_);
lean_inc(v___y_3860_);
lean_inc_ref(v___y_3859_);
lean_inc(v___y_3858_);
lean_inc(v___y_3857_);
lean_inc_ref(v___y_3856_);
v___x_3868_ = lean_apply_12(v_x_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, lean_box(0));
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed(lean_object* v_x_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_){
_start:
{
lean_object* v_res_3882_; 
v_res_3882_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(v_x_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object* v_mvarId_3883_, lean_object* v_x_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_){
_start:
{
lean_object* v___f_3897_; lean_object* v___x_3898_; 
lean_inc(v___y_3891_);
lean_inc_ref(v___y_3890_);
lean_inc(v___y_3889_);
lean_inc_ref(v___y_3888_);
lean_inc(v___y_3887_);
lean_inc(v___y_3886_);
lean_inc_ref(v___y_3885_);
v___f_3897_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_3897_, 0, v_x_3884_);
lean_closure_set(v___f_3897_, 1, v___y_3885_);
lean_closure_set(v___f_3897_, 2, v___y_3886_);
lean_closure_set(v___f_3897_, 3, v___y_3887_);
lean_closure_set(v___f_3897_, 4, v___y_3888_);
lean_closure_set(v___f_3897_, 5, v___y_3889_);
lean_closure_set(v___f_3897_, 6, v___y_3890_);
lean_closure_set(v___f_3897_, 7, v___y_3891_);
v___x_3898_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3883_, v___f_3897_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_);
if (lean_obj_tag(v___x_3898_) == 0)
{
return v___x_3898_;
}
else
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3906_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3901_ = v___x_3898_;
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3898_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object* v_mvarId_3907_, lean_object* v_x_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_mvarId_3907_, v_x_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec(v___y_3915_);
lean_dec_ref(v___y_3914_);
lean_dec(v___y_3913_);
lean_dec_ref(v___y_3912_);
lean_dec(v___y_3911_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(lean_object* v_00_u03b1_3922_, lean_object* v_mvarId_3923_, lean_object* v_x_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
lean_object* v___x_3937_; 
v___x_3937_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_mvarId_3923_, v_x_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
return v___x_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object* v_00_u03b1_3938_, lean_object* v_mvarId_3939_, lean_object* v_x_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(v_00_u03b1_3938_, v_mvarId_3939_, v_x_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0(lean_object* v_x_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3965_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_3966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3965_);
return v___x_3966_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0___boxed(lean_object* v_x_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0(v_x_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v_x_3967_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(lean_object* v_snd_3979_, lean_object* v_a_3980_, lean_object* v___x_3981_, lean_object* v_____r_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_){
_start:
{
lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3995_ = lean_array_push(v_snd_3979_, v_a_3980_);
v___x_3996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3981_);
lean_ctor_set(v___x_3996_, 1, v___x_3995_);
v___x_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3996_);
v___x_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1___boxed(lean_object* v_snd_3999_, lean_object* v_a_4000_, lean_object* v___x_4001_, lean_object* v_____r_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(v_snd_3999_, v_a_4000_, v___x_4001_, v_____r_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec(v___y_4007_);
lean_dec_ref(v___y_4006_);
lean_dec(v___y_4005_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object* v_cls_4016_, lean_object* v_msg_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_){
_start:
{
lean_object* v_ref_4023_; lean_object* v___x_4024_; lean_object* v_a_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4069_; 
v_ref_4023_ = lean_ctor_get(v___y_4020_, 5);
v___x_4024_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_);
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4027_ = v___x_4024_;
v_isShared_4028_ = v_isSharedCheck_4069_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_a_4025_);
lean_dec(v___x_4024_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4069_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4029_; lean_object* v_traceState_4030_; lean_object* v_env_4031_; lean_object* v_nextMacroScope_4032_; lean_object* v_ngen_4033_; lean_object* v_auxDeclNGen_4034_; lean_object* v_cache_4035_; lean_object* v_messages_4036_; lean_object* v_infoState_4037_; lean_object* v_snapshotTasks_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4068_; 
v___x_4029_ = lean_st_ref_take(v___y_4021_);
v_traceState_4030_ = lean_ctor_get(v___x_4029_, 4);
v_env_4031_ = lean_ctor_get(v___x_4029_, 0);
v_nextMacroScope_4032_ = lean_ctor_get(v___x_4029_, 1);
v_ngen_4033_ = lean_ctor_get(v___x_4029_, 2);
v_auxDeclNGen_4034_ = lean_ctor_get(v___x_4029_, 3);
v_cache_4035_ = lean_ctor_get(v___x_4029_, 5);
v_messages_4036_ = lean_ctor_get(v___x_4029_, 6);
v_infoState_4037_ = lean_ctor_get(v___x_4029_, 7);
v_snapshotTasks_4038_ = lean_ctor_get(v___x_4029_, 8);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4040_ = v___x_4029_;
v_isShared_4041_ = v_isSharedCheck_4068_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_snapshotTasks_4038_);
lean_inc(v_infoState_4037_);
lean_inc(v_messages_4036_);
lean_inc(v_cache_4035_);
lean_inc(v_traceState_4030_);
lean_inc(v_auxDeclNGen_4034_);
lean_inc(v_ngen_4033_);
lean_inc(v_nextMacroScope_4032_);
lean_inc(v_env_4031_);
lean_dec(v___x_4029_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4068_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
uint64_t v_tid_4042_; lean_object* v_traces_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4067_; 
v_tid_4042_ = lean_ctor_get_uint64(v_traceState_4030_, sizeof(void*)*1);
v_traces_4043_ = lean_ctor_get(v_traceState_4030_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v_traceState_4030_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4045_ = v_traceState_4030_;
v_isShared_4046_ = v_isSharedCheck_4067_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_traces_4043_);
lean_dec(v_traceState_4030_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4067_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4047_; double v___x_4048_; uint8_t v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4057_; 
v___x_4047_ = lean_box(0);
v___x_4048_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_4049_ = 0;
v___x_4050_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_4051_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4051_, 0, v_cls_4016_);
lean_ctor_set(v___x_4051_, 1, v___x_4047_);
lean_ctor_set(v___x_4051_, 2, v___x_4050_);
lean_ctor_set_float(v___x_4051_, sizeof(void*)*3, v___x_4048_);
lean_ctor_set_float(v___x_4051_, sizeof(void*)*3 + 8, v___x_4048_);
lean_ctor_set_uint8(v___x_4051_, sizeof(void*)*3 + 16, v___x_4049_);
v___x_4052_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_4053_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4051_);
lean_ctor_set(v___x_4053_, 1, v_a_4025_);
lean_ctor_set(v___x_4053_, 2, v___x_4052_);
lean_inc(v_ref_4023_);
v___x_4054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4054_, 0, v_ref_4023_);
lean_ctor_set(v___x_4054_, 1, v___x_4053_);
v___x_4055_ = l_Lean_PersistentArray_push___redArg(v_traces_4043_, v___x_4054_);
if (v_isShared_4046_ == 0)
{
lean_ctor_set(v___x_4045_, 0, v___x_4055_);
v___x_4057_ = v___x_4045_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4055_);
lean_ctor_set_uint64(v_reuseFailAlloc_4066_, sizeof(void*)*1, v_tid_4042_);
v___x_4057_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
lean_object* v___x_4059_; 
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 4, v___x_4057_);
v___x_4059_ = v___x_4040_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_env_4031_);
lean_ctor_set(v_reuseFailAlloc_4065_, 1, v_nextMacroScope_4032_);
lean_ctor_set(v_reuseFailAlloc_4065_, 2, v_ngen_4033_);
lean_ctor_set(v_reuseFailAlloc_4065_, 3, v_auxDeclNGen_4034_);
lean_ctor_set(v_reuseFailAlloc_4065_, 4, v___x_4057_);
lean_ctor_set(v_reuseFailAlloc_4065_, 5, v_cache_4035_);
lean_ctor_set(v_reuseFailAlloc_4065_, 6, v_messages_4036_);
lean_ctor_set(v_reuseFailAlloc_4065_, 7, v_infoState_4037_);
lean_ctor_set(v_reuseFailAlloc_4065_, 8, v_snapshotTasks_4038_);
v___x_4059_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4063_; 
v___x_4060_ = lean_st_ref_put(v___y_4021_, v___x_4059_);
v___x_4061_ = lean_box(0);
if (v_isShared_4028_ == 0)
{
lean_ctor_set(v___x_4027_, 0, v___x_4061_);
v___x_4063_ = v___x_4027_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4061_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object* v_cls_4070_, lean_object* v_msg_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_){
_start:
{
lean_object* v_res_4077_; 
v_res_4077_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_cls_4070_, v_msg_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_);
lean_dec(v___y_4075_);
lean_dec_ref(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec_ref(v___y_4072_);
return v_res_4077_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(uint8_t v___x_4078_, lean_object* v___f_4079_, lean_object* v_____r_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v___x_4093_; lean_object* v_caches_4094_; lean_object* v_typeAnalysis_4095_; lean_object* v_target_4096_; lean_object* v_hypotheses_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4107_; 
v___x_4093_ = lean_st_ref_take(v___y_4082_);
v_caches_4094_ = lean_ctor_get(v___x_4093_, 0);
v_typeAnalysis_4095_ = lean_ctor_get(v___x_4093_, 1);
v_target_4096_ = lean_ctor_get(v___x_4093_, 2);
v_hypotheses_4097_ = lean_ctor_get(v___x_4093_, 3);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4093_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4099_ = v___x_4093_;
v_isShared_4100_ = v_isSharedCheck_4107_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_hypotheses_4097_);
lean_inc(v_target_4096_);
lean_inc(v_typeAnalysis_4095_);
lean_inc(v_caches_4094_);
lean_dec(v___x_4093_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4107_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4100_ == 0)
{
v___x_4102_ = v___x_4099_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_caches_4094_);
lean_ctor_set(v_reuseFailAlloc_4106_, 1, v_typeAnalysis_4095_);
lean_ctor_set(v_reuseFailAlloc_4106_, 2, v_target_4096_);
lean_ctor_set(v_reuseFailAlloc_4106_, 3, v_hypotheses_4097_);
v___x_4102_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
lean_ctor_set_uint8(v___x_4102_, sizeof(void*)*4, v___x_4078_);
v___x_4103_ = lean_st_ref_put(v___y_4082_, v___x_4102_);
v___x_4104_ = lean_box(0);
lean_inc(v___y_4091_);
lean_inc_ref(v___y_4090_);
lean_inc(v___y_4089_);
lean_inc_ref(v___y_4088_);
lean_inc(v___y_4087_);
lean_inc_ref(v___y_4086_);
lean_inc(v___y_4085_);
lean_inc_ref(v___y_4084_);
lean_inc(v___y_4083_);
lean_inc(v___y_4082_);
lean_inc_ref(v___y_4081_);
v___x_4105_ = lean_apply_13(v___f_4079_, v___x_4104_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, lean_box(0));
return v___x_4105_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2___boxed(lean_object* v___x_4108_, lean_object* v___f_4109_, lean_object* v_____r_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
uint8_t v___x_10030__boxed_4123_; lean_object* v_res_4124_; 
v___x_10030__boxed_4123_ = lean_unbox(v___x_4108_);
v_res_4124_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_10030__boxed_4123_, v___f_4109_, v_____r_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec(v___y_4115_);
lean_dec_ref(v___y_4114_);
lean_dec(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
return v_res_4124_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4126_; lean_object* v___f_4127_; lean_object* v_methods_4128_; 
v___x_4126_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed), 11, 0);
v___f_4127_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__0));
v_methods_4128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_methods_4128_, 0, v___f_4127_);
lean_ctor_set(v_methods_4128_, 1, v___x_4126_);
return v_methods_4128_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4130_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__2));
v___x_4131_ = l_Lean_stringToMessageData(v___x_4130_);
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object* v_upperBound_4132_, lean_object* v___x_4133_, lean_object* v_config_4134_, lean_object* v_a_4135_, lean_object* v_b_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_){
_start:
{
lean_object* v___y_4150_; uint8_t v___x_4172_; 
v___x_4172_ = lean_nat_dec_lt(v_a_4135_, v_upperBound_4132_);
if (v___x_4172_ == 0)
{
lean_object* v___x_4173_; 
lean_dec(v_a_4135_);
lean_dec_ref(v_config_4134_);
v___x_4173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4173_, 0, v_b_4136_);
return v___x_4173_;
}
else
{
uint8_t v___x_4174_; lean_object* v_methods_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___x_4174_ = 1;
v_methods_4175_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1);
v___x_4176_ = lean_array_fget_borrowed(v___x_4133_, v_a_4135_);
lean_inc(v___x_4176_);
lean_inc_ref(v_config_4134_);
v___x_4177_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v___x_4174_, v_methods_4175_, v_config_4134_, v___x_4176_, v___y_4138_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_object* v_a_4178_; lean_object* v_snd_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4241_; 
v_a_4178_ = lean_ctor_get(v___x_4177_, 0);
lean_inc(v_a_4178_);
lean_dec_ref_known(v___x_4177_, 1);
v_snd_4179_ = lean_ctor_get(v_b_4136_, 1);
v_isSharedCheck_4241_ = !lean_is_exclusive(v_b_4136_);
if (v_isSharedCheck_4241_ == 0)
{
lean_object* v_unused_4242_; 
v_unused_4242_ = lean_ctor_get(v_b_4136_, 0);
lean_dec(v_unused_4242_);
v___x_4181_ = v_b_4136_;
v_isShared_4182_ = v_isSharedCheck_4241_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_snd_4179_);
lean_dec(v_b_4136_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4241_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v_type_4183_; lean_object* v_value_4184_; uint8_t v___x_4185_; 
v_type_4183_ = lean_ctor_get(v_a_4178_, 1);
v_value_4184_ = lean_ctor_get(v_a_4178_, 2);
lean_inc_ref(v_type_4183_);
v___x_4185_ = l_Lean_Expr_isFalse(v_type_4183_);
if (v___x_4185_ == 0)
{
lean_object* v_type_4186_; lean_object* v___x_4187_; lean_object* v___f_4188_; uint8_t v___x_4216_; 
lean_del_object(v___x_4181_);
v_type_4186_ = lean_ctor_get(v___x_4176_, 1);
v___x_4187_ = lean_box(0);
lean_inc(v_a_4178_);
lean_inc(v_snd_4179_);
v___f_4188_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1___boxed), 16, 3);
lean_closure_set(v___f_4188_, 0, v_snd_4179_);
lean_closure_set(v___f_4188_, 1, v_a_4178_);
lean_closure_set(v___f_4188_, 2, v___x_4187_);
v___x_4216_ = lean_expr_eqv(v_type_4186_, v_type_4183_);
if (v___x_4216_ == 0)
{
lean_inc_ref(v_type_4183_);
lean_dec(v_snd_4179_);
lean_dec(v_a_4178_);
goto v___jp_4192_;
}
else
{
if (v___x_4185_ == 0)
{
lean_object* v___x_4217_; lean_object* v___x_4218_; 
lean_dec_ref(v___f_4188_);
v___x_4217_ = lean_box(0);
v___x_4218_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(v_snd_4179_, v_a_4178_, v___x_4187_, v___x_4217_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
v___y_4150_ = v___x_4218_;
goto v___jp_4149_;
}
else
{
lean_inc_ref(v_type_4183_);
lean_dec(v_snd_4179_);
lean_dec(v_a_4178_);
goto v___jp_4192_;
}
}
v___jp_4189_:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4190_ = lean_box(0);
v___x_4191_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_4172_, v___f_4188_, v___x_4190_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
v___y_4150_ = v___x_4191_;
goto v___jp_4149_;
}
v___jp_4192_:
{
lean_object* v_options_4193_; uint8_t v_hasTrace_4194_; 
v_options_4193_ = lean_ctor_get(v___y_4146_, 2);
v_hasTrace_4194_ = lean_ctor_get_uint8(v_options_4193_, sizeof(void*)*1);
if (v_hasTrace_4194_ == 0)
{
lean_dec_ref(v_type_4183_);
goto v___jp_4189_;
}
else
{
lean_object* v_inheritedTraceOptions_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; uint8_t v___x_4198_; 
v_inheritedTraceOptions_4195_ = lean_ctor_get(v___y_4146_, 13);
v___x_4196_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_4197_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_4198_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4195_, v_options_4193_, v___x_4197_);
if (v___x_4198_ == 0)
{
lean_dec_ref(v_type_4183_);
goto v___jp_4189_;
}
else
{
lean_object* v_type_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v_type_4199_ = lean_ctor_get(v___x_4176_, 1);
lean_inc_ref(v_type_4199_);
v___x_4200_ = l_Lean_MessageData_ofExpr(v_type_4199_);
v___x_4201_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3);
v___x_4202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4200_);
lean_ctor_set(v___x_4202_, 1, v___x_4201_);
v___x_4203_ = l_Lean_MessageData_ofExpr(v_type_4183_);
v___x_4204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4202_);
lean_ctor_set(v___x_4204_, 1, v___x_4203_);
v___x_4205_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v___x_4196_, v___x_4204_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; lean_object* v___x_4207_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref_known(v___x_4205_, 1);
v___x_4207_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_4172_, v___f_4188_, v_a_4206_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
v___y_4150_ = v___x_4207_;
goto v___jp_4149_;
}
else
{
lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4215_; 
lean_dec_ref(v___f_4188_);
lean_dec(v_a_4135_);
lean_dec_ref(v_config_4134_);
v_a_4208_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4210_ = v___x_4205_;
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4205_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4213_; 
if (v_isShared_4211_ == 0)
{
v___x_4213_ = v___x_4210_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4208_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4219_; 
lean_inc_ref(v_value_4184_);
lean_dec(v_a_4178_);
lean_dec(v_a_4135_);
lean_dec_ref(v_config_4134_);
v___x_4219_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4184_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4231_; 
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4231_ == 0)
{
lean_object* v_unused_4232_; 
v_unused_4232_ = lean_ctor_get(v___x_4219_, 0);
lean_dec(v_unused_4232_);
v___x_4221_ = v___x_4219_;
v_isShared_4222_ = v_isSharedCheck_4231_;
goto v_resetjp_4220_;
}
else
{
lean_dec(v___x_4219_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4231_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4226_; 
v___x_4223_ = lean_box(v___x_4185_);
v___x_4224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4224_, 0, v___x_4223_);
if (v_isShared_4182_ == 0)
{
lean_ctor_set(v___x_4181_, 0, v___x_4224_);
v___x_4226_ = v___x_4181_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4224_);
lean_ctor_set(v_reuseFailAlloc_4230_, 1, v_snd_4179_);
v___x_4226_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
lean_object* v___x_4228_; 
if (v_isShared_4222_ == 0)
{
lean_ctor_set(v___x_4221_, 0, v___x_4226_);
v___x_4228_ = v___x_4221_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v___x_4226_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
}
else
{
lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4240_; 
lean_del_object(v___x_4181_);
lean_dec(v_snd_4179_);
v_a_4233_ = lean_ctor_get(v___x_4219_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4235_ = v___x_4219_;
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_dec(v___x_4219_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4238_; 
if (v_isShared_4236_ == 0)
{
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_a_4233_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
}
}
}
else
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_dec_ref(v_b_4136_);
lean_dec(v_a_4135_);
lean_dec_ref(v_config_4134_);
v_a_4243_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4177_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4177_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
v___jp_4149_:
{
if (lean_obj_tag(v___y_4150_) == 0)
{
lean_object* v_a_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4163_; 
v_a_4151_ = lean_ctor_get(v___y_4150_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___y_4150_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4153_ = v___y_4150_;
v_isShared_4154_ = v_isSharedCheck_4163_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_a_4151_);
lean_dec(v___y_4150_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4163_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
if (lean_obj_tag(v_a_4151_) == 0)
{
lean_object* v_a_4155_; lean_object* v___x_4157_; 
lean_dec(v_a_4135_);
lean_dec_ref(v_config_4134_);
v_a_4155_ = lean_ctor_get(v_a_4151_, 0);
lean_inc(v_a_4155_);
lean_dec_ref_known(v_a_4151_, 1);
if (v_isShared_4154_ == 0)
{
lean_ctor_set(v___x_4153_, 0, v_a_4155_);
v___x_4157_ = v___x_4153_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_a_4155_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
else
{
lean_object* v_a_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
lean_del_object(v___x_4153_);
v_a_4159_ = lean_ctor_get(v_a_4151_, 0);
lean_inc(v_a_4159_);
lean_dec_ref_known(v_a_4151_, 1);
v___x_4160_ = lean_unsigned_to_nat(1u);
v___x_4161_ = lean_nat_add(v_a_4135_, v___x_4160_);
lean_dec(v_a_4135_);
v_a_4135_ = v___x_4161_;
v_b_4136_ = v_a_4159_;
goto _start;
}
}
}
else
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4171_; 
lean_dec(v_a_4135_);
lean_dec_ref(v_config_4134_);
v_a_4164_ = lean_ctor_get(v___y_4150_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___y_4150_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4166_ = v___y_4150_;
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___y_4150_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_a_4164_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_4251_ = _args[0];
lean_object* v___x_4252_ = _args[1];
lean_object* v_config_4253_ = _args[2];
lean_object* v_a_4254_ = _args[3];
lean_object* v_b_4255_ = _args[4];
lean_object* v___y_4256_ = _args[5];
lean_object* v___y_4257_ = _args[6];
lean_object* v___y_4258_ = _args[7];
lean_object* v___y_4259_ = _args[8];
lean_object* v___y_4260_ = _args[9];
lean_object* v___y_4261_ = _args[10];
lean_object* v___y_4262_ = _args[11];
lean_object* v___y_4263_ = _args[12];
lean_object* v___y_4264_ = _args[13];
lean_object* v___y_4265_ = _args[14];
lean_object* v___y_4266_ = _args[15];
lean_object* v___y_4267_ = _args[16];
_start:
{
lean_object* v_res_4268_; 
v_res_4268_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_upperBound_4251_, v___x_4252_, v_config_4253_, v_a_4254_, v_b_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
lean_dec(v___y_4266_);
lean_dec_ref(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
lean_dec(v___y_4258_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
lean_dec_ref(v___x_4252_);
lean_dec(v_upperBound_4251_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(lean_object* v_config_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_){
_start:
{
lean_object* v___x_4282_; lean_object* v_hypotheses_4283_; lean_object* v___x_4284_; lean_object* v_newHyps_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___x_4282_ = lean_st_ref_get(v___y_4271_);
v_hypotheses_4283_ = lean_ctor_get(v___x_4282_, 3);
lean_inc_ref(v_hypotheses_4283_);
lean_dec(v___x_4282_);
v___x_4284_ = lean_array_get_size(v_hypotheses_4283_);
v_newHyps_4285_ = lean_mk_empty_array_with_capacity(v___x_4284_);
v___x_4286_ = lean_unsigned_to_nat(0u);
v___x_4287_ = lean_box(0);
v___x_4288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4288_, 0, v___x_4287_);
lean_ctor_set(v___x_4288_, 1, v_newHyps_4285_);
v___x_4289_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v___x_4284_, v_hypotheses_4283_, v_config_4269_, v___x_4286_, v___x_4288_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_);
lean_dec_ref(v_hypotheses_4283_);
if (lean_obj_tag(v___x_4289_) == 0)
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4319_; 
v_a_4290_ = lean_ctor_get(v___x_4289_, 0);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4292_ = v___x_4289_;
v_isShared_4293_ = v_isSharedCheck_4319_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v___x_4289_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4319_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v_fst_4294_; 
v_fst_4294_ = lean_ctor_get(v_a_4290_, 0);
if (lean_obj_tag(v_fst_4294_) == 0)
{
lean_object* v_snd_4295_; lean_object* v___x_4296_; lean_object* v_caches_4297_; lean_object* v_typeAnalysis_4298_; lean_object* v_target_4299_; uint8_t v_didChange_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4313_; 
v_snd_4295_ = lean_ctor_get(v_a_4290_, 1);
lean_inc(v_snd_4295_);
lean_dec(v_a_4290_);
v___x_4296_ = lean_st_ref_take(v___y_4271_);
v_caches_4297_ = lean_ctor_get(v___x_4296_, 0);
v_typeAnalysis_4298_ = lean_ctor_get(v___x_4296_, 1);
v_target_4299_ = lean_ctor_get(v___x_4296_, 2);
v_didChange_4300_ = lean_ctor_get_uint8(v___x_4296_, sizeof(void*)*4);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4313_ == 0)
{
lean_object* v_unused_4314_; 
v_unused_4314_ = lean_ctor_get(v___x_4296_, 3);
lean_dec(v_unused_4314_);
v___x_4302_ = v___x_4296_;
v_isShared_4303_ = v_isSharedCheck_4313_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_target_4299_);
lean_inc(v_typeAnalysis_4298_);
lean_inc(v_caches_4297_);
lean_dec(v___x_4296_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4313_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
lean_ctor_set(v___x_4302_, 3, v_snd_4295_);
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_caches_4297_);
lean_ctor_set(v_reuseFailAlloc_4312_, 1, v_typeAnalysis_4298_);
lean_ctor_set(v_reuseFailAlloc_4312_, 2, v_target_4299_);
lean_ctor_set(v_reuseFailAlloc_4312_, 3, v_snd_4295_);
lean_ctor_set_uint8(v_reuseFailAlloc_4312_, sizeof(void*)*4, v_didChange_4300_);
v___x_4305_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
lean_object* v___x_4306_; uint8_t v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4310_; 
v___x_4306_ = lean_st_ref_put(v___y_4271_, v___x_4305_);
v___x_4307_ = 0;
v___x_4308_ = lean_box(v___x_4307_);
if (v_isShared_4293_ == 0)
{
lean_ctor_set(v___x_4292_, 0, v___x_4308_);
v___x_4310_ = v___x_4292_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v___x_4308_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
}
else
{
lean_object* v_val_4315_; lean_object* v___x_4317_; 
lean_inc_ref(v_fst_4294_);
lean_dec(v_a_4290_);
v_val_4315_ = lean_ctor_get(v_fst_4294_, 0);
lean_inc(v_val_4315_);
lean_dec_ref_known(v_fst_4294_, 1);
if (v_isShared_4293_ == 0)
{
lean_ctor_set(v___x_4292_, 0, v_val_4315_);
v___x_4317_ = v___x_4292_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_val_4315_);
v___x_4317_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
return v___x_4317_;
}
}
}
}
else
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
v_a_4320_ = lean_ctor_get(v___x_4289_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___x_4289_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4289_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4325_; 
if (v_isShared_4323_ == 0)
{
v___x_4325_ = v___x_4322_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4320_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed(lean_object* v_config_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(v_config_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
lean_dec(v___y_4335_);
lean_dec_ref(v___y_4334_);
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
lean_dec(v___y_4331_);
lean_dec(v___y_4330_);
lean_dec_ref(v___y_4329_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_){
_start:
{
lean_object* v_config_4354_; lean_object* v___x_4355_; lean_object* v_maxSteps_4356_; lean_object* v_target_4357_; lean_object* v___x_4358_; lean_object* v_config_4359_; lean_object* v___f_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
v_config_4354_ = lean_ctor_get(v___y_4342_, 0);
v___x_4355_ = lean_st_ref_get(v___y_4343_);
v_maxSteps_4356_ = lean_ctor_get(v_config_4354_, 1);
v_target_4357_ = lean_ctor_get(v___x_4355_, 2);
lean_inc_ref(v_target_4357_);
lean_dec(v___x_4355_);
v___x_4358_ = lean_unsigned_to_nat(2u);
lean_inc(v_maxSteps_4356_);
v_config_4359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_config_4359_, 0, v_maxSteps_4356_);
lean_ctor_set(v_config_4359_, 1, v___x_4358_);
v___f_4360_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed), 13, 1);
lean_closure_set(v___f_4360_, 0, v_config_4359_);
v___x_4361_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_4357_);
lean_dec_ref(v_target_4357_);
v___x_4362_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v___x_4361_, v___f_4360_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_);
return v___x_4362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___boxed(lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_);
lean_dec(v___y_4373_);
lean_dec_ref(v___y_4372_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v___y_4367_);
lean_dec_ref(v___y_4366_);
lean_dec(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(lean_object* v_cls_4384_, lean_object* v_msg_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
lean_object* v___x_4398_; 
v___x_4398_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_cls_4384_, v_msg_4385_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___boxed(lean_object* v_cls_4399_, lean_object* v_msg_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(v_cls_4399_, v_msg_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
lean_dec(v___y_4403_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(lean_object* v_upperBound_4414_, lean_object* v___x_4415_, lean_object* v_config_4416_, lean_object* v_inst_4417_, lean_object* v_R_4418_, lean_object* v_a_4419_, lean_object* v_b_4420_, lean_object* v_c_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v___x_4434_; 
v___x_4434_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_upperBound_4414_, v___x_4415_, v_config_4416_, v_a_4419_, v_b_4420_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_4435_ = _args[0];
lean_object* v___x_4436_ = _args[1];
lean_object* v_config_4437_ = _args[2];
lean_object* v_inst_4438_ = _args[3];
lean_object* v_R_4439_ = _args[4];
lean_object* v_a_4440_ = _args[5];
lean_object* v_b_4441_ = _args[6];
lean_object* v_c_4442_ = _args[7];
lean_object* v___y_4443_ = _args[8];
lean_object* v___y_4444_ = _args[9];
lean_object* v___y_4445_ = _args[10];
lean_object* v___y_4446_ = _args[11];
lean_object* v___y_4447_ = _args[12];
lean_object* v___y_4448_ = _args[13];
lean_object* v___y_4449_ = _args[14];
lean_object* v___y_4450_ = _args[15];
lean_object* v___y_4451_ = _args[16];
lean_object* v___y_4452_ = _args[17];
lean_object* v___y_4453_ = _args[18];
lean_object* v___y_4454_ = _args[19];
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(v_upperBound_4435_, v___x_4436_, v_config_4437_, v_inst_4438_, v_R_4439_, v_a_4440_, v_b_4441_, v_c_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
lean_dec(v___y_4453_);
lean_dec_ref(v___y_4452_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec(v___y_4445_);
lean_dec(v___y_4444_);
lean_dec_ref(v___y_4443_);
lean_dec_ref(v___x_4436_);
lean_dec(v_upperBound_4435_);
return v_res_4455_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_AC_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_AC_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_AC_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_AC_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(builtin);
}
#ifdef __cplusplus
}
#endif
