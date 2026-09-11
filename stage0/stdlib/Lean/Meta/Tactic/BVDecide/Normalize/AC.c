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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
lean_object* lean_mk_array(lean_object*, lean_object*);
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0___boxed(lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Operations mismatch:\n      the left-hand-side has operation "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\n        "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "\n      but the right-hand-side has operation "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Canonicalizing with respect to operation: '"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "'."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Failed to recognize operation: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(lean_object* v_a_224_, lean_object* v_b_225_, lean_object* v_x_226_){
_start:
{
if (lean_obj_tag(v_x_226_) == 0)
{
lean_dec(v_b_225_);
lean_dec_ref(v_a_224_);
return v_x_226_;
}
else
{
lean_object* v_key_227_; lean_object* v_value_228_; lean_object* v_tail_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_241_; 
v_key_227_ = lean_ctor_get(v_x_226_, 0);
v_value_228_ = lean_ctor_get(v_x_226_, 1);
v_tail_229_ = lean_ctor_get(v_x_226_, 2);
v_isSharedCheck_241_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_241_ == 0)
{
v___x_231_ = v_x_226_;
v_isShared_232_ = v_isSharedCheck_241_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_tail_229_);
lean_inc(v_value_228_);
lean_inc(v_key_227_);
lean_dec(v_x_226_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_241_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
uint8_t v___x_233_; 
v___x_233_ = lean_expr_eqv(v_key_227_, v_a_224_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_224_, v_b_225_, v_tail_229_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 2, v___x_234_);
v___x_236_ = v___x_231_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_key_227_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_value_228_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
else
{
lean_object* v___x_239_; 
lean_dec(v_value_228_);
lean_dec(v_key_227_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 1, v_b_225_);
lean_ctor_set(v___x_231_, 0, v_a_224_);
v___x_239_ = v___x_231_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_224_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_b_225_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_tail_229_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(lean_object* v_a_242_, lean_object* v_x_243_){
_start:
{
if (lean_obj_tag(v_x_243_) == 0)
{
uint8_t v___x_244_; 
v___x_244_ = 0;
return v___x_244_;
}
else
{
lean_object* v_key_245_; lean_object* v_tail_246_; uint8_t v___x_247_; 
v_key_245_ = lean_ctor_get(v_x_243_, 0);
v_tail_246_ = lean_ctor_get(v_x_243_, 2);
v___x_247_ = lean_expr_eqv(v_key_245_, v_a_242_);
if (v___x_247_ == 0)
{
v_x_243_ = v_tail_246_;
goto _start;
}
else
{
return v___x_247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg___boxed(lean_object* v_a_249_, lean_object* v_x_250_){
_start:
{
uint8_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_249_, v_x_250_);
lean_dec(v_x_250_);
lean_dec_ref(v_a_249_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
if (lean_obj_tag(v_x_254_) == 0)
{
return v_x_253_;
}
else
{
lean_object* v_key_255_; lean_object* v_value_256_; lean_object* v_tail_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_280_; 
v_key_255_ = lean_ctor_get(v_x_254_, 0);
v_value_256_ = lean_ctor_get(v_x_254_, 1);
v_tail_257_ = lean_ctor_get(v_x_254_, 2);
v_isSharedCheck_280_ = !lean_is_exclusive(v_x_254_);
if (v_isSharedCheck_280_ == 0)
{
v___x_259_ = v_x_254_;
v_isShared_260_ = v_isSharedCheck_280_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_tail_257_);
lean_inc(v_value_256_);
lean_inc(v_key_255_);
lean_dec(v_x_254_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_280_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; uint64_t v___x_262_; uint64_t v___x_263_; uint64_t v___x_264_; uint64_t v_fold_265_; uint64_t v___x_266_; uint64_t v___x_267_; uint64_t v___x_268_; size_t v___x_269_; size_t v___x_270_; size_t v___x_271_; size_t v___x_272_; size_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_261_ = lean_array_get_size(v_x_253_);
v___x_262_ = l_Lean_Expr_hash(v_key_255_);
v___x_263_ = 32ULL;
v___x_264_ = lean_uint64_shift_right(v___x_262_, v___x_263_);
v_fold_265_ = lean_uint64_xor(v___x_262_, v___x_264_);
v___x_266_ = 16ULL;
v___x_267_ = lean_uint64_shift_right(v_fold_265_, v___x_266_);
v___x_268_ = lean_uint64_xor(v_fold_265_, v___x_267_);
v___x_269_ = lean_uint64_to_usize(v___x_268_);
v___x_270_ = lean_usize_of_nat(v___x_261_);
v___x_271_ = ((size_t)1ULL);
v___x_272_ = lean_usize_sub(v___x_270_, v___x_271_);
v___x_273_ = lean_usize_land(v___x_269_, v___x_272_);
v___x_274_ = lean_array_uget_borrowed(v_x_253_, v___x_273_);
lean_inc(v___x_274_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 2, v___x_274_);
v___x_276_ = v___x_259_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_key_255_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_value_256_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v___x_274_);
v___x_276_ = v_reuseFailAlloc_279_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_277_; 
v___x_277_ = lean_array_uset(v_x_253_, v___x_273_, v___x_276_);
v_x_253_ = v___x_277_;
v_x_254_ = v_tail_257_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(lean_object* v_i_281_, lean_object* v_source_282_, lean_object* v_target_283_){
_start:
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = lean_array_get_size(v_source_282_);
v___x_285_ = lean_nat_dec_lt(v_i_281_, v___x_284_);
if (v___x_285_ == 0)
{
lean_dec_ref(v_source_282_);
lean_dec(v_i_281_);
return v_target_283_;
}
else
{
lean_object* v_es_286_; lean_object* v___x_287_; lean_object* v_source_288_; lean_object* v_target_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v_es_286_ = lean_array_fget(v_source_282_, v_i_281_);
v___x_287_ = lean_box(0);
v_source_288_ = lean_array_fset(v_source_282_, v_i_281_, v___x_287_);
v_target_289_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(v_target_283_, v_es_286_);
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = lean_nat_add(v_i_281_, v___x_290_);
lean_dec(v_i_281_);
v_i_281_ = v___x_291_;
v_source_282_ = v_source_288_;
v_target_283_ = v_target_289_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(lean_object* v_data_293_){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v_nbuckets_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_294_ = lean_array_get_size(v_data_293_);
v___x_295_ = lean_unsigned_to_nat(2u);
v_nbuckets_296_ = lean_nat_mul(v___x_294_, v___x_295_);
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = lean_box(0);
v___x_299_ = lean_mk_array(v_nbuckets_296_, v___x_298_);
v___x_300_ = lean_array_propagate_mark(v_data_293_, v___x_299_);
v___x_301_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(v___x_297_, v_data_293_, v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(lean_object* v_m_302_, lean_object* v_a_303_, lean_object* v_b_304_){
_start:
{
lean_object* v_size_305_; lean_object* v_buckets_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_349_; 
v_size_305_ = lean_ctor_get(v_m_302_, 0);
v_buckets_306_ = lean_ctor_get(v_m_302_, 1);
v_isSharedCheck_349_ = !lean_is_exclusive(v_m_302_);
if (v_isSharedCheck_349_ == 0)
{
v___x_308_ = v_m_302_;
v_isShared_309_ = v_isSharedCheck_349_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_buckets_306_);
lean_inc(v_size_305_);
lean_dec(v_m_302_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_349_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; uint64_t v___x_311_; uint64_t v___x_312_; uint64_t v___x_313_; uint64_t v_fold_314_; uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v___x_317_; size_t v___x_318_; size_t v___x_319_; size_t v___x_320_; size_t v___x_321_; size_t v___x_322_; lean_object* v_bkt_323_; uint8_t v___x_324_; 
v___x_310_ = lean_array_get_size(v_buckets_306_);
v___x_311_ = l_Lean_Expr_hash(v_a_303_);
v___x_312_ = 32ULL;
v___x_313_ = lean_uint64_shift_right(v___x_311_, v___x_312_);
v_fold_314_ = lean_uint64_xor(v___x_311_, v___x_313_);
v___x_315_ = 16ULL;
v___x_316_ = lean_uint64_shift_right(v_fold_314_, v___x_315_);
v___x_317_ = lean_uint64_xor(v_fold_314_, v___x_316_);
v___x_318_ = lean_uint64_to_usize(v___x_317_);
v___x_319_ = lean_usize_of_nat(v___x_310_);
v___x_320_ = ((size_t)1ULL);
v___x_321_ = lean_usize_sub(v___x_319_, v___x_320_);
v___x_322_ = lean_usize_land(v___x_318_, v___x_321_);
v_bkt_323_ = lean_array_uget_borrowed(v_buckets_306_, v___x_322_);
v___x_324_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_303_, v_bkt_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v_size_x27_326_; lean_object* v___x_327_; lean_object* v_buckets_x27_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_325_ = lean_unsigned_to_nat(1u);
v_size_x27_326_ = lean_nat_add(v_size_305_, v___x_325_);
lean_dec(v_size_305_);
lean_inc(v_bkt_323_);
v___x_327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_327_, 0, v_a_303_);
lean_ctor_set(v___x_327_, 1, v_b_304_);
lean_ctor_set(v___x_327_, 2, v_bkt_323_);
v_buckets_x27_328_ = lean_array_uset(v_buckets_306_, v___x_322_, v___x_327_);
v___x_329_ = lean_unsigned_to_nat(4u);
v___x_330_ = lean_nat_mul(v_size_x27_326_, v___x_329_);
v___x_331_ = lean_unsigned_to_nat(3u);
v___x_332_ = lean_nat_div(v___x_330_, v___x_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_array_get_size(v_buckets_x27_328_);
v___x_334_ = lean_nat_dec_le(v___x_332_, v___x_333_);
lean_dec(v___x_332_);
if (v___x_334_ == 0)
{
lean_object* v_val_335_; lean_object* v___x_337_; 
v_val_335_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(v_buckets_x27_328_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v_val_335_);
lean_ctor_set(v___x_308_, 0, v_size_x27_326_);
v___x_337_ = v___x_308_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_size_x27_326_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_val_335_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
else
{
lean_object* v___x_340_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v_buckets_x27_328_);
lean_ctor_set(v___x_308_, 0, v_size_x27_326_);
v___x_340_ = v___x_308_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_size_x27_326_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_buckets_x27_328_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
else
{
lean_object* v___x_342_; lean_object* v_buckets_x27_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_347_; 
lean_inc(v_bkt_323_);
v___x_342_ = lean_box(0);
v_buckets_x27_343_ = lean_array_uset(v_buckets_306_, v___x_322_, v___x_342_);
v___x_344_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_303_, v_b_304_, v_bkt_323_);
v___x_345_ = lean_array_uset(v_buckets_x27_343_, v___x_322_, v___x_344_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v___x_345_);
v___x_347_ = v___x_308_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_size_305_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(lean_object* v_a_350_, lean_object* v_x_351_){
_start:
{
if (lean_obj_tag(v_x_351_) == 0)
{
lean_object* v___x_352_; 
v___x_352_ = lean_box(0);
return v___x_352_;
}
else
{
lean_object* v_key_353_; lean_object* v_value_354_; lean_object* v_tail_355_; uint8_t v___x_356_; 
v_key_353_ = lean_ctor_get(v_x_351_, 0);
v_value_354_ = lean_ctor_get(v_x_351_, 1);
v_tail_355_ = lean_ctor_get(v_x_351_, 2);
v___x_356_ = lean_expr_eqv(v_key_353_, v_a_350_);
if (v___x_356_ == 0)
{
v_x_351_ = v_tail_355_;
goto _start;
}
else
{
lean_object* v___x_358_; 
lean_inc(v_value_354_);
v___x_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_358_, 0, v_value_354_);
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_359_, lean_object* v_x_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_359_, v_x_360_);
lean_dec(v_x_360_);
lean_dec_ref(v_a_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(lean_object* v_m_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_buckets_364_; lean_object* v___x_365_; uint64_t v___x_366_; uint64_t v___x_367_; uint64_t v___x_368_; uint64_t v_fold_369_; uint64_t v___x_370_; uint64_t v___x_371_; uint64_t v___x_372_; size_t v___x_373_; size_t v___x_374_; size_t v___x_375_; size_t v___x_376_; size_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_buckets_364_ = lean_ctor_get(v_m_362_, 1);
v___x_365_ = lean_array_get_size(v_buckets_364_);
v___x_366_ = l_Lean_Expr_hash(v_a_363_);
v___x_367_ = 32ULL;
v___x_368_ = lean_uint64_shift_right(v___x_366_, v___x_367_);
v_fold_369_ = lean_uint64_xor(v___x_366_, v___x_368_);
v___x_370_ = 16ULL;
v___x_371_ = lean_uint64_shift_right(v_fold_369_, v___x_370_);
v___x_372_ = lean_uint64_xor(v_fold_369_, v___x_371_);
v___x_373_ = lean_uint64_to_usize(v___x_372_);
v___x_374_ = lean_usize_of_nat(v___x_365_);
v___x_375_ = ((size_t)1ULL);
v___x_376_ = lean_usize_sub(v___x_374_, v___x_375_);
v___x_377_ = lean_usize_land(v___x_373_, v___x_376_);
v___x_378_ = lean_array_uget_borrowed(v_buckets_364_, v___x_377_);
v___x_379_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_363_, v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg___boxed(lean_object* v_m_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_m_380_, v_a_381_);
lean_dec_ref(v_a_381_);
lean_dec_ref(v_m_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(lean_object* v_e_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_op_386_; lean_object* v_exprToVarIndex_387_; lean_object* v_varToExpr_388_; lean_object* v___x_389_; 
v_op_386_ = lean_ctor_get(v_a_384_, 0);
v_exprToVarIndex_387_ = lean_ctor_get(v_a_384_, 1);
v_varToExpr_388_ = lean_ctor_get(v_a_384_, 2);
v___x_389_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_exprToVarIndex_387_, v_e_383_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_401_; 
lean_inc_ref(v_varToExpr_388_);
lean_inc_ref(v_exprToVarIndex_387_);
lean_inc_ref(v_op_386_);
v_isSharedCheck_401_ = !lean_is_exclusive(v_a_384_);
if (v_isSharedCheck_401_ == 0)
{
lean_object* v_unused_402_; lean_object* v_unused_403_; lean_object* v_unused_404_; 
v_unused_402_ = lean_ctor_get(v_a_384_, 2);
lean_dec(v_unused_402_);
v_unused_403_ = lean_ctor_get(v_a_384_, 1);
lean_dec(v_unused_403_);
v_unused_404_ = lean_ctor_get(v_a_384_, 0);
lean_dec(v_unused_404_);
v___x_391_ = v_a_384_;
v_isShared_392_ = v_isSharedCheck_401_;
goto v_resetjp_390_;
}
else
{
lean_dec(v_a_384_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_401_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v_size_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
v_size_393_ = lean_ctor_get(v_exprToVarIndex_387_, 0);
lean_inc_n(v_size_393_, 2);
lean_inc_ref(v_e_383_);
v___x_394_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(v_exprToVarIndex_387_, v_e_383_, v_size_393_);
v___x_395_ = lean_array_push(v_varToExpr_388_, v_e_383_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 2, v___x_395_);
lean_ctor_set(v___x_391_, 1, v___x_394_);
v___x_397_ = v___x_391_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_op_386_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_400_, 2, v___x_395_);
v___x_397_ = v_reuseFailAlloc_400_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v_size_393_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
}
}
else
{
lean_object* v_val_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_413_; 
lean_dec_ref(v_e_383_);
v_val_405_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_413_ == 0)
{
v___x_407_ = v___x_389_;
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_val_405_);
lean_dec(v___x_389_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v_val_405_);
lean_ctor_set(v___x_409_, 1, v_a_384_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 0);
lean_ctor_set(v___x_407_, 0, v___x_409_);
v___x_411_ = v___x_407_;
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg___boxed(lean_object* v_e_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_414_, v_a_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar(lean_object* v_e_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_418_, v_a_419_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___boxed(lean_object* v_e_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar(v_e_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0(lean_object* v_00_u03b2_438_, lean_object* v_m_439_, lean_object* v_a_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_m_439_, v_a_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___boxed(lean_object* v_00_u03b2_442_, lean_object* v_m_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0(v_00_u03b2_442_, v_m_443_, v_a_444_);
lean_dec_ref(v_a_444_);
lean_dec_ref(v_m_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1(lean_object* v_00_u03b2_446_, lean_object* v_m_447_, lean_object* v_a_448_, lean_object* v_b_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(v_m_447_, v_a_448_, v_b_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0(lean_object* v_00_u03b2_451_, lean_object* v_a_452_, lean_object* v_x_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_452_, v_x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_455_, lean_object* v_a_456_, lean_object* v_x_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0(v_00_u03b2_455_, v_a_456_, v_x_457_);
lean_dec(v_x_457_);
lean_dec_ref(v_a_456_);
return v_res_458_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2(lean_object* v_00_u03b2_459_, lean_object* v_a_460_, lean_object* v_x_461_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_460_, v_x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_463_, lean_object* v_a_464_, lean_object* v_x_465_){
_start:
{
uint8_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2(v_00_u03b2_463_, v_a_464_, v_x_465_);
lean_dec(v_x_465_);
lean_dec_ref(v_a_464_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3(lean_object* v_00_u03b2_468_, lean_object* v_data_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(v_data_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4(lean_object* v_00_u03b2_471_, lean_object* v_a_472_, lean_object* v_b_473_, lean_object* v_x_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_472_, v_b_473_, v_x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_476_, lean_object* v_i_477_, lean_object* v_source_478_, lean_object* v_target_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(v_i_477_, v_source_478_, v_target_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_481_, lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(v_x_482_, v_x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(lean_object* v_msgData_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___x_491_; lean_object* v_env_492_; lean_object* v___x_493_; lean_object* v_toCold_494_; lean_object* v_mctx_495_; lean_object* v_lctx_496_; lean_object* v_options_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_491_ = lean_st_ref_get(v___y_489_);
v_env_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc_ref(v_env_492_);
lean_dec(v___x_491_);
v___x_493_ = lean_st_ref_get(v___y_487_);
v_toCold_494_ = lean_ctor_get(v___y_488_, 0);
v_mctx_495_ = lean_ctor_get(v___x_493_, 0);
lean_inc_ref(v_mctx_495_);
lean_dec(v___x_493_);
v_lctx_496_ = lean_ctor_get(v___y_486_, 2);
v_options_497_ = lean_ctor_get(v_toCold_494_, 2);
lean_inc_ref(v_options_497_);
lean_inc_ref(v_lctx_496_);
v___x_498_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_498_, 0, v_env_492_);
lean_ctor_set(v___x_498_, 1, v_mctx_495_);
lean_ctor_set(v___x_498_, 2, v_lctx_496_);
lean_ctor_set(v___x_498_, 3, v_options_497_);
v___x_499_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v_msgData_485_);
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1___boxed(lean_object* v_msgData_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msgData_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(lean_object* v_msg_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_ref_514_; lean_object* v___x_515_; lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_524_; 
v_ref_514_ = lean_ctor_get(v___y_511_, 2);
v___x_515_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
v_a_516_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_524_ == 0)
{
v___x_518_ = v___x_515_;
v_isShared_519_ = v_isSharedCheck_524_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_524_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_522_; 
lean_inc(v_ref_514_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v_ref_514_);
lean_ctor_set(v___x_520_, 1, v_a_516_);
if (v_isShared_519_ == 0)
{
lean_ctor_set_tag(v___x_518_, 1);
lean_ctor_set(v___x_518_, 0, v___x_520_);
v___x_522_ = v___x_518_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg___boxed(lean_object* v_msg_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__0(lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
if (lean_obj_tag(v_a_532_) == 0)
{
lean_object* v___x_534_; 
v___x_534_ = l_List_reverse___redArg(v_a_533_);
return v___x_534_;
}
else
{
lean_object* v_head_535_; lean_object* v_tail_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_545_; 
v_head_535_ = lean_ctor_get(v_a_532_, 0);
v_tail_536_ = lean_ctor_get(v_a_532_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v_a_532_);
if (v_isSharedCheck_545_ == 0)
{
v___x_538_ = v_a_532_;
v_isShared_539_ = v_isSharedCheck_545_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_tail_536_);
lean_inc(v_head_535_);
lean_dec(v_a_532_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_545_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_540_ = l_Lean_MessageData_ofExpr(v_head_535_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v_a_533_);
lean_ctor_set(v___x_538_, 0, v___x_540_);
v___x_542_ = v___x_538_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_a_533_);
v___x_542_ = v_reuseFailAlloc_544_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
v_a_532_ = v_tail_536_;
v_a_533_ = v___x_542_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__0));
v___x_548_ = l_Lean_stringToMessageData(v___x_547_);
return v___x_548_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__2));
v___x_551_ = l_Lean_stringToMessageData(v___x_550_);
return v___x_551_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__4));
v___x_554_ = l_Lean_stringToMessageData(v___x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(lean_object* v_idx_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_varToExpr_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v_varToExpr_564_ = lean_ctor_get(v_a_556_, 2);
v___x_565_ = lean_array_get_size(v_varToExpr_564_);
v___x_566_ = lean_nat_dec_lt(v_idx_555_, v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
lean_inc_ref(v_varToExpr_564_);
lean_dec_ref(v_a_556_);
v___x_567_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1);
v___x_568_ = l_Nat_reprFast(v_idx_555_);
v___x_569_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
v___x_570_ = l_Lean_MessageData_ofFormat(v___x_569_);
v___x_571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_567_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3);
v___x_573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_571_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = l_Nat_reprFast(v___x_565_);
v___x_575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
v___x_576_ = l_Lean_MessageData_ofFormat(v___x_575_);
v___x_577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_573_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5);
v___x_579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = lean_array_to_list(v_varToExpr_564_);
v___x_581_ = lean_box(0);
v___x_582_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__0(v___x_580_, v___x_581_);
v___x_583_ = l_Lean_MessageData_ofList(v___x_582_);
v___x_584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_579_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v___x_584_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
return v___x_585_;
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_586_ = lean_array_fget(v_varToExpr_564_, v_idx_555_);
lean_dec(v_idx_555_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v_a_556_);
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___boxed(lean_object* v_idx_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(v_idx_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(lean_object* v_00_u03b1_599_, lean_object* v_msg_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_600_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___boxed(lean_object* v_00_u03b1_610_, lean_object* v_msg_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(v_00_u03b1_610_, v_msg_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec_ref(v___y_612_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(lean_object* v_c_621_){
_start:
{
lean_object* v___y_623_; 
if (lean_obj_tag(v_c_621_) == 0)
{
lean_object* v___x_627_; 
v___x_627_ = lean_unsigned_to_nat(0u);
v___y_623_ = v___x_627_;
goto v___jp_622_;
}
else
{
lean_object* v_val_628_; 
v_val_628_ = lean_ctor_get(v_c_621_, 0);
v___y_623_ = v_val_628_;
goto v___jp_622_;
}
v___jp_622_:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = lean_nat_add(v___y_623_, v___x_624_);
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
return v___x_626_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0___boxed(lean_object* v_c_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v_c_629_);
lean_dec(v_c_629_);
return v_res_630_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_box(0);
v___x_632_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v___x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(lean_object* v_a_633_, lean_object* v_x_634_){
_start:
{
if (lean_obj_tag(v_x_634_) == 0)
{
lean_object* v___x_635_; lean_object* v_val_636_; lean_object* v___x_637_; 
v___x_635_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0, &l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0);
v_val_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_val_636_);
v___x_637_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_637_, 0, v_a_633_);
lean_ctor_set(v___x_637_, 1, v_val_636_);
lean_ctor_set(v___x_637_, 2, v_x_634_);
return v___x_637_;
}
else
{
lean_object* v_key_638_; lean_object* v_value_639_; lean_object* v_tail_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_655_; 
v_key_638_ = lean_ctor_get(v_x_634_, 0);
v_value_639_ = lean_ctor_get(v_x_634_, 1);
v_tail_640_ = lean_ctor_get(v_x_634_, 2);
v_isSharedCheck_655_ = !lean_is_exclusive(v_x_634_);
if (v_isSharedCheck_655_ == 0)
{
v___x_642_ = v_x_634_;
v_isShared_643_ = v_isSharedCheck_655_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_tail_640_);
lean_inc(v_value_639_);
lean_inc(v_key_638_);
lean_dec(v_x_634_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_655_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
uint8_t v___x_644_; 
v___x_644_ = lean_nat_dec_eq(v_key_638_, v_a_633_);
if (v___x_644_ == 0)
{
lean_object* v_tail_645_; lean_object* v___x_647_; 
v_tail_645_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(v_a_633_, v_tail_640_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 2, v_tail_645_);
v___x_647_ = v___x_642_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_key_638_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_value_639_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v_tail_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v_val_651_; lean_object* v___x_653_; 
lean_dec(v_key_638_);
v___x_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_649_, 0, v_value_639_);
v___x_650_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v___x_649_);
lean_dec_ref_known(v___x_649_, 1);
v_val_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_val_651_);
lean_dec(v___x_650_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 1, v_val_651_);
lean_ctor_set(v___x_642_, 0, v_a_633_);
v___x_653_ = v___x_642_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_633_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_val_651_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v_tail_640_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_656_, lean_object* v_x_657_){
_start:
{
if (lean_obj_tag(v_x_657_) == 0)
{
return v_x_656_;
}
else
{
lean_object* v_key_658_; lean_object* v_value_659_; lean_object* v_tail_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_683_; 
v_key_658_ = lean_ctor_get(v_x_657_, 0);
v_value_659_ = lean_ctor_get(v_x_657_, 1);
v_tail_660_ = lean_ctor_get(v_x_657_, 2);
v_isSharedCheck_683_ = !lean_is_exclusive(v_x_657_);
if (v_isSharedCheck_683_ == 0)
{
v___x_662_ = v_x_657_;
v_isShared_663_ = v_isSharedCheck_683_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_tail_660_);
lean_inc(v_value_659_);
lean_inc(v_key_658_);
lean_dec(v_x_657_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_683_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; uint64_t v___x_665_; uint64_t v___x_666_; uint64_t v___x_667_; uint64_t v_fold_668_; uint64_t v___x_669_; uint64_t v___x_670_; uint64_t v___x_671_; size_t v___x_672_; size_t v___x_673_; size_t v___x_674_; size_t v___x_675_; size_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_664_ = lean_array_get_size(v_x_656_);
v___x_665_ = lean_uint64_of_nat(v_key_658_);
v___x_666_ = 32ULL;
v___x_667_ = lean_uint64_shift_right(v___x_665_, v___x_666_);
v_fold_668_ = lean_uint64_xor(v___x_665_, v___x_667_);
v___x_669_ = 16ULL;
v___x_670_ = lean_uint64_shift_right(v_fold_668_, v___x_669_);
v___x_671_ = lean_uint64_xor(v_fold_668_, v___x_670_);
v___x_672_ = lean_uint64_to_usize(v___x_671_);
v___x_673_ = lean_usize_of_nat(v___x_664_);
v___x_674_ = ((size_t)1ULL);
v___x_675_ = lean_usize_sub(v___x_673_, v___x_674_);
v___x_676_ = lean_usize_land(v___x_672_, v___x_675_);
v___x_677_ = lean_array_uget_borrowed(v_x_656_, v___x_676_);
lean_inc(v___x_677_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 2, v___x_677_);
v___x_679_ = v___x_662_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_key_658_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_value_659_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v___x_677_);
v___x_679_ = v_reuseFailAlloc_682_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; 
v___x_680_ = lean_array_uset(v_x_656_, v___x_676_, v___x_679_);
v_x_656_ = v___x_680_;
v_x_657_ = v_tail_660_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(lean_object* v_i_684_, lean_object* v_source_685_, lean_object* v_target_686_){
_start:
{
lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_687_ = lean_array_get_size(v_source_685_);
v___x_688_ = lean_nat_dec_lt(v_i_684_, v___x_687_);
if (v___x_688_ == 0)
{
lean_dec_ref(v_source_685_);
lean_dec(v_i_684_);
return v_target_686_;
}
else
{
lean_object* v_es_689_; lean_object* v___x_690_; lean_object* v_source_691_; lean_object* v_target_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v_es_689_ = lean_array_fget(v_source_685_, v_i_684_);
v___x_690_ = lean_box(0);
v_source_691_ = lean_array_fset(v_source_685_, v_i_684_, v___x_690_);
v_target_692_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(v_target_686_, v_es_689_);
v___x_693_ = lean_unsigned_to_nat(1u);
v___x_694_ = lean_nat_add(v_i_684_, v___x_693_);
lean_dec(v_i_684_);
v_i_684_ = v___x_694_;
v_source_685_ = v_source_691_;
v_target_686_ = v_target_692_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(lean_object* v_data_696_){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v_nbuckets_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_697_ = lean_array_get_size(v_data_696_);
v___x_698_ = lean_unsigned_to_nat(2u);
v_nbuckets_699_ = lean_nat_mul(v___x_697_, v___x_698_);
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_box(0);
v___x_702_ = lean_mk_array(v_nbuckets_699_, v___x_701_);
v___x_703_ = lean_array_propagate_mark(v_data_696_, v___x_702_);
v___x_704_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(v___x_700_, v_data_696_, v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(lean_object* v_a_705_, lean_object* v_x_706_){
_start:
{
if (lean_obj_tag(v_x_706_) == 0)
{
uint8_t v___x_707_; 
v___x_707_ = 0;
return v___x_707_;
}
else
{
lean_object* v_key_708_; lean_object* v_tail_709_; uint8_t v___x_710_; 
v_key_708_ = lean_ctor_get(v_x_706_, 0);
v_tail_709_ = lean_ctor_get(v_x_706_, 2);
v___x_710_ = lean_nat_dec_eq(v_key_708_, v_a_705_);
if (v___x_710_ == 0)
{
v_x_706_ = v_tail_709_;
goto _start;
}
else
{
return v___x_710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_712_, lean_object* v_x_713_){
_start:
{
uint8_t v_res_714_; lean_object* v_r_715_; 
v_res_714_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_712_, v_x_713_);
lean_dec(v_x_713_);
lean_dec(v_a_712_);
v_r_715_ = lean_box(v_res_714_);
return v_r_715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(lean_object* v_m_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_size_718_; lean_object* v_buckets_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_767_; 
v_size_718_ = lean_ctor_get(v_m_716_, 0);
v_buckets_719_ = lean_ctor_get(v_m_716_, 1);
v_isSharedCheck_767_ = !lean_is_exclusive(v_m_716_);
if (v_isSharedCheck_767_ == 0)
{
v___x_721_ = v_m_716_;
v_isShared_722_ = v_isSharedCheck_767_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_buckets_719_);
lean_inc(v_size_718_);
lean_dec(v_m_716_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_767_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; uint64_t v___x_724_; uint64_t v___x_725_; uint64_t v___x_726_; uint64_t v_fold_727_; uint64_t v___x_728_; uint64_t v___x_729_; uint64_t v___x_730_; size_t v___x_731_; size_t v___x_732_; size_t v___x_733_; size_t v___x_734_; size_t v___x_735_; lean_object* v_bkt_736_; uint8_t v___x_737_; 
v___x_723_ = lean_array_get_size(v_buckets_719_);
v___x_724_ = lean_uint64_of_nat(v_a_717_);
v___x_725_ = 32ULL;
v___x_726_ = lean_uint64_shift_right(v___x_724_, v___x_725_);
v_fold_727_ = lean_uint64_xor(v___x_724_, v___x_726_);
v___x_728_ = 16ULL;
v___x_729_ = lean_uint64_shift_right(v_fold_727_, v___x_728_);
v___x_730_ = lean_uint64_xor(v_fold_727_, v___x_729_);
v___x_731_ = lean_uint64_to_usize(v___x_730_);
v___x_732_ = lean_usize_of_nat(v___x_723_);
v___x_733_ = ((size_t)1ULL);
v___x_734_ = lean_usize_sub(v___x_732_, v___x_733_);
v___x_735_ = lean_usize_land(v___x_731_, v___x_734_);
v_bkt_736_ = lean_array_uget_borrowed(v_buckets_719_, v___x_735_);
v___x_737_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_717_, v_bkt_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; lean_object* v_size_x27_739_; lean_object* v___x_740_; lean_object* v_buckets_x27_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_738_ = lean_unsigned_to_nat(1u);
v_size_x27_739_ = lean_nat_add(v_size_718_, v___x_738_);
lean_dec(v_size_718_);
lean_inc(v_bkt_736_);
v___x_740_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_740_, 0, v_a_717_);
lean_ctor_set(v___x_740_, 1, v___x_738_);
lean_ctor_set(v___x_740_, 2, v_bkt_736_);
v_buckets_x27_741_ = lean_array_uset(v_buckets_719_, v___x_735_, v___x_740_);
v___x_742_ = lean_unsigned_to_nat(4u);
v___x_743_ = lean_nat_mul(v_size_x27_739_, v___x_742_);
v___x_744_ = lean_unsigned_to_nat(3u);
v___x_745_ = lean_nat_div(v___x_743_, v___x_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_array_get_size(v_buckets_x27_741_);
v___x_747_ = lean_nat_dec_le(v___x_745_, v___x_746_);
lean_dec(v___x_745_);
if (v___x_747_ == 0)
{
lean_object* v_val_748_; lean_object* v___x_750_; 
v_val_748_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_741_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 1, v_val_748_);
lean_ctor_set(v___x_721_, 0, v_size_x27_739_);
v___x_750_ = v___x_721_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_size_x27_739_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_val_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
else
{
lean_object* v___x_753_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 1, v_buckets_x27_741_);
lean_ctor_set(v___x_721_, 0, v_size_x27_739_);
v___x_753_ = v___x_721_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_size_x27_739_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_buckets_x27_741_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
else
{
lean_object* v___x_755_; lean_object* v_buckets_x27_756_; lean_object* v_bkt_x27_757_; lean_object* v___y_759_; uint8_t v___x_764_; 
lean_inc(v_bkt_736_);
v___x_755_ = lean_box(0);
v_buckets_x27_756_ = lean_array_uset(v_buckets_719_, v___x_735_, v___x_755_);
lean_inc(v_a_717_);
v_bkt_x27_757_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(v_a_717_, v_bkt_736_);
v___x_764_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_717_, v_bkt_x27_757_);
lean_dec(v_a_717_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = lean_unsigned_to_nat(1u);
v___x_766_ = lean_nat_sub(v_size_718_, v___x_765_);
lean_dec(v_size_718_);
v___y_759_ = v___x_766_;
goto v___jp_758_;
}
else
{
v___y_759_ = v_size_718_;
goto v___jp_758_;
}
v___jp_758_:
{
lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_760_ = lean_array_uset(v_buckets_x27_756_, v___x_735_, v_bkt_x27_757_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 1, v___x_760_);
lean_ctor_set(v___x_721_, 0, v___y_759_);
v___x_762_ = v___x_721_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___y_759_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(lean_object* v_coeff_768_, lean_object* v_e_769_, lean_object* v_a_770_){
_start:
{
lean_object* v___x_772_; lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_790_; 
v___x_772_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_769_, v_a_770_);
v_a_773_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_790_ == 0)
{
v___x_775_ = v___x_772_;
v_isShared_776_ = v_isSharedCheck_790_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_790_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v_fst_777_; lean_object* v_snd_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_789_; 
v_fst_777_ = lean_ctor_get(v_a_773_, 0);
v_snd_778_ = lean_ctor_get(v_a_773_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v_a_773_);
if (v_isSharedCheck_789_ == 0)
{
v___x_780_ = v_a_773_;
v_isShared_781_ = v_isSharedCheck_789_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_snd_778_);
lean_inc(v_fst_777_);
lean_dec(v_a_773_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_789_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(v_coeff_768_, v_fst_777_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_782_);
v___x_784_ = v___x_780_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_snd_778_);
v___x_784_ = v_reuseFailAlloc_788_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_786_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_784_);
v___x_786_ = v___x_775_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___boxed(lean_object* v_coeff_791_, lean_object* v_e_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_791_, v_e_792_, v_a_793_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(lean_object* v_coeff_796_, lean_object* v_e_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_796_, v_e_797_, v_a_798_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___boxed(lean_object* v_coeff_807_, lean_object* v_e_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(v_coeff_807_, v_e_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
return v_res_817_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(lean_object* v_00_u03b2_818_, lean_object* v_a_819_, lean_object* v_x_820_){
_start:
{
uint8_t v___x_821_; 
v___x_821_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_819_, v_x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_822_, lean_object* v_a_823_, lean_object* v_x_824_){
_start:
{
uint8_t v_res_825_; lean_object* v_r_826_; 
v_res_825_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(v_00_u03b2_822_, v_a_823_, v_x_824_);
lean_dec(v_x_824_);
lean_dec(v_a_823_);
v_r_826_ = lean_box(v_res_825_);
return v_r_826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1(lean_object* v_00_u03b2_827_, lean_object* v_data_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_data_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_830_, lean_object* v_i_831_, lean_object* v_source_832_, lean_object* v_target_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(v_i_831_, v_source_832_, v_target_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_835_, lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_836_, v_x_837_);
return v___x_838_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_839_; double v___x_840_; 
v___x_839_ = lean_unsigned_to_nat(0u);
v___x_840_ = lean_float_of_nat(v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(lean_object* v_cls_844_, lean_object* v_msg_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_ref_852_; lean_object* v___x_853_; lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_899_; 
v_ref_852_ = lean_ctor_get(v___y_849_, 2);
v___x_853_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_845_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_899_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_899_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_899_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v_traceState_859_; lean_object* v_env_860_; lean_object* v_nextMacroScope_861_; lean_object* v_ngen_862_; lean_object* v_auxDeclNGen_863_; lean_object* v_cache_864_; lean_object* v_messages_865_; lean_object* v_infoState_866_; lean_object* v_snapshotTasks_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_898_; 
v___x_858_ = lean_st_ref_take(v___y_850_);
v_traceState_859_ = lean_ctor_get(v___x_858_, 4);
v_env_860_ = lean_ctor_get(v___x_858_, 0);
v_nextMacroScope_861_ = lean_ctor_get(v___x_858_, 1);
v_ngen_862_ = lean_ctor_get(v___x_858_, 2);
v_auxDeclNGen_863_ = lean_ctor_get(v___x_858_, 3);
v_cache_864_ = lean_ctor_get(v___x_858_, 5);
v_messages_865_ = lean_ctor_get(v___x_858_, 6);
v_infoState_866_ = lean_ctor_get(v___x_858_, 7);
v_snapshotTasks_867_ = lean_ctor_get(v___x_858_, 8);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_898_ == 0)
{
v___x_869_ = v___x_858_;
v_isShared_870_ = v_isSharedCheck_898_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_snapshotTasks_867_);
lean_inc(v_infoState_866_);
lean_inc(v_messages_865_);
lean_inc(v_cache_864_);
lean_inc(v_traceState_859_);
lean_inc(v_auxDeclNGen_863_);
lean_inc(v_ngen_862_);
lean_inc(v_nextMacroScope_861_);
lean_inc(v_env_860_);
lean_dec(v___x_858_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_898_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
uint64_t v_tid_871_; lean_object* v_traces_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_897_; 
v_tid_871_ = lean_ctor_get_uint64(v_traceState_859_, sizeof(void*)*1);
v_traces_872_ = lean_ctor_get(v_traceState_859_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v_traceState_859_);
if (v_isSharedCheck_897_ == 0)
{
v___x_874_ = v_traceState_859_;
v_isShared_875_ = v_isSharedCheck_897_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_traces_872_);
lean_dec(v_traceState_859_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_897_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; double v___x_877_; uint8_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_876_ = lean_box(0);
v___x_877_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_878_ = 0;
v___x_879_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_880_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_880_, 0, v_cls_844_);
lean_ctor_set(v___x_880_, 1, v___x_876_);
lean_ctor_set(v___x_880_, 2, v___x_879_);
lean_ctor_set_float(v___x_880_, sizeof(void*)*3, v___x_877_);
lean_ctor_set_float(v___x_880_, sizeof(void*)*3 + 8, v___x_877_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*3 + 16, v___x_878_);
v___x_881_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_882_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_882_, 0, v___x_880_);
lean_ctor_set(v___x_882_, 1, v_a_854_);
lean_ctor_set(v___x_882_, 2, v___x_881_);
lean_inc(v_ref_852_);
v___x_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_883_, 0, v_ref_852_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = l_Lean_PersistentArray_push___redArg(v_traces_872_, v___x_883_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_884_);
v___x_886_ = v___x_874_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_884_);
lean_ctor_set_uint64(v_reuseFailAlloc_896_, sizeof(void*)*1, v_tid_871_);
v___x_886_ = v_reuseFailAlloc_896_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 4, v___x_886_);
v___x_888_ = v___x_869_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_env_860_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_nextMacroScope_861_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_ngen_862_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v_auxDeclNGen_863_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_895_, 5, v_cache_864_);
lean_ctor_set(v_reuseFailAlloc_895_, 6, v_messages_865_);
lean_ctor_set(v_reuseFailAlloc_895_, 7, v_infoState_866_);
lean_ctor_set(v_reuseFailAlloc_895_, 8, v_snapshotTasks_867_);
v___x_888_ = v_reuseFailAlloc_895_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_889_ = lean_st_ref_put(v___y_850_, v___x_888_);
v___x_890_ = lean_box(0);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v___y_846_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_891_);
v___x_893_ = v___x_856_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___boxed(lean_object* v_cls_900_, lean_object* v_msg_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_900_, v_msg_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
return v_res_908_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6(void){
_start:
{
lean_object* v_cls_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_cls_919_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_920_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_921_ = l_Lean_Name_append(v___x_920_, v_cls_919_);
return v___x_921_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__7));
v___x_924_ = l_Lean_stringToMessageData(v___x_923_);
return v___x_924_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__9));
v___x_927_ = l_Lean_stringToMessageData(v___x_926_);
return v___x_927_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__11));
v___x_930_ = l_Lean_stringToMessageData(v___x_929_);
return v___x_930_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__13));
v___x_933_ = l_Lean_stringToMessageData(v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(lean_object* v_op_934_, lean_object* v_coeff_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
if (lean_obj_tag(v_a_936_) == 5)
{
lean_object* v_fn_945_; 
v_fn_945_ = lean_ctor_get(v_a_936_, 0);
if (lean_obj_tag(v_fn_945_) == 5)
{
lean_object* v_arg_946_; lean_object* v_fn_947_; lean_object* v_arg_948_; uint8_t v___x_949_; 
v_arg_946_ = lean_ctor_get(v_a_936_, 1);
v_fn_947_ = lean_ctor_get(v_fn_945_, 0);
v_arg_948_ = lean_ctor_get(v_fn_945_, 1);
lean_inc_ref(v_fn_947_);
v___x_949_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(v_fn_947_);
if (v___x_949_ == 0)
{
lean_object* v_toCold_950_; lean_object* v_options_951_; uint8_t v_hasTrace_952_; 
v_toCold_950_ = lean_ctor_get(v_a_942_, 0);
v_options_951_ = lean_ctor_get(v_toCold_950_, 2);
v_hasTrace_952_ = lean_ctor_get_uint8(v_options_951_, sizeof(void*)*1);
if (v_hasTrace_952_ == 0)
{
lean_object* v___x_953_; 
lean_dec_ref(v_op_934_);
v___x_953_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_935_, v_a_936_, v_a_937_);
return v___x_953_;
}
else
{
lean_object* v_inheritedTraceOptions_954_; lean_object* v_cls_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v_inheritedTraceOptions_954_ = lean_ctor_get(v_toCold_950_, 11);
v_cls_955_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_956_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_957_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_954_, v_options_951_, v___x_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; 
lean_dec_ref(v_op_934_);
v___x_958_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_935_, v_a_936_, v_a_937_);
return v___x_958_;
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_959_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8);
lean_inc_ref(v_fn_947_);
v___x_960_ = l_Lean_MessageData_ofExpr(v_fn_947_);
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_961_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
lean_inc_ref(v_arg_948_);
v___x_964_ = l_Lean_MessageData_ofExpr(v_arg_948_);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set(v___x_966_, 1, v___x_962_);
lean_inc_ref(v_arg_946_);
v___x_967_ = l_Lean_MessageData_ofExpr(v_arg_946_);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12);
v___x_970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_934_);
v___x_972_ = l_Lean_MessageData_ofExpr(v___x_971_);
v___x_973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_970_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14);
v___x_975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_955_, v___x_975_, v_a_937_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v_snd_978_; lean_object* v___x_979_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v___x_976_, 1);
v_snd_978_ = lean_ctor_get(v_a_977_, 1);
lean_inc(v_snd_978_);
lean_dec(v_a_977_);
v___x_979_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_935_, v_a_936_, v_snd_978_);
return v___x_979_;
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec_ref_known(v_a_936_, 2);
lean_dec_ref(v_coeff_935_);
v_a_980_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_976_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_976_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
}
else
{
lean_object* v___x_988_; 
lean_inc_ref(v_arg_948_);
lean_inc_ref(v_arg_946_);
lean_dec_ref_known(v_a_936_, 2);
lean_inc_ref(v_op_934_);
v___x_988_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_934_, v_coeff_935_, v_arg_948_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v_fst_990_; lean_object* v_snd_991_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_988_, 1);
v_fst_990_ = lean_ctor_get(v_a_989_, 0);
lean_inc(v_fst_990_);
v_snd_991_ = lean_ctor_get(v_a_989_, 1);
lean_inc(v_snd_991_);
lean_dec(v_a_989_);
v_coeff_935_ = v_fst_990_;
v_a_936_ = v_arg_946_;
v_a_937_ = v_snd_991_;
goto _start;
}
else
{
lean_dec_ref(v_arg_946_);
lean_dec_ref(v_op_934_);
return v___x_988_;
}
}
}
else
{
lean_object* v___x_993_; 
lean_dec_ref(v_op_934_);
v___x_993_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_935_, v_a_936_, v_a_937_);
return v___x_993_;
}
}
else
{
lean_object* v___x_994_; 
lean_dec_ref(v_op_934_);
v___x_994_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_935_, v_a_936_, v_a_937_);
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___boxed(lean_object* v_op_995_, lean_object* v_coeff_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_995_, v_coeff_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
lean_dec(v_a_1002_);
lean_dec_ref(v_a_1001_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(lean_object* v_cls_1007_, lean_object* v_msg_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_1007_, v_msg_1008_, v___y_1009_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___boxed(lean_object* v_cls_1018_, lean_object* v_msg_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(v_cls_1018_, v_msg_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
return v_res_1028_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = lean_box(0);
v___x_1030_ = lean_unsigned_to_nat(16u);
v___x_1031_ = lean_mk_array(v___x_1030_, v___x_1029_);
return v___x_1031_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1032_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set(v___x_1034_, 1, v___x_1032_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(lean_object* v_op_1035_, lean_object* v_e_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1046_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_1035_, v___x_1045_, v_e_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___boxed(lean_object* v_op_1047_, lean_object* v_e_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_op_1047_, v_e_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(lean_object* v_a_1058_, lean_object* v_x_1059_){
_start:
{
if (lean_obj_tag(v_x_1059_) == 0)
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_box(0);
return v___x_1060_;
}
else
{
lean_object* v_key_1061_; lean_object* v_value_1062_; lean_object* v_tail_1063_; uint8_t v___x_1064_; 
v_key_1061_ = lean_ctor_get(v_x_1059_, 0);
v_value_1062_ = lean_ctor_get(v_x_1059_, 1);
v_tail_1063_ = lean_ctor_get(v_x_1059_, 2);
v___x_1064_ = lean_nat_dec_eq(v_key_1061_, v_a_1058_);
if (v___x_1064_ == 0)
{
v_x_1059_ = v_tail_1063_;
goto _start;
}
else
{
lean_object* v___x_1066_; 
lean_inc(v_value_1062_);
v___x_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1066_, 0, v_value_1062_);
return v___x_1066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg___boxed(lean_object* v_a_1067_, lean_object* v_x_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1067_, v_x_1068_);
lean_dec(v_x_1068_);
lean_dec(v_a_1067_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(lean_object* v_m_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v_buckets_1072_; lean_object* v___x_1073_; uint64_t v___x_1074_; uint64_t v___x_1075_; uint64_t v___x_1076_; uint64_t v_fold_1077_; uint64_t v___x_1078_; uint64_t v___x_1079_; uint64_t v___x_1080_; size_t v___x_1081_; size_t v___x_1082_; size_t v___x_1083_; size_t v___x_1084_; size_t v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v_buckets_1072_ = lean_ctor_get(v_m_1070_, 1);
v___x_1073_ = lean_array_get_size(v_buckets_1072_);
v___x_1074_ = lean_uint64_of_nat(v_a_1071_);
v___x_1075_ = 32ULL;
v___x_1076_ = lean_uint64_shift_right(v___x_1074_, v___x_1075_);
v_fold_1077_ = lean_uint64_xor(v___x_1074_, v___x_1076_);
v___x_1078_ = 16ULL;
v___x_1079_ = lean_uint64_shift_right(v_fold_1077_, v___x_1078_);
v___x_1080_ = lean_uint64_xor(v_fold_1077_, v___x_1079_);
v___x_1081_ = lean_uint64_to_usize(v___x_1080_);
v___x_1082_ = lean_usize_of_nat(v___x_1073_);
v___x_1083_ = ((size_t)1ULL);
v___x_1084_ = lean_usize_sub(v___x_1082_, v___x_1083_);
v___x_1085_ = lean_usize_land(v___x_1081_, v___x_1084_);
v___x_1086_ = lean_array_uget_borrowed(v_buckets_1072_, v___x_1085_);
v___x_1087_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1071_, v___x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg___boxed(lean_object* v_m_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1088_, v_a_1089_);
lean_dec(v_a_1089_);
lean_dec_ref(v_m_1088_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(lean_object* v_a_1091_, lean_object* v_b_1092_, lean_object* v_x_1093_){
_start:
{
if (lean_obj_tag(v_x_1093_) == 0)
{
lean_dec(v_b_1092_);
lean_dec(v_a_1091_);
return v_x_1093_;
}
else
{
lean_object* v_key_1094_; lean_object* v_value_1095_; lean_object* v_tail_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1108_; 
v_key_1094_ = lean_ctor_get(v_x_1093_, 0);
v_value_1095_ = lean_ctor_get(v_x_1093_, 1);
v_tail_1096_ = lean_ctor_get(v_x_1093_, 2);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_x_1093_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1098_ = v_x_1093_;
v_isShared_1099_ = v_isSharedCheck_1108_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_tail_1096_);
lean_inc(v_value_1095_);
lean_inc(v_key_1094_);
lean_dec(v_x_1093_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1108_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
uint8_t v___x_1100_; 
v___x_1100_ = lean_nat_dec_eq(v_key_1094_, v_a_1091_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1101_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1091_, v_b_1092_, v_tail_1096_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 2, v___x_1101_);
v___x_1103_ = v___x_1098_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_key_1094_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_value_1095_);
lean_ctor_set(v_reuseFailAlloc_1104_, 2, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
else
{
lean_object* v___x_1106_; 
lean_dec(v_value_1095_);
lean_dec(v_key_1094_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 1, v_b_1092_);
lean_ctor_set(v___x_1098_, 0, v_a_1091_);
v___x_1106_ = v___x_1098_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1091_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_b_1092_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v_tail_1096_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(lean_object* v_m_1109_, lean_object* v_a_1110_, lean_object* v_b_1111_){
_start:
{
lean_object* v_size_1112_; lean_object* v_buckets_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1156_; 
v_size_1112_ = lean_ctor_get(v_m_1109_, 0);
v_buckets_1113_ = lean_ctor_get(v_m_1109_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_m_1109_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1115_ = v_m_1109_;
v_isShared_1116_ = v_isSharedCheck_1156_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_buckets_1113_);
lean_inc(v_size_1112_);
lean_dec(v_m_1109_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1156_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; uint64_t v___x_1118_; uint64_t v___x_1119_; uint64_t v___x_1120_; uint64_t v_fold_1121_; uint64_t v___x_1122_; uint64_t v___x_1123_; uint64_t v___x_1124_; size_t v___x_1125_; size_t v___x_1126_; size_t v___x_1127_; size_t v___x_1128_; size_t v___x_1129_; lean_object* v_bkt_1130_; uint8_t v___x_1131_; 
v___x_1117_ = lean_array_get_size(v_buckets_1113_);
v___x_1118_ = lean_uint64_of_nat(v_a_1110_);
v___x_1119_ = 32ULL;
v___x_1120_ = lean_uint64_shift_right(v___x_1118_, v___x_1119_);
v_fold_1121_ = lean_uint64_xor(v___x_1118_, v___x_1120_);
v___x_1122_ = 16ULL;
v___x_1123_ = lean_uint64_shift_right(v_fold_1121_, v___x_1122_);
v___x_1124_ = lean_uint64_xor(v_fold_1121_, v___x_1123_);
v___x_1125_ = lean_uint64_to_usize(v___x_1124_);
v___x_1126_ = lean_usize_of_nat(v___x_1117_);
v___x_1127_ = ((size_t)1ULL);
v___x_1128_ = lean_usize_sub(v___x_1126_, v___x_1127_);
v___x_1129_ = lean_usize_land(v___x_1125_, v___x_1128_);
v_bkt_1130_ = lean_array_uget_borrowed(v_buckets_1113_, v___x_1129_);
v___x_1131_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1110_, v_bkt_1130_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v_size_x27_1133_; lean_object* v___x_1134_; lean_object* v_buckets_x27_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1132_ = lean_unsigned_to_nat(1u);
v_size_x27_1133_ = lean_nat_add(v_size_1112_, v___x_1132_);
lean_dec(v_size_1112_);
lean_inc(v_bkt_1130_);
v___x_1134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1134_, 0, v_a_1110_);
lean_ctor_set(v___x_1134_, 1, v_b_1111_);
lean_ctor_set(v___x_1134_, 2, v_bkt_1130_);
v_buckets_x27_1135_ = lean_array_uset(v_buckets_1113_, v___x_1129_, v___x_1134_);
v___x_1136_ = lean_unsigned_to_nat(4u);
v___x_1137_ = lean_nat_mul(v_size_x27_1133_, v___x_1136_);
v___x_1138_ = lean_unsigned_to_nat(3u);
v___x_1139_ = lean_nat_div(v___x_1137_, v___x_1138_);
lean_dec(v___x_1137_);
v___x_1140_ = lean_array_get_size(v_buckets_x27_1135_);
v___x_1141_ = lean_nat_dec_le(v___x_1139_, v___x_1140_);
lean_dec(v___x_1139_);
if (v___x_1141_ == 0)
{
lean_object* v_val_1142_; lean_object* v___x_1144_; 
v_val_1142_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_1135_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 1, v_val_1142_);
lean_ctor_set(v___x_1115_, 0, v_size_x27_1133_);
v___x_1144_ = v___x_1115_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_size_x27_1133_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_val_1142_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
else
{
lean_object* v___x_1147_; 
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 1, v_buckets_x27_1135_);
lean_ctor_set(v___x_1115_, 0, v_size_x27_1133_);
v___x_1147_ = v___x_1115_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_size_x27_1133_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_buckets_x27_1135_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
else
{
lean_object* v___x_1149_; lean_object* v_buckets_x27_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1154_; 
lean_inc(v_bkt_1130_);
v___x_1149_ = lean_box(0);
v_buckets_x27_1150_ = lean_array_uset(v_buckets_1113_, v___x_1129_, v___x_1149_);
v___x_1151_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1110_, v_b_1111_, v_bkt_1130_);
v___x_1152_ = lean_array_uset(v_buckets_x27_1150_, v___x_1129_, v___x_1151_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 1, v___x_1152_);
v___x_1154_ = v___x_1115_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_size_1112_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v___x_1152_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(lean_object* v_snd_1157_, lean_object* v_x_1158_, lean_object* v_x_1159_){
_start:
{
if (lean_obj_tag(v_x_1159_) == 0)
{
return v_x_1158_;
}
else
{
lean_object* v_key_1160_; lean_object* v_value_1161_; lean_object* v_tail_1162_; lean_object* v___y_1164_; lean_object* v___x_1167_; 
v_key_1160_ = lean_ctor_get(v_x_1159_, 0);
lean_inc(v_key_1160_);
v_value_1161_ = lean_ctor_get(v_x_1159_, 1);
lean_inc(v_value_1161_);
v_tail_1162_ = lean_ctor_get(v_x_1159_, 2);
lean_inc(v_tail_1162_);
lean_dec_ref_known(v_x_1159_, 3);
v___x_1167_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_snd_1157_, v_key_1160_);
if (lean_obj_tag(v___x_1167_) == 1)
{
lean_object* v_val_1168_; uint8_t v___x_1169_; 
v_val_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_val_1168_);
lean_dec_ref_known(v___x_1167_, 1);
v___x_1169_ = lean_nat_dec_le(v_value_1161_, v_val_1168_);
if (v___x_1169_ == 0)
{
lean_dec(v_value_1161_);
v___y_1164_ = v_val_1168_;
goto v___jp_1163_;
}
else
{
lean_dec(v_val_1168_);
v___y_1164_ = v_value_1161_;
goto v___jp_1163_;
}
}
else
{
lean_dec(v___x_1167_);
lean_dec(v_value_1161_);
lean_dec(v_key_1160_);
v_x_1159_ = v_tail_1162_;
goto _start;
}
v___jp_1163_:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(v_x_1158_, v_key_1160_, v___y_1164_);
v_x_1158_ = v___x_1165_;
v_x_1159_ = v_tail_1162_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5___boxed(lean_object* v_snd_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(v_snd_1171_, v_x_1172_, v_x_1173_);
lean_dec_ref(v_snd_1171_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(lean_object* v_snd_1175_, lean_object* v_as_1176_, size_t v_i_1177_, size_t v_stop_1178_, lean_object* v_b_1179_){
_start:
{
uint8_t v___x_1180_; 
v___x_1180_ = lean_usize_dec_eq(v_i_1177_, v_stop_1178_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; size_t v___x_1183_; size_t v___x_1184_; 
v___x_1181_ = lean_array_uget_borrowed(v_as_1176_, v_i_1177_);
lean_inc(v___x_1181_);
v___x_1182_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(v_snd_1175_, v_b_1179_, v___x_1181_);
v___x_1183_ = ((size_t)1ULL);
v___x_1184_ = lean_usize_add(v_i_1177_, v___x_1183_);
v_i_1177_ = v___x_1184_;
v_b_1179_ = v___x_1182_;
goto _start;
}
else
{
return v_b_1179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6___boxed(lean_object* v_snd_1186_, lean_object* v_as_1187_, lean_object* v_i_1188_, lean_object* v_stop_1189_, lean_object* v_b_1190_){
_start:
{
size_t v_i_boxed_1191_; size_t v_stop_boxed_1192_; lean_object* v_res_1193_; 
v_i_boxed_1191_ = lean_unbox_usize(v_i_1188_);
lean_dec(v_i_1188_);
v_stop_boxed_1192_ = lean_unbox_usize(v_stop_1189_);
lean_dec(v_stop_1189_);
v_res_1193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1186_, v_as_1187_, v_i_boxed_1191_, v_stop_boxed_1192_, v_b_1190_);
lean_dec_ref(v_as_1187_);
lean_dec_ref(v_snd_1186_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(lean_object* v_commonCnt_1194_, lean_object* v_a_1195_, lean_object* v_x_1196_){
_start:
{
if (lean_obj_tag(v_x_1196_) == 0)
{
lean_dec(v_a_1195_);
return v_x_1196_;
}
else
{
lean_object* v_key_1197_; lean_object* v_value_1198_; lean_object* v_tail_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1212_; 
v_key_1197_ = lean_ctor_get(v_x_1196_, 0);
v_value_1198_ = lean_ctor_get(v_x_1196_, 1);
v_tail_1199_ = lean_ctor_get(v_x_1196_, 2);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_x_1196_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1201_ = v_x_1196_;
v_isShared_1202_ = v_isSharedCheck_1212_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_tail_1199_);
lean_inc(v_value_1198_);
lean_inc(v_key_1197_);
lean_dec(v_x_1196_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1212_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
uint8_t v___x_1203_; 
v___x_1203_ = lean_nat_dec_eq(v_key_1197_, v_a_1195_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1204_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1194_, v_a_1195_, v_tail_1199_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 2, v___x_1204_);
v___x_1206_ = v___x_1201_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_key_1197_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_value_1198_);
lean_ctor_set(v_reuseFailAlloc_1207_, 2, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1210_; 
lean_dec(v_key_1197_);
v___x_1208_ = lean_nat_sub(v_value_1198_, v_commonCnt_1194_);
lean_dec(v_value_1198_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 1, v___x_1208_);
lean_ctor_set(v___x_1201_, 0, v_a_1195_);
v___x_1210_ = v___x_1201_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1195_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1211_, 2, v_tail_1199_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0___boxed(lean_object* v_commonCnt_1213_, lean_object* v_a_1214_, lean_object* v_x_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1213_, v_a_1214_, v_x_1215_);
lean_dec(v_commonCnt_1213_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(lean_object* v_commonCnt_1217_, lean_object* v_m_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_size_1220_; lean_object* v_buckets_1221_; lean_object* v___x_1222_; uint64_t v___x_1223_; uint64_t v___x_1224_; uint64_t v___x_1225_; uint64_t v_fold_1226_; uint64_t v___x_1227_; uint64_t v___x_1228_; uint64_t v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; size_t v___x_1232_; size_t v___x_1233_; size_t v___x_1234_; lean_object* v_bucket_1235_; uint8_t v___x_1236_; 
v_size_1220_ = lean_ctor_get(v_m_1218_, 0);
v_buckets_1221_ = lean_ctor_get(v_m_1218_, 1);
v___x_1222_ = lean_array_get_size(v_buckets_1221_);
v___x_1223_ = lean_uint64_of_nat(v_a_1219_);
v___x_1224_ = 32ULL;
v___x_1225_ = lean_uint64_shift_right(v___x_1223_, v___x_1224_);
v_fold_1226_ = lean_uint64_xor(v___x_1223_, v___x_1225_);
v___x_1227_ = 16ULL;
v___x_1228_ = lean_uint64_shift_right(v_fold_1226_, v___x_1227_);
v___x_1229_ = lean_uint64_xor(v_fold_1226_, v___x_1228_);
v___x_1230_ = lean_uint64_to_usize(v___x_1229_);
v___x_1231_ = lean_usize_of_nat(v___x_1222_);
v___x_1232_ = ((size_t)1ULL);
v___x_1233_ = lean_usize_sub(v___x_1231_, v___x_1232_);
v___x_1234_ = lean_usize_land(v___x_1230_, v___x_1233_);
v_bucket_1235_ = lean_array_uget_borrowed(v_buckets_1221_, v___x_1234_);
v___x_1236_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1219_, v_bucket_1235_);
if (v___x_1236_ == 0)
{
lean_dec(v_a_1219_);
return v_m_1218_;
}
else
{
lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1247_; 
lean_inc(v_bucket_1235_);
lean_inc_ref(v_buckets_1221_);
lean_inc(v_size_1220_);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_m_1218_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; lean_object* v_unused_1249_; 
v_unused_1248_ = lean_ctor_get(v_m_1218_, 1);
lean_dec(v_unused_1248_);
v_unused_1249_ = lean_ctor_get(v_m_1218_, 0);
lean_dec(v_unused_1249_);
v___x_1238_ = v_m_1218_;
v_isShared_1239_ = v_isSharedCheck_1247_;
goto v_resetjp_1237_;
}
else
{
lean_dec(v_m_1218_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1247_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; lean_object* v_buckets_1241_; lean_object* v_bucket_1242_; lean_object* v___x_1243_; lean_object* v___x_1245_; 
v___x_1240_ = lean_box(0);
v_buckets_1241_ = lean_array_uset(v_buckets_1221_, v___x_1234_, v___x_1240_);
v_bucket_1242_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1217_, v_a_1219_, v_bucket_1235_);
v___x_1243_ = lean_array_uset(v_buckets_1241_, v___x_1234_, v_bucket_1242_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 1, v___x_1243_);
v___x_1245_ = v___x_1238_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_size_1220_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v___x_1243_);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0___boxed(lean_object* v_commonCnt_1250_, lean_object* v_m_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_commonCnt_1250_, v_m_1251_, v_a_1252_);
lean_dec(v_commonCnt_1250_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(lean_object* v_x_1254_, lean_object* v_x_1255_){
_start:
{
if (lean_obj_tag(v_x_1255_) == 0)
{
return v_x_1254_;
}
else
{
lean_object* v_key_1256_; lean_object* v_value_1257_; lean_object* v_tail_1258_; lean_object* v___x_1259_; 
v_key_1256_ = lean_ctor_get(v_x_1255_, 0);
lean_inc(v_key_1256_);
v_value_1257_ = lean_ctor_get(v_x_1255_, 1);
lean_inc(v_value_1257_);
v_tail_1258_ = lean_ctor_get(v_x_1255_, 2);
lean_inc(v_tail_1258_);
lean_dec_ref_known(v_x_1255_, 3);
v___x_1259_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_value_1257_, v_x_1254_, v_key_1256_);
lean_dec(v_value_1257_);
v_x_1254_ = v___x_1259_;
v_x_1255_ = v_tail_1258_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(lean_object* v_x_1261_, lean_object* v_x_1262_){
_start:
{
if (lean_obj_tag(v_x_1262_) == 0)
{
return v_x_1261_;
}
else
{
lean_object* v_key_1263_; lean_object* v_value_1264_; lean_object* v_tail_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v_key_1263_ = lean_ctor_get(v_x_1262_, 0);
lean_inc(v_key_1263_);
v_value_1264_ = lean_ctor_get(v_x_1262_, 1);
lean_inc(v_value_1264_);
v_tail_1265_ = lean_ctor_get(v_x_1262_, 2);
lean_inc(v_tail_1265_);
lean_dec_ref_known(v_x_1262_, 3);
v___x_1266_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_value_1264_, v_x_1261_, v_key_1263_);
lean_dec(v_value_1264_);
v___x_1267_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(v___x_1266_, v_tail_1265_);
return v___x_1267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(lean_object* v_as_1268_, size_t v_i_1269_, size_t v_stop_1270_, lean_object* v_b_1271_){
_start:
{
uint8_t v___x_1272_; 
v___x_1272_ = lean_usize_dec_eq(v_i_1269_, v_stop_1270_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; lean_object* v___x_1274_; size_t v___x_1275_; size_t v___x_1276_; 
v___x_1273_ = lean_array_uget_borrowed(v_as_1268_, v_i_1269_);
lean_inc(v___x_1273_);
v___x_1274_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(v_b_1271_, v___x_1273_);
v___x_1275_ = ((size_t)1ULL);
v___x_1276_ = lean_usize_add(v_i_1269_, v___x_1275_);
v_i_1269_ = v___x_1276_;
v_b_1271_ = v___x_1274_;
goto _start;
}
else
{
return v_b_1271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2___boxed(lean_object* v_as_1278_, lean_object* v_i_1279_, lean_object* v_stop_1280_, lean_object* v_b_1281_){
_start:
{
size_t v_i_boxed_1282_; size_t v_stop_boxed_1283_; lean_object* v_res_1284_; 
v_i_boxed_1282_ = lean_unbox_usize(v_i_1279_);
lean_dec(v_i_1279_);
v_stop_boxed_1283_ = lean_unbox_usize(v_stop_1280_);
lean_dec(v_stop_1280_);
v_res_1284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_as_1278_, v_i_boxed_1282_, v_stop_boxed_1283_, v_b_1281_);
lean_dec_ref(v_as_1278_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(lean_object* v_x_1285_, lean_object* v_y_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v___y_1290_; lean_object* v_fst_1291_; lean_object* v_snd_1292_; lean_object* v_size_1296_; lean_object* v_buckets_1297_; lean_object* v_size_1298_; lean_object* v_buckets_1299_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v_buckets_1308_; lean_object* v___y_1309_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v_buckets_1320_; lean_object* v_fst_1328_; lean_object* v_buckets_1329_; lean_object* v_snd_1330_; uint8_t v___x_1340_; 
v_size_1296_ = lean_ctor_get(v_y_1286_, 0);
lean_inc(v_size_1296_);
v_buckets_1297_ = lean_ctor_get(v_y_1286_, 1);
v_size_1298_ = lean_ctor_get(v_x_1285_, 0);
lean_inc(v_size_1298_);
v_buckets_1299_ = lean_ctor_get(v_x_1285_, 1);
v___x_1340_ = lean_nat_dec_lt(v_size_1296_, v_size_1298_);
if (v___x_1340_ == 0)
{
lean_inc_ref(v_buckets_1299_);
v_fst_1328_ = v_x_1285_;
v_buckets_1329_ = v_buckets_1299_;
v_snd_1330_ = v_y_1286_;
goto v___jp_1327_;
}
else
{
lean_inc_ref(v_buckets_1297_);
v_fst_1328_ = v_y_1286_;
v_buckets_1329_ = v_buckets_1297_;
v_snd_1330_ = v_x_1285_;
goto v___jp_1327_;
}
v___jp_1289_:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1293_, 0, v___y_1290_);
lean_ctor_set(v___x_1293_, 1, v_fst_1291_);
lean_ctor_set(v___x_1293_, 2, v_snd_1292_);
v___x_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
lean_ctor_set(v___x_1294_, 1, v_a_1287_);
v___x_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
return v___x_1295_;
}
v___jp_1300_:
{
uint8_t v___x_1304_; 
v___x_1304_ = lean_nat_dec_lt(v_size_1296_, v_size_1298_);
lean_dec(v_size_1298_);
lean_dec(v_size_1296_);
if (v___x_1304_ == 0)
{
v___y_1290_ = v___y_1302_;
v_fst_1291_ = v___y_1301_;
v_snd_1292_ = v___y_1303_;
goto v___jp_1289_;
}
else
{
v___y_1290_ = v___y_1302_;
v_fst_1291_ = v___y_1303_;
v_snd_1292_ = v___y_1301_;
goto v___jp_1289_;
}
}
v___jp_1305_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v___x_1310_ = lean_unsigned_to_nat(0u);
v___x_1311_ = lean_array_get_size(v_buckets_1308_);
v___x_1312_ = lean_nat_dec_lt(v___x_1310_, v___x_1311_);
if (v___x_1312_ == 0)
{
lean_dec_ref(v_buckets_1308_);
v___y_1301_ = v___y_1309_;
v___y_1302_ = v___y_1307_;
v___y_1303_ = v___y_1306_;
goto v___jp_1300_;
}
else
{
size_t v___x_1313_; size_t v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = ((size_t)0ULL);
v___x_1314_ = lean_usize_of_nat(v___x_1311_);
v___x_1315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1308_, v___x_1313_, v___x_1314_, v___y_1306_);
lean_dec_ref(v_buckets_1308_);
v___y_1301_ = v___y_1309_;
v___y_1302_ = v___y_1307_;
v___y_1303_ = v___x_1315_;
goto v___jp_1300_;
}
}
v___jp_1316_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1321_ = lean_unsigned_to_nat(0u);
v___x_1322_ = lean_array_get_size(v_buckets_1320_);
v___x_1323_ = lean_nat_dec_lt(v___x_1321_, v___x_1322_);
if (v___x_1323_ == 0)
{
v___y_1306_ = v___y_1317_;
v___y_1307_ = v___y_1319_;
v_buckets_1308_ = v_buckets_1320_;
v___y_1309_ = v___y_1318_;
goto v___jp_1305_;
}
else
{
size_t v___x_1324_; size_t v___x_1325_; lean_object* v___x_1326_; 
v___x_1324_ = ((size_t)0ULL);
v___x_1325_ = lean_usize_of_nat(v___x_1322_);
v___x_1326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1320_, v___x_1324_, v___x_1325_, v___y_1318_);
v___y_1306_ = v___y_1317_;
v___y_1307_ = v___y_1319_;
v_buckets_1308_ = v_buckets_1320_;
v___y_1309_ = v___x_1326_;
goto v___jp_1305_;
}
}
v___jp_1327_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1331_ = lean_unsigned_to_nat(0u);
v___x_1332_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1333_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1334_ = lean_array_get_size(v_buckets_1329_);
v___x_1335_ = lean_nat_dec_lt(v___x_1331_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_dec_ref(v_buckets_1329_);
v___y_1317_ = v_snd_1330_;
v___y_1318_ = v_fst_1328_;
v___y_1319_ = v___x_1333_;
v_buckets_1320_ = v___x_1332_;
goto v___jp_1316_;
}
else
{
size_t v___x_1336_; size_t v___x_1337_; lean_object* v___x_1338_; lean_object* v_buckets_1339_; 
v___x_1336_ = ((size_t)0ULL);
v___x_1337_ = lean_usize_of_nat(v___x_1334_);
v___x_1338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1330_, v_buckets_1329_, v___x_1336_, v___x_1337_, v___x_1333_);
lean_dec_ref(v_buckets_1329_);
v_buckets_1339_ = lean_ctor_get(v___x_1338_, 1);
lean_inc_ref(v_buckets_1339_);
v___y_1317_ = v_snd_1330_;
v___y_1318_ = v_fst_1328_;
v___y_1319_ = v___x_1338_;
v_buckets_1320_ = v_buckets_1339_;
goto v___jp_1316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg___boxed(lean_object* v_x_1341_, lean_object* v_y_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1341_, v_y_1342_, v_a_1343_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(lean_object* v_x_1346_, lean_object* v_y_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1346_, v_y_1347_, v_a_1348_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___boxed(lean_object* v_x_1357_, lean_object* v_y_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(v_x_1357_, v_y_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3(lean_object* v_00_u03b2_1368_, lean_object* v_m_1369_, lean_object* v_a_1370_, lean_object* v_b_1371_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(v_m_1369_, v_a_1370_, v_b_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4(lean_object* v_00_u03b2_1373_, lean_object* v_m_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1374_, v_a_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___boxed(lean_object* v_00_u03b2_1377_, lean_object* v_m_1378_, lean_object* v_a_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4(v_00_u03b2_1377_, v_m_1378_, v_a_1379_);
lean_dec(v_a_1379_);
lean_dec_ref(v_m_1378_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5(lean_object* v_00_u03b2_1381_, lean_object* v_a_1382_, lean_object* v_b_1383_, lean_object* v_x_1384_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1382_, v_b_1383_, v_x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7(lean_object* v_00_u03b2_1386_, lean_object* v_a_1387_, lean_object* v_x_1388_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1387_, v_x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1390_, lean_object* v_a_1391_, lean_object* v_x_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7(v_00_u03b2_1390_, v_a_1391_, v_x_1392_);
lean_dec(v_x_1392_);
lean_dec(v_a_1391_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
if (lean_obj_tag(v_x_1395_) == 0)
{
return v_x_1394_;
}
else
{
lean_object* v_key_1396_; lean_object* v_value_1397_; lean_object* v_tail_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v_key_1396_ = lean_ctor_get(v_x_1395_, 0);
v_value_1397_ = lean_ctor_get(v_x_1395_, 1);
v_tail_1398_ = lean_ctor_get(v_x_1395_, 2);
lean_inc(v_value_1397_);
lean_inc(v_key_1396_);
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v_key_1396_);
lean_ctor_set(v___x_1399_, 1, v_value_1397_);
v___x_1400_ = lean_array_push(v_x_1394_, v___x_1399_);
v_x_1394_ = v___x_1400_;
v_x_1395_ = v_tail_1398_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___boxed(lean_object* v_x_1402_, lean_object* v_x_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(v_x_1402_, v_x_1403_);
lean_dec(v_x_1403_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(lean_object* v_as_1405_, size_t v_i_1406_, size_t v_stop_1407_, lean_object* v_b_1408_){
_start:
{
uint8_t v___x_1409_; 
v___x_1409_ = lean_usize_dec_eq(v_i_1406_, v_stop_1407_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1411_; size_t v___x_1412_; size_t v___x_1413_; 
v___x_1410_ = lean_array_uget_borrowed(v_as_1405_, v_i_1406_);
v___x_1411_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(v_b_1408_, v___x_1410_);
v___x_1412_ = ((size_t)1ULL);
v___x_1413_ = lean_usize_add(v_i_1406_, v___x_1412_);
v_i_1406_ = v___x_1413_;
v_b_1408_ = v___x_1411_;
goto _start;
}
else
{
return v_b_1408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4___boxed(lean_object* v_as_1415_, lean_object* v_i_1416_, lean_object* v_stop_1417_, lean_object* v_b_1418_){
_start:
{
size_t v_i_boxed_1419_; size_t v_stop_boxed_1420_; lean_object* v_res_1421_; 
v_i_boxed_1419_ = lean_unbox_usize(v_i_1416_);
lean_dec(v_i_1416_);
v_stop_boxed_1420_ = lean_unbox_usize(v_stop_1417_);
lean_dec(v_stop_1417_);
v_res_1421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_as_1415_, v_i_boxed_1419_, v_stop_boxed_1420_, v_b_1418_);
lean_dec_ref(v_as_1415_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(lean_object* v_upperBound_1422_, lean_object* v___x_1423_, lean_object* v_op_1424_, lean_object* v_a_1425_, lean_object* v_b_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v___y_1430_; uint8_t v___x_1434_; 
v___x_1434_ = lean_nat_dec_lt(v_a_1425_, v_upperBound_1422_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_dec(v_a_1425_);
lean_dec_ref(v_op_1424_);
lean_dec_ref(v___x_1423_);
v___x_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1435_, 0, v_b_1426_);
lean_ctor_set(v___x_1435_, 1, v___y_1427_);
v___x_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
return v___x_1436_;
}
else
{
if (lean_obj_tag(v_b_1426_) == 0)
{
lean_object* v___x_1437_; 
lean_inc_ref(v___x_1423_);
v___x_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1423_);
v___y_1430_ = v___x_1437_;
goto v___jp_1429_;
}
else
{
lean_object* v_val_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1447_; 
v_val_1438_ = lean_ctor_get(v_b_1426_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_b_1426_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1440_ = v_b_1426_;
v_isShared_1441_ = v_isSharedCheck_1447_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_val_1438_);
lean_dec(v_b_1426_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1447_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1445_; 
lean_inc_ref(v_op_1424_);
v___x_1442_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_1424_);
lean_inc_ref(v___x_1423_);
v___x_1443_ = l_Lean_mkAppB(v___x_1442_, v_val_1438_, v___x_1423_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1443_);
v___x_1445_ = v___x_1440_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
v___y_1430_ = v___x_1445_;
goto v___jp_1429_;
}
}
}
}
v___jp_1429_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = lean_unsigned_to_nat(1u);
v___x_1432_ = lean_nat_add(v_a_1425_, v___x_1431_);
lean_dec(v_a_1425_);
v_a_1425_ = v___x_1432_;
v_b_1426_ = v___y_1430_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg___boxed(lean_object* v_upperBound_1448_, lean_object* v___x_1449_, lean_object* v_op_1450_, lean_object* v_a_1451_, lean_object* v_b_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1448_, v___x_1449_, v_op_1450_, v_a_1451_, v_b_1452_, v___y_1453_);
lean_dec(v_upperBound_1448_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(lean_object* v_op_1456_, lean_object* v_as_1457_, size_t v_sz_1458_, size_t v_i_1459_, lean_object* v_b_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
uint8_t v___x_1469_; 
v___x_1469_ = lean_usize_dec_lt(v_i_1459_, v_sz_1458_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_dec_ref(v_op_1456_);
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v_b_1460_);
lean_ctor_set(v___x_1470_, 1, v___y_1461_);
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
else
{
lean_object* v_a_1472_; lean_object* v_fst_1473_; lean_object* v_snd_1474_; lean_object* v_varToExpr_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v_a_1472_ = lean_array_uget_borrowed(v_as_1457_, v_i_1459_);
v_fst_1473_ = lean_ctor_get(v_a_1472_, 0);
v_snd_1474_ = lean_ctor_get(v_a_1472_, 1);
v_varToExpr_1475_ = lean_ctor_get(v___y_1461_, 2);
v___x_1476_ = l_Lean_instInhabitedExpr;
v___x_1477_ = lean_unsigned_to_nat(0u);
v___x_1478_ = lean_array_get(v___x_1476_, v_varToExpr_1475_, v_fst_1473_);
lean_inc_ref(v_op_1456_);
v___x_1479_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_snd_1474_, v___x_1478_, v_op_1456_, v___x_1477_, v_b_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v_fst_1481_; lean_object* v_snd_1482_; size_t v___x_1483_; size_t v___x_1484_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1480_);
lean_dec_ref_known(v___x_1479_, 1);
v_fst_1481_ = lean_ctor_get(v_a_1480_, 0);
lean_inc(v_fst_1481_);
v_snd_1482_ = lean_ctor_get(v_a_1480_, 1);
lean_inc(v_snd_1482_);
lean_dec(v_a_1480_);
v___x_1483_ = ((size_t)1ULL);
v___x_1484_ = lean_usize_add(v_i_1459_, v___x_1483_);
v_i_1459_ = v___x_1484_;
v_b_1460_ = v_fst_1481_;
v___y_1461_ = v_snd_1482_;
goto _start;
}
else
{
lean_dec_ref(v_op_1456_);
return v___x_1479_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1___boxed(lean_object* v_op_1486_, lean_object* v_as_1487_, lean_object* v_sz_1488_, lean_object* v_i_1489_, lean_object* v_b_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
size_t v_sz_boxed_1499_; size_t v_i_boxed_1500_; lean_object* v_res_1501_; 
v_sz_boxed_1499_ = lean_unbox_usize(v_sz_1488_);
lean_dec(v_sz_1488_);
v_i_boxed_1500_ = lean_unbox_usize(v_i_1489_);
lean_dec(v_i_1489_);
v_res_1501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1486_, v_as_1487_, v_sz_boxed_1499_, v_i_boxed_1500_, v_b_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec_ref(v_as_1487_);
return v_res_1501_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(lean_object* v_x1_1502_, lean_object* v_x2_1503_){
_start:
{
lean_object* v_fst_1504_; lean_object* v_fst_1505_; uint8_t v___x_1506_; 
v_fst_1504_ = lean_ctor_get(v_x1_1502_, 0);
v_fst_1505_ = lean_ctor_get(v_x2_1503_, 0);
v___x_1506_ = lean_nat_dec_lt(v_fst_1504_, v_fst_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed(lean_object* v_x1_1507_, lean_object* v_x2_1508_){
_start:
{
uint8_t v_res_1509_; lean_object* v_r_1510_; 
v_res_1509_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v_x1_1507_, v_x2_1508_);
lean_dec_ref(v_x2_1508_);
lean_dec_ref(v_x1_1507_);
v_r_1510_ = lean_box(v_res_1509_);
return v_r_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(lean_object* v_hi_1511_, lean_object* v_pivot_1512_, lean_object* v_as_1513_, lean_object* v_i_1514_, lean_object* v_k_1515_){
_start:
{
uint8_t v___x_1516_; 
v___x_1516_ = lean_nat_dec_lt(v_k_1515_, v_hi_1511_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
lean_dec(v_k_1515_);
v___x_1517_ = lean_array_fswap(v_as_1513_, v_i_1514_, v_hi_1511_);
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v_i_1514_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
return v___x_1518_;
}
else
{
lean_object* v___x_1519_; lean_object* v_fst_1520_; lean_object* v_fst_1521_; uint8_t v___x_1522_; 
v___x_1519_ = lean_array_fget_borrowed(v_as_1513_, v_k_1515_);
v_fst_1520_ = lean_ctor_get(v___x_1519_, 0);
v_fst_1521_ = lean_ctor_get(v_pivot_1512_, 0);
v___x_1522_ = lean_nat_dec_lt(v_fst_1520_, v_fst_1521_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = lean_unsigned_to_nat(1u);
v___x_1524_ = lean_nat_add(v_k_1515_, v___x_1523_);
lean_dec(v_k_1515_);
v_k_1515_ = v___x_1524_;
goto _start;
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1526_ = lean_array_fswap(v_as_1513_, v_i_1514_, v_k_1515_);
v___x_1527_ = lean_unsigned_to_nat(1u);
v___x_1528_ = lean_nat_add(v_i_1514_, v___x_1527_);
lean_dec(v_i_1514_);
v___x_1529_ = lean_nat_add(v_k_1515_, v___x_1527_);
lean_dec(v_k_1515_);
v_as_1513_ = v___x_1526_;
v_i_1514_ = v___x_1528_;
v_k_1515_ = v___x_1529_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg___boxed(lean_object* v_hi_1531_, lean_object* v_pivot_1532_, lean_object* v_as_1533_, lean_object* v_i_1534_, lean_object* v_k_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1531_, v_pivot_1532_, v_as_1533_, v_i_1534_, v_k_1535_);
lean_dec_ref(v_pivot_1532_);
lean_dec(v_hi_1531_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(lean_object* v_n_1537_, lean_object* v_as_1538_, lean_object* v_lo_1539_, lean_object* v_hi_1540_){
_start:
{
lean_object* v___y_1542_; uint8_t v___x_1552_; 
v___x_1552_ = lean_nat_dec_lt(v_lo_1539_, v_hi_1540_);
if (v___x_1552_ == 0)
{
lean_dec(v_lo_1539_);
return v_as_1538_;
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v_mid_1555_; lean_object* v___y_1557_; lean_object* v___y_1563_; lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1553_ = lean_nat_add(v_lo_1539_, v_hi_1540_);
v___x_1554_ = lean_unsigned_to_nat(1u);
v_mid_1555_ = lean_nat_shiftr(v___x_1553_, v___x_1554_);
lean_dec(v___x_1553_);
v___x_1568_ = lean_array_fget_borrowed(v_as_1538_, v_mid_1555_);
v___x_1569_ = lean_array_fget_borrowed(v_as_1538_, v_lo_1539_);
v___x_1570_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1568_, v___x_1569_);
if (v___x_1570_ == 0)
{
v___y_1563_ = v_as_1538_;
goto v___jp_1562_;
}
else
{
lean_object* v___x_1571_; 
v___x_1571_ = lean_array_fswap(v_as_1538_, v_lo_1539_, v_mid_1555_);
v___y_1563_ = v___x_1571_;
goto v___jp_1562_;
}
v___jp_1556_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v___x_1558_ = lean_array_fget_borrowed(v___y_1557_, v_mid_1555_);
v___x_1559_ = lean_array_fget_borrowed(v___y_1557_, v_hi_1540_);
v___x_1560_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1558_, v___x_1559_);
if (v___x_1560_ == 0)
{
lean_dec(v_mid_1555_);
v___y_1542_ = v___y_1557_;
goto v___jp_1541_;
}
else
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_array_fswap(v___y_1557_, v_mid_1555_, v_hi_1540_);
lean_dec(v_mid_1555_);
v___y_1542_ = v___x_1561_;
goto v___jp_1541_;
}
}
v___jp_1562_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1564_ = lean_array_fget_borrowed(v___y_1563_, v_hi_1540_);
v___x_1565_ = lean_array_fget_borrowed(v___y_1563_, v_lo_1539_);
v___x_1566_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1564_, v___x_1565_);
if (v___x_1566_ == 0)
{
v___y_1557_ = v___y_1563_;
goto v___jp_1556_;
}
else
{
lean_object* v___x_1567_; 
v___x_1567_ = lean_array_fswap(v___y_1563_, v_lo_1539_, v_hi_1540_);
v___y_1557_ = v___x_1567_;
goto v___jp_1556_;
}
}
}
v___jp_1541_:
{
lean_object* v_pivot_1543_; lean_object* v___x_1544_; lean_object* v_fst_1545_; lean_object* v_snd_1546_; uint8_t v___x_1547_; 
v_pivot_1543_ = lean_array_fget(v___y_1542_, v_hi_1540_);
lean_inc_n(v_lo_1539_, 2);
v___x_1544_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1540_, v_pivot_1543_, v___y_1542_, v_lo_1539_, v_lo_1539_);
lean_dec(v_pivot_1543_);
v_fst_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_fst_1545_);
v_snd_1546_ = lean_ctor_get(v___x_1544_, 1);
lean_inc(v_snd_1546_);
lean_dec_ref(v___x_1544_);
v___x_1547_ = lean_nat_dec_le(v_hi_1540_, v_fst_1545_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1537_, v_snd_1546_, v_lo_1539_, v_fst_1545_);
v___x_1549_ = lean_unsigned_to_nat(1u);
v___x_1550_ = lean_nat_add(v_fst_1545_, v___x_1549_);
lean_dec(v_fst_1545_);
v_as_1538_ = v___x_1548_;
v_lo_1539_ = v___x_1550_;
goto _start;
}
else
{
lean_dec(v_fst_1545_);
lean_dec(v_lo_1539_);
return v_snd_1546_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___boxed(lean_object* v_n_1572_, lean_object* v_as_1573_, lean_object* v_lo_1574_, lean_object* v_hi_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1572_, v_as_1573_, v_lo_1574_, v_hi_1575_);
lean_dec(v_hi_1575_);
lean_dec(v_n_1572_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(lean_object* v_coeff_1577_, lean_object* v_op_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v___y_1588_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1606_; lean_object* v_size_1613_; lean_object* v_buckets_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v_size_1613_ = lean_ctor_get(v_coeff_1577_, 0);
v_buckets_1614_ = lean_ctor_get(v_coeff_1577_, 1);
v___x_1615_ = lean_mk_empty_array_with_capacity(v_size_1613_);
v___x_1616_ = lean_unsigned_to_nat(0u);
v___x_1617_ = lean_array_get_size(v_buckets_1614_);
v___x_1618_ = lean_nat_dec_lt(v___x_1616_, v___x_1617_);
if (v___x_1618_ == 0)
{
v___y_1606_ = v___x_1615_;
goto v___jp_1605_;
}
else
{
size_t v___x_1619_; size_t v___x_1620_; lean_object* v___x_1621_; 
v___x_1619_ = ((size_t)0ULL);
v___x_1620_ = lean_usize_of_nat(v___x_1617_);
v___x_1621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_buckets_1614_, v___x_1619_, v___x_1620_, v___x_1615_);
v___y_1606_ = v___x_1621_;
goto v___jp_1605_;
}
v___jp_1587_:
{
lean_object* v_acc_1589_; size_t v_sz_1590_; size_t v___x_1591_; lean_object* v___x_1592_; 
v_acc_1589_ = lean_box(0);
v_sz_1590_ = lean_array_size(v___y_1588_);
v___x_1591_ = ((size_t)0ULL);
v___x_1592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1578_, v___y_1588_, v_sz_1590_, v___x_1591_, v_acc_1589_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
lean_dec_ref(v___y_1588_);
return v___x_1592_;
}
v___jp_1593_:
{
lean_object* v___x_1598_; 
v___x_1598_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v___y_1595_, v___y_1594_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec(v___y_1595_);
v___y_1588_ = v___x_1598_;
goto v___jp_1587_;
}
v___jp_1599_:
{
uint8_t v___x_1604_; 
v___x_1604_ = lean_nat_dec_le(v___y_1603_, v___y_1601_);
if (v___x_1604_ == 0)
{
lean_dec(v___y_1601_);
lean_inc(v___y_1603_);
v___y_1594_ = v___y_1600_;
v___y_1595_ = v___y_1602_;
v___y_1596_ = v___y_1603_;
v___y_1597_ = v___y_1603_;
goto v___jp_1593_;
}
else
{
v___y_1594_ = v___y_1600_;
v___y_1595_ = v___y_1602_;
v___y_1596_ = v___y_1603_;
v___y_1597_ = v___y_1601_;
goto v___jp_1593_;
}
}
v___jp_1605_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1607_ = lean_array_get_size(v___y_1606_);
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1609_ = lean_nat_dec_eq(v___x_1607_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1610_ = lean_unsigned_to_nat(1u);
v___x_1611_ = lean_nat_sub(v___x_1607_, v___x_1610_);
v___x_1612_ = lean_nat_dec_le(v___x_1608_, v___x_1611_);
if (v___x_1612_ == 0)
{
lean_inc(v___x_1611_);
v___y_1600_ = v___y_1606_;
v___y_1601_ = v___x_1611_;
v___y_1602_ = v___x_1607_;
v___y_1603_ = v___x_1611_;
goto v___jp_1599_;
}
else
{
v___y_1600_ = v___y_1606_;
v___y_1601_ = v___x_1611_;
v___y_1602_ = v___x_1607_;
v___y_1603_ = v___x_1608_;
goto v___jp_1599_;
}
}
else
{
v___y_1588_ = v___y_1606_;
goto v___jp_1587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr___boxed(lean_object* v_coeff_1622_, lean_object* v_op_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_coeff_1622_, v_op_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
lean_dec_ref(v_coeff_1622_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(lean_object* v_upperBound_1633_, lean_object* v___x_1634_, lean_object* v_op_1635_, lean_object* v_inst_1636_, lean_object* v_R_1637_, lean_object* v_a_1638_, lean_object* v_b_1639_, lean_object* v_c_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1633_, v___x_1634_, v_op_1635_, v_a_1638_, v_b_1639_, v___y_1641_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___boxed(lean_object* v_upperBound_1650_, lean_object* v___x_1651_, lean_object* v_op_1652_, lean_object* v_inst_1653_, lean_object* v_R_1654_, lean_object* v_a_1655_, lean_object* v_b_1656_, lean_object* v_c_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(v_upperBound_1650_, v___x_1651_, v_op_1652_, v_inst_1653_, v_R_1654_, v_a_1655_, v_b_1656_, v_c_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v_upperBound_1650_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(lean_object* v_n_1667_, lean_object* v_as_1668_, lean_object* v_lo_1669_, lean_object* v_hi_1670_, lean_object* v_w_1671_, lean_object* v_hlo_1672_, lean_object* v_hhi_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1667_, v_as_1668_, v_lo_1669_, v_hi_1670_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___boxed(lean_object* v_n_1675_, lean_object* v_as_1676_, lean_object* v_lo_1677_, lean_object* v_hi_1678_, lean_object* v_w_1679_, lean_object* v_hlo_1680_, lean_object* v_hhi_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(v_n_1675_, v_as_1676_, v_lo_1677_, v_hi_1678_, v_w_1679_, v_hlo_1680_, v_hhi_1681_);
lean_dec(v_hi_1678_);
lean_dec(v_n_1675_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(lean_object* v_n_1683_, lean_object* v_lo_1684_, lean_object* v_hi_1685_, lean_object* v_hhi_1686_, lean_object* v_pivot_1687_, lean_object* v_as_1688_, lean_object* v_i_1689_, lean_object* v_k_1690_, lean_object* v_ilo_1691_, lean_object* v_ik_1692_, lean_object* v_w_1693_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1685_, v_pivot_1687_, v_as_1688_, v_i_1689_, v_k_1690_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___boxed(lean_object* v_n_1695_, lean_object* v_lo_1696_, lean_object* v_hi_1697_, lean_object* v_hhi_1698_, lean_object* v_pivot_1699_, lean_object* v_as_1700_, lean_object* v_i_1701_, lean_object* v_k_1702_, lean_object* v_ilo_1703_, lean_object* v_ik_1704_, lean_object* v_w_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(v_n_1695_, v_lo_1696_, v_hi_1697_, v_hhi_1698_, v_pivot_1699_, v_as_1700_, v_i_1701_, v_k_1702_, v_ilo_1703_, v_ik_1704_, v_w_1705_);
lean_dec_ref(v_pivot_1699_);
lean_dec(v_hi_1697_);
lean_dec(v_lo_1696_);
lean_dec(v_n_1695_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(lean_object* v_e_1707_, lean_object* v___y_1708_){
_start:
{
uint8_t v___x_1710_; 
v___x_1710_ = l_Lean_Expr_hasMVar(v_e_1707_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; 
v___x_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1711_, 0, v_e_1707_);
return v___x_1711_;
}
else
{
lean_object* v___x_1712_; lean_object* v_mctx_1713_; lean_object* v___x_1714_; lean_object* v_fst_1715_; lean_object* v_snd_1716_; lean_object* v___x_1717_; lean_object* v_cache_1718_; lean_object* v_zetaDeltaFVarIds_1719_; lean_object* v_postponed_1720_; lean_object* v_diag_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1730_; 
v___x_1712_ = lean_st_ref_get(v___y_1708_);
v_mctx_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc_ref(v_mctx_1713_);
lean_dec(v___x_1712_);
v___x_1714_ = l_Lean_instantiateMVarsCore(v_mctx_1713_, v_e_1707_);
v_fst_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_fst_1715_);
v_snd_1716_ = lean_ctor_get(v___x_1714_, 1);
lean_inc(v_snd_1716_);
lean_dec_ref(v___x_1714_);
v___x_1717_ = lean_st_ref_take(v___y_1708_);
v_cache_1718_ = lean_ctor_get(v___x_1717_, 1);
v_zetaDeltaFVarIds_1719_ = lean_ctor_get(v___x_1717_, 2);
v_postponed_1720_ = lean_ctor_get(v___x_1717_, 3);
v_diag_1721_ = lean_ctor_get(v___x_1717_, 4);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1730_ == 0)
{
lean_object* v_unused_1731_; 
v_unused_1731_ = lean_ctor_get(v___x_1717_, 0);
lean_dec(v_unused_1731_);
v___x_1723_ = v___x_1717_;
v_isShared_1724_ = v_isSharedCheck_1730_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_diag_1721_);
lean_inc(v_postponed_1720_);
lean_inc(v_zetaDeltaFVarIds_1719_);
lean_inc(v_cache_1718_);
lean_dec(v___x_1717_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1730_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v_snd_1716_);
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_snd_1716_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_cache_1718_);
lean_ctor_set(v_reuseFailAlloc_1729_, 2, v_zetaDeltaFVarIds_1719_);
lean_ctor_set(v_reuseFailAlloc_1729_, 3, v_postponed_1720_);
lean_ctor_set(v_reuseFailAlloc_1729_, 4, v_diag_1721_);
v___x_1726_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = lean_st_ref_put(v___y_1708_, v___x_1726_);
v___x_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1728_, 0, v_fst_1715_);
return v___x_1728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg___boxed(lean_object* v_e_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1732_, v___y_1733_);
lean_dec(v___y_1733_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(lean_object* v_e_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1736_, v___y_1738_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___boxed(lean_object* v_e_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(v_e_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(lean_object* v_x_1750_, lean_object* v_y_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Lean_Meta_mkEq(v_x_1750_, v_y_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1780_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1780_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1780_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set_tag(v___x_1760_, 1);
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
uint8_t v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = 0;
v___x_1765_ = lean_box(0);
v___x_1766_ = l_Lean_Meta_mkFreshExprMVar(v___x_1763_, v___x_1764_, v___x_1765_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1768_ = l_Lean_Expr_mvarId_x21(v_a_1767_);
v___x_1769_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v___x_1768_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v___x_1770_; 
lean_dec_ref_known(v___x_1769_, 1);
v___x_1770_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_a_1767_, v_a_1753_);
return v___x_1770_;
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec(v_a_1767_);
v_a_1771_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1769_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1769_);
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
return v___x_1766_;
}
}
}
}
else
{
return v___x_1757_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC___boxed(lean_object* v_x_1781_, lean_object* v_y_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v_x_1781_, v_y_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
return v_res_1788_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = lean_unsigned_to_nat(32u);
v___x_1790_ = lean_mk_empty_array_with_capacity(v___x_1789_);
v___x_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
return v___x_1791_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1792_ = ((size_t)5ULL);
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = lean_unsigned_to_nat(32u);
v___x_1795_ = lean_mk_empty_array_with_capacity(v___x_1794_);
v___x_1796_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0);
v___x_1797_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
lean_ctor_set(v___x_1797_, 1, v___x_1795_);
lean_ctor_set(v___x_1797_, 2, v___x_1793_);
lean_ctor_set(v___x_1797_, 3, v___x_1793_);
lean_ctor_set_usize(v___x_1797_, 4, v___x_1792_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(lean_object* v___y_1798_){
_start:
{
lean_object* v___x_1800_; lean_object* v_traceState_1801_; lean_object* v_traces_1802_; lean_object* v___x_1803_; lean_object* v_traceState_1804_; lean_object* v_env_1805_; lean_object* v_nextMacroScope_1806_; lean_object* v_ngen_1807_; lean_object* v_auxDeclNGen_1808_; lean_object* v_cache_1809_; lean_object* v_messages_1810_; lean_object* v_infoState_1811_; lean_object* v_snapshotTasks_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1831_; 
v___x_1800_ = lean_st_ref_get(v___y_1798_);
v_traceState_1801_ = lean_ctor_get(v___x_1800_, 4);
lean_inc_ref(v_traceState_1801_);
lean_dec(v___x_1800_);
v_traces_1802_ = lean_ctor_get(v_traceState_1801_, 0);
lean_inc_ref(v_traces_1802_);
lean_dec_ref(v_traceState_1801_);
v___x_1803_ = lean_st_ref_take(v___y_1798_);
v_traceState_1804_ = lean_ctor_get(v___x_1803_, 4);
v_env_1805_ = lean_ctor_get(v___x_1803_, 0);
v_nextMacroScope_1806_ = lean_ctor_get(v___x_1803_, 1);
v_ngen_1807_ = lean_ctor_get(v___x_1803_, 2);
v_auxDeclNGen_1808_ = lean_ctor_get(v___x_1803_, 3);
v_cache_1809_ = lean_ctor_get(v___x_1803_, 5);
v_messages_1810_ = lean_ctor_get(v___x_1803_, 6);
v_infoState_1811_ = lean_ctor_get(v___x_1803_, 7);
v_snapshotTasks_1812_ = lean_ctor_get(v___x_1803_, 8);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1814_ = v___x_1803_;
v_isShared_1815_ = v_isSharedCheck_1831_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_snapshotTasks_1812_);
lean_inc(v_infoState_1811_);
lean_inc(v_messages_1810_);
lean_inc(v_cache_1809_);
lean_inc(v_traceState_1804_);
lean_inc(v_auxDeclNGen_1808_);
lean_inc(v_ngen_1807_);
lean_inc(v_nextMacroScope_1806_);
lean_inc(v_env_1805_);
lean_dec(v___x_1803_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1831_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
uint64_t v_tid_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1829_; 
v_tid_1816_ = lean_ctor_get_uint64(v_traceState_1804_, sizeof(void*)*1);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_traceState_1804_);
if (v_isSharedCheck_1829_ == 0)
{
lean_object* v_unused_1830_; 
v_unused_1830_ = lean_ctor_get(v_traceState_1804_, 0);
lean_dec(v_unused_1830_);
v___x_1818_ = v_traceState_1804_;
v_isShared_1819_ = v_isSharedCheck_1829_;
goto v_resetjp_1817_;
}
else
{
lean_dec(v_traceState_1804_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1829_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1820_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1820_);
v___x_1822_ = v___x_1818_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1820_);
lean_ctor_set_uint64(v_reuseFailAlloc_1828_, sizeof(void*)*1, v_tid_1816_);
v___x_1822_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1824_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 4, v___x_1822_);
v___x_1824_ = v___x_1814_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_env_1805_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_nextMacroScope_1806_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_ngen_1807_);
lean_ctor_set(v_reuseFailAlloc_1827_, 3, v_auxDeclNGen_1808_);
lean_ctor_set(v_reuseFailAlloc_1827_, 4, v___x_1822_);
lean_ctor_set(v_reuseFailAlloc_1827_, 5, v_cache_1809_);
lean_ctor_set(v_reuseFailAlloc_1827_, 6, v_messages_1810_);
lean_ctor_set(v_reuseFailAlloc_1827_, 7, v_infoState_1811_);
lean_ctor_set(v_reuseFailAlloc_1827_, 8, v_snapshotTasks_1812_);
v___x_1824_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = lean_st_ref_put(v___y_1798_, v___x_1824_);
v___x_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1826_, 0, v_traces_1802_);
return v___x_1826_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___boxed(lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1832_);
lean_dec(v___y_1832_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1843_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
return v_res_1856_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(lean_object* v_opts_1857_, lean_object* v_opt_1858_){
_start:
{
lean_object* v_name_1859_; lean_object* v_defValue_1860_; lean_object* v_map_1861_; lean_object* v___x_1862_; 
v_name_1859_ = lean_ctor_get(v_opt_1858_, 0);
v_defValue_1860_ = lean_ctor_get(v_opt_1858_, 1);
v_map_1861_ = lean_ctor_get(v_opts_1857_, 0);
v___x_1862_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1861_, v_name_1859_);
if (lean_obj_tag(v___x_1862_) == 0)
{
uint8_t v___x_1863_; 
v___x_1863_ = lean_unbox(v_defValue_1860_);
return v___x_1863_;
}
else
{
lean_object* v_val_1864_; 
v_val_1864_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_val_1864_);
lean_dec_ref_known(v___x_1862_, 1);
if (lean_obj_tag(v_val_1864_) == 1)
{
uint8_t v_v_1865_; 
v_v_1865_ = lean_ctor_get_uint8(v_val_1864_, 0);
lean_dec_ref_known(v_val_1864_, 0);
return v_v_1865_;
}
else
{
uint8_t v___x_1866_; 
lean_dec(v_val_1864_);
v___x_1866_ = lean_unbox(v_defValue_1860_);
return v___x_1866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object* v_opts_1867_, lean_object* v_opt_1868_){
_start:
{
uint8_t v_res_1869_; lean_object* v_r_1870_; 
v_res_1869_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_1867_, v_opt_1868_);
lean_dec_ref(v_opt_1868_);
lean_dec_ref(v_opts_1867_);
v_r_1870_ = lean_box(v_res_1869_);
return v_r_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(lean_object* v_cls_1871_, lean_object* v_____do__lift_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_toCold_1883_; lean_object* v_options_1884_; uint8_t v_hasTrace_1885_; 
v_toCold_1883_ = lean_ctor_get(v___y_1880_, 0);
v_options_1884_ = lean_ctor_get(v_toCold_1883_, 2);
v_hasTrace_1885_ = lean_ctor_get_uint8(v_options_1884_, sizeof(void*)*1);
if (v_hasTrace_1885_ == 0)
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
lean_dec(v_cls_1871_);
v___x_1886_ = lean_box(v_hasTrace_1885_);
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
return v___x_1887_;
}
else
{
lean_object* v___x_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1888_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_1889_ = l_Lean_Name_append(v___x_1888_, v_cls_1871_);
v___x_1890_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_1872_, v_options_1884_, v___x_1889_);
lean_dec(v___x_1889_);
v___x_1891_ = lean_box(v___x_1890_);
v___x_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
return v___x_1892_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0___boxed(lean_object* v_cls_1893_, lean_object* v_____do__lift_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_1893_, v_____do__lift_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v_____do__lift_1894_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1(lean_object* v___x_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Lean_mkAppB(v___x_1906_, v___y_1907_, v___y_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(lean_object* v_val_1910_, lean_object* v_lhs_1911_, lean_object* v_rhs_1912_, lean_object* v_P_1913_, uint8_t v___x_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___x_1923_; 
lean_inc_ref(v_lhs_1911_);
lean_inc_ref(v_val_1910_);
v___x_1923_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1910_, v_lhs_1911_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v_fst_1925_; lean_object* v_snd_1926_; lean_object* v___x_1927_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v_fst_1925_ = lean_ctor_get(v_a_1924_, 0);
lean_inc(v_fst_1925_);
v_snd_1926_ = lean_ctor_get(v_a_1924_, 1);
lean_inc(v_snd_1926_);
lean_dec(v_a_1924_);
lean_inc_ref(v_rhs_1912_);
lean_inc_ref(v_val_1910_);
v___x_1927_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1910_, v_rhs_1912_, v_snd_1926_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v_fst_1929_; lean_object* v_snd_1930_; lean_object* v___x_1931_; lean_object* v_a_1932_; lean_object* v_fst_1933_; lean_object* v_snd_1934_; lean_object* v_common_1935_; lean_object* v_x_1936_; lean_object* v_y_1937_; lean_object* v___x_1938_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
v_fst_1929_ = lean_ctor_get(v_a_1928_, 0);
lean_inc(v_fst_1929_);
v_snd_1930_ = lean_ctor_get(v_a_1928_, 1);
lean_inc(v_snd_1930_);
lean_dec(v_a_1928_);
v___x_1931_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_1925_, v_fst_1929_, v_snd_1930_);
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref(v___x_1931_);
v_fst_1933_ = lean_ctor_get(v_a_1932_, 0);
lean_inc(v_fst_1933_);
v_snd_1934_ = lean_ctor_get(v_a_1932_, 1);
lean_inc(v_snd_1934_);
lean_dec(v_a_1932_);
v_common_1935_ = lean_ctor_get(v_fst_1933_, 0);
lean_inc_ref(v_common_1935_);
v_x_1936_ = lean_ctor_get(v_fst_1933_, 1);
lean_inc_ref(v_x_1936_);
v_y_1937_ = lean_ctor_get(v_fst_1933_, 2);
lean_inc_ref(v_y_1937_);
lean_dec(v_fst_1933_);
lean_inc_ref(v_val_1910_);
v___x_1938_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_1935_, v_val_1910_, v_snd_1934_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec_ref(v_common_1935_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v_fst_1940_; lean_object* v_snd_1941_; lean_object* v___x_1942_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1938_, 1);
v_fst_1940_ = lean_ctor_get(v_a_1939_, 0);
lean_inc(v_fst_1940_);
v_snd_1941_ = lean_ctor_get(v_a_1939_, 1);
lean_inc(v_snd_1941_);
lean_dec(v_a_1939_);
lean_inc_ref(v_val_1910_);
v___x_1942_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_1936_, v_val_1910_, v_snd_1941_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec_ref(v_x_1936_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v_fst_1944_; lean_object* v_snd_1945_; lean_object* v___x_1946_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v_fst_1944_ = lean_ctor_get(v_a_1943_, 0);
lean_inc(v_fst_1944_);
v_snd_1945_ = lean_ctor_get(v_a_1943_, 1);
lean_inc(v_snd_1945_);
lean_dec(v_a_1943_);
lean_inc_ref(v_val_1910_);
v___x_1946_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_1937_, v_val_1910_, v_snd_1945_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec_ref(v_y_1937_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_2011_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_2011_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_2011_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v_fst_1951_; lean_object* v_snd_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_2010_; 
v_fst_1951_ = lean_ctor_get(v_a_1947_, 0);
v_snd_1952_ = lean_ctor_get(v_a_1947_, 1);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_a_1947_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1954_ = v_a_1947_;
v_isShared_1955_ = v_isSharedCheck_2010_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_snd_1952_);
lean_inc(v_fst_1951_);
lean_dec(v_a_1947_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_2010_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___x_2000_; lean_object* v___f_2001_; lean_object* v___y_2003_; lean_object* v___x_2007_; 
lean_inc_ref(v_val_1910_);
v___x_2000_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_1910_);
v___f_2001_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_2001_, 0, v___x_2000_);
lean_inc(v_fst_1940_);
lean_inc_ref(v___f_2001_);
v___x_2007_ = l_Option_merge___redArg(v___f_2001_, v_fst_1940_, v_fst_1944_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v___x_2008_; 
lean_inc_ref(v_val_1910_);
v___x_2008_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1910_);
v___y_2003_ = v___x_2008_;
goto v___jp_2002_;
}
else
{
lean_object* v_val_2009_; 
v_val_2009_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_val_2009_);
lean_dec_ref_known(v___x_2007_, 1);
v___y_2003_ = v_val_2009_;
goto v___jp_2002_;
}
v___jp_1956_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
lean_inc_ref(v_P_1913_);
v___x_1959_ = l_Lean_mkAppB(v_P_1913_, v_lhs_1911_, v_rhs_1912_);
v___x_1960_ = l_Lean_mkAppB(v_P_1913_, v___y_1957_, v___y_1958_);
v___x_1961_ = lean_expr_eqv(v___x_1959_, v___x_1960_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; 
lean_del_object(v___x_1949_);
lean_inc_ref(v___x_1960_);
v___x_1962_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_1959_, v___x_1960_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1964_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1962_, 1);
v___x_1964_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1960_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1976_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1967_ = v___x_1964_;
v_isShared_1968_ = v_isSharedCheck_1976_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1976_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1969_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1969_, 0, v_a_1965_);
lean_ctor_set(v___x_1969_, 1, v_a_1963_);
lean_ctor_set_uint8(v___x_1969_, sizeof(void*)*2, v___x_1961_);
lean_ctor_set_uint8(v___x_1969_, sizeof(void*)*2 + 1, v___x_1961_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_1969_);
v___x_1971_ = v___x_1954_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v_snd_1952_);
v___x_1971_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1973_; 
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 0, v___x_1971_);
v___x_1973_ = v___x_1967_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1971_);
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
else
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
lean_dec(v_a_1963_);
lean_del_object(v___x_1954_);
lean_dec(v_snd_1952_);
v_a_1977_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1964_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1964_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec_ref(v___x_1960_);
lean_del_object(v___x_1954_);
lean_dec(v_snd_1952_);
v_a_1985_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1962_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1962_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
lean_object* v___x_1993_; lean_object* v___x_1995_; 
lean_dec_ref(v___x_1960_);
lean_dec_ref(v___x_1959_);
v___x_1993_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1993_, 0, v___x_1914_);
lean_ctor_set_uint8(v___x_1993_, 1, v___x_1914_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_1993_);
v___x_1995_ = v___x_1954_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_snd_1952_);
v___x_1995_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1997_; 
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_1995_);
v___x_1997_ = v___x_1949_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
v___jp_2002_:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Option_merge___redArg(v___f_2001_, v_fst_1940_, v_fst_1951_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1910_);
v___y_1957_ = v___y_2003_;
v___y_1958_ = v___x_2005_;
goto v___jp_1956_;
}
else
{
lean_object* v_val_2006_; 
lean_dec_ref(v_val_1910_);
v_val_2006_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_val_2006_);
lean_dec_ref_known(v___x_2004_, 1);
v___y_1957_ = v___y_2003_;
v___y_1958_ = v_val_2006_;
goto v___jp_1956_;
}
}
}
}
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec(v_fst_1944_);
lean_dec(v_fst_1940_);
lean_dec_ref(v_P_1913_);
lean_dec_ref(v_rhs_1912_);
lean_dec_ref(v_lhs_1911_);
lean_dec_ref(v_val_1910_);
v_a_2012_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_1946_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_1946_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v_fst_1940_);
lean_dec_ref(v_y_1937_);
lean_dec_ref(v_P_1913_);
lean_dec_ref(v_rhs_1912_);
lean_dec_ref(v_lhs_1911_);
lean_dec_ref(v_val_1910_);
v_a_2020_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_1942_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_1942_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec_ref(v_y_1937_);
lean_dec_ref(v_x_1936_);
lean_dec_ref(v_P_1913_);
lean_dec_ref(v_rhs_1912_);
lean_dec_ref(v_lhs_1911_);
lean_dec_ref(v_val_1910_);
v_a_2028_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_1938_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_1938_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_dec(v_fst_1925_);
lean_dec_ref(v_P_1913_);
lean_dec_ref(v_rhs_1912_);
lean_dec_ref(v_lhs_1911_);
lean_dec_ref(v_val_1910_);
v_a_2036_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_1927_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_1927_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec_ref(v_P_1913_);
lean_dec_ref(v_rhs_1912_);
lean_dec_ref(v_lhs_1911_);
lean_dec_ref(v_val_1910_);
v_a_2044_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_1923_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_1923_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object* v_val_2052_, lean_object* v_lhs_2053_, lean_object* v_rhs_2054_, lean_object* v_P_2055_, lean_object* v___x_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
uint8_t v___x_187283__boxed_2065_; lean_object* v_res_2066_; 
v___x_187283__boxed_2065_ = lean_unbox(v___x_2056_);
v_res_2066_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(v_val_2052_, v_lhs_2053_, v_rhs_2054_, v_P_2055_, v___x_187283__boxed_2065_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
return v_res_2066_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_2069_ = l_Lean_stringToMessageData(v___x_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(lean_object* v_x_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1);
v___x_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object* v_x_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(v_x_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v_x_2083_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object* v_cls_2095_, lean_object* v_msg_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v_ref_2102_; lean_object* v___x_2103_; lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2148_; 
v_ref_2102_ = lean_ctor_get(v___y_2099_, 2);
v___x_2103_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2106_ = v___x_2103_;
v_isShared_2107_ = v_isSharedCheck_2148_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2103_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2148_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2108_; lean_object* v_traceState_2109_; lean_object* v_env_2110_; lean_object* v_nextMacroScope_2111_; lean_object* v_ngen_2112_; lean_object* v_auxDeclNGen_2113_; lean_object* v_cache_2114_; lean_object* v_messages_2115_; lean_object* v_infoState_2116_; lean_object* v_snapshotTasks_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2147_; 
v___x_2108_ = lean_st_ref_take(v___y_2100_);
v_traceState_2109_ = lean_ctor_get(v___x_2108_, 4);
v_env_2110_ = lean_ctor_get(v___x_2108_, 0);
v_nextMacroScope_2111_ = lean_ctor_get(v___x_2108_, 1);
v_ngen_2112_ = lean_ctor_get(v___x_2108_, 2);
v_auxDeclNGen_2113_ = lean_ctor_get(v___x_2108_, 3);
v_cache_2114_ = lean_ctor_get(v___x_2108_, 5);
v_messages_2115_ = lean_ctor_get(v___x_2108_, 6);
v_infoState_2116_ = lean_ctor_get(v___x_2108_, 7);
v_snapshotTasks_2117_ = lean_ctor_get(v___x_2108_, 8);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2119_ = v___x_2108_;
v_isShared_2120_ = v_isSharedCheck_2147_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_snapshotTasks_2117_);
lean_inc(v_infoState_2116_);
lean_inc(v_messages_2115_);
lean_inc(v_cache_2114_);
lean_inc(v_traceState_2109_);
lean_inc(v_auxDeclNGen_2113_);
lean_inc(v_ngen_2112_);
lean_inc(v_nextMacroScope_2111_);
lean_inc(v_env_2110_);
lean_dec(v___x_2108_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2147_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
uint64_t v_tid_2121_; lean_object* v_traces_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2146_; 
v_tid_2121_ = lean_ctor_get_uint64(v_traceState_2109_, sizeof(void*)*1);
v_traces_2122_ = lean_ctor_get(v_traceState_2109_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_traceState_2109_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2124_ = v_traceState_2109_;
v_isShared_2125_ = v_isSharedCheck_2146_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_traces_2122_);
lean_dec(v_traceState_2109_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2146_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; double v___x_2127_; uint8_t v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2136_; 
v___x_2126_ = lean_box(0);
v___x_2127_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_2128_ = 0;
v___x_2129_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_2130_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2130_, 0, v_cls_2095_);
lean_ctor_set(v___x_2130_, 1, v___x_2126_);
lean_ctor_set(v___x_2130_, 2, v___x_2129_);
lean_ctor_set_float(v___x_2130_, sizeof(void*)*3, v___x_2127_);
lean_ctor_set_float(v___x_2130_, sizeof(void*)*3 + 8, v___x_2127_);
lean_ctor_set_uint8(v___x_2130_, sizeof(void*)*3 + 16, v___x_2128_);
v___x_2131_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_2132_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2130_);
lean_ctor_set(v___x_2132_, 1, v_a_2104_);
lean_ctor_set(v___x_2132_, 2, v___x_2131_);
lean_inc(v_ref_2102_);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v_ref_2102_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = l_Lean_PersistentArray_push___redArg(v_traces_2122_, v___x_2133_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2134_);
v___x_2136_ = v___x_2124_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2134_);
lean_ctor_set_uint64(v_reuseFailAlloc_2145_, sizeof(void*)*1, v_tid_2121_);
v___x_2136_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
lean_object* v___x_2138_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 4, v___x_2136_);
v___x_2138_ = v___x_2119_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_env_2110_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_nextMacroScope_2111_);
lean_ctor_set(v_reuseFailAlloc_2144_, 2, v_ngen_2112_);
lean_ctor_set(v_reuseFailAlloc_2144_, 3, v_auxDeclNGen_2113_);
lean_ctor_set(v_reuseFailAlloc_2144_, 4, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2144_, 5, v_cache_2114_);
lean_ctor_set(v_reuseFailAlloc_2144_, 6, v_messages_2115_);
lean_ctor_set(v_reuseFailAlloc_2144_, 7, v_infoState_2116_);
lean_ctor_set(v_reuseFailAlloc_2144_, 8, v_snapshotTasks_2117_);
v___x_2138_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2139_ = lean_st_ref_put(v___y_2100_, v___x_2138_);
v___x_2140_ = lean_box(0);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 0, v___x_2140_);
v___x_2142_ = v___x_2106_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object* v_cls_2149_, lean_object* v_msg_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2149_, v_msg_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
return v_res_2156_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2159_ = l_Lean_stringToMessageData(v___x_2158_);
return v___x_2159_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2));
v___x_2162_ = l_Lean_stringToMessageData(v___x_2161_);
return v___x_2162_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4));
v___x_2165_ = l_Lean_stringToMessageData(v___x_2164_);
return v___x_2165_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = lean_box(0);
v___x_2167_ = lean_unsigned_to_nat(16u);
v___x_2168_ = lean_mk_array(v___x_2167_, v___x_2166_);
return v___x_2168_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7(void){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2169_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6);
v___x_2170_ = lean_unsigned_to_nat(0u);
v___x_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
lean_ctor_set(v___x_2171_, 1, v___x_2169_);
return v___x_2171_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9));
v___x_2176_ = l_Lean_stringToMessageData(v___x_2175_);
return v___x_2176_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12(void){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11));
v___x_2179_ = l_Lean_stringToMessageData(v___x_2178_);
return v___x_2179_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13));
v___x_2182_ = l_Lean_stringToMessageData(v___x_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(lean_object* v_lhs_2183_, lean_object* v_rhs_2184_, uint8_t v___x_2185_, lean_object* v___f_2186_, lean_object* v_cls_2187_, lean_object* v_P_2188_, lean_object* v_____r_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v___x_2209_; 
lean_inc_ref(v_lhs_2183_);
v___x_2209_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2183_);
if (lean_obj_tag(v___x_2209_) == 1)
{
lean_object* v_val_2210_; lean_object* v___x_2211_; 
v_val_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_val_2210_);
lean_dec_ref_known(v___x_2209_, 1);
lean_inc_ref(v_rhs_2184_);
v___x_2211_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2184_);
if (lean_obj_tag(v___x_2211_) == 1)
{
lean_object* v_val_2212_; uint8_t v___x_2252_; 
v_val_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_val_2212_);
lean_dec_ref_known(v___x_2211_, 1);
v___x_2252_ = lean_expr_eqv(v_val_2210_, v_val_2212_);
if (v___x_2252_ == 0)
{
lean_dec_ref(v_P_2188_);
goto v___jp_2213_;
}
else
{
if (v___x_2185_ == 0)
{
lean_object* v_toCold_2253_; lean_object* v_options_2254_; lean_object* v_inheritedTraceOptions_2255_; uint8_t v_hasTrace_2256_; lean_object* v___x_2257_; lean_object* v___f_2258_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; 
lean_dec(v_val_2212_);
lean_dec_ref(v___f_2186_);
v_toCold_2253_ = lean_ctor_get(v___y_2197_, 0);
v_options_2254_ = lean_ctor_get(v_toCold_2253_, 2);
v_inheritedTraceOptions_2255_ = lean_ctor_get(v_toCold_2253_, 11);
v_hasTrace_2256_ = lean_ctor_get_uint8(v_options_2254_, sizeof(void*)*1);
v___x_2257_ = lean_box(v___x_2185_);
lean_inc(v_val_2210_);
v___f_2258_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 13, 5);
lean_closure_set(v___f_2258_, 0, v_val_2210_);
lean_closure_set(v___f_2258_, 1, v_lhs_2183_);
lean_closure_set(v___f_2258_, 2, v_rhs_2184_);
lean_closure_set(v___f_2258_, 3, v_P_2188_);
lean_closure_set(v___f_2258_, 4, v___x_2257_);
if (v_hasTrace_2256_ == 0)
{
lean_dec(v_cls_2187_);
v___y_2260_ = v___y_2193_;
v___y_2261_ = v___y_2194_;
v___y_2262_ = v___y_2195_;
v___y_2263_ = v___y_2196_;
v___y_2264_ = v___y_2197_;
v___y_2265_ = v___y_2198_;
goto v___jp_2259_;
}
else
{
lean_object* v___x_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2270_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2187_);
v___x_2271_ = l_Lean_Name_append(v___x_2270_, v_cls_2187_);
v___x_2272_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2255_, v_options_2254_, v___x_2271_);
lean_dec(v___x_2271_);
if (v___x_2272_ == 0)
{
lean_dec(v_cls_2187_);
v___y_2260_ = v___y_2193_;
v___y_2261_ = v___y_2194_;
v___y_2262_ = v___y_2195_;
v___y_2263_ = v___y_2196_;
v___y_2264_ = v___y_2197_;
v___y_2265_ = v___y_2198_;
goto v___jp_2259_;
}
else
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2273_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10);
lean_inc(v_val_2210_);
v___x_2274_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2210_);
v___x_2275_ = l_Lean_MessageData_ofExpr(v___x_2274_);
v___x_2276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2273_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12);
v___x_2278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2276_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2187_, v___x_2278_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_dec_ref_known(v___x_2279_, 1);
v___y_2260_ = v___y_2193_;
v___y_2261_ = v___y_2194_;
v___y_2262_ = v___y_2195_;
v___y_2263_ = v___y_2196_;
v___y_2264_ = v___y_2197_;
v___y_2265_ = v___y_2198_;
goto v___jp_2259_;
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec_ref(v___f_2258_);
lean_dec(v_val_2210_);
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2279_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
}
v___jp_2259_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2266_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7);
v___x_2267_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8));
v___x_2268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2268_, 0, v_val_2210_);
lean_ctor_set(v___x_2268_, 1, v___x_2266_);
lean_ctor_set(v___x_2268_, 2, v___x_2267_);
v___x_2269_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___f_2258_, v___x_2268_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
return v___x_2269_;
}
}
else
{
lean_dec_ref(v_P_2188_);
goto v___jp_2213_;
}
}
v___jp_2213_:
{
lean_object* v_toCold_2214_; lean_object* v_inheritedTraceOptions_2215_; lean_object* v___x_2216_; 
v_toCold_2214_ = lean_ctor_get(v___y_2197_, 0);
v_inheritedTraceOptions_2215_ = lean_ctor_get(v_toCold_2214_, 11);
lean_inc(v___y_2198_);
lean_inc_ref(v___y_2197_);
lean_inc(v___y_2196_);
lean_inc_ref(v___y_2195_);
lean_inc(v___y_2194_);
lean_inc_ref(v___y_2193_);
lean_inc(v___y_2192_);
lean_inc_ref(v___y_2191_);
lean_inc(v___y_2190_);
lean_inc_ref(v_inheritedTraceOptions_2215_);
v___x_2216_ = lean_apply_11(v___f_2186_, v_inheritedTraceOptions_2215_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, lean_box(0));
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; uint8_t v___x_2218_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2217_);
lean_dec_ref_known(v___x_2216_, 1);
v___x_2218_ = lean_unbox(v_a_2217_);
lean_dec(v_a_2217_);
if (v___x_2218_ == 0)
{
lean_dec(v_val_2212_);
lean_dec(v_val_2210_);
lean_dec(v_cls_2187_);
lean_dec_ref(v_rhs_2184_);
lean_dec_ref(v_lhs_2183_);
goto v___jp_2200_;
}
else
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2219_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1);
v___x_2220_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2210_);
v___x_2221_ = l_Lean_MessageData_ofExpr(v___x_2220_);
v___x_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2219_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3);
v___x_2224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2222_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
v___x_2225_ = l_Lean_indentExpr(v_lhs_2183_);
v___x_2226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2224_);
lean_ctor_set(v___x_2226_, 1, v___x_2225_);
v___x_2227_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5);
v___x_2228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2226_);
lean_ctor_set(v___x_2228_, 1, v___x_2227_);
v___x_2229_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2212_);
v___x_2230_ = l_Lean_MessageData_ofExpr(v___x_2229_);
v___x_2231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2228_);
lean_ctor_set(v___x_2231_, 1, v___x_2230_);
v___x_2232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v___x_2223_);
v___x_2233_ = l_Lean_indentExpr(v_rhs_2184_);
v___x_2234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2232_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
v___x_2235_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2187_, v___x_2234_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_dec_ref_known(v___x_2235_, 1);
goto v___jp_2200_;
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2235_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_dec(v_val_2212_);
lean_dec(v_val_2210_);
lean_dec(v_cls_2187_);
lean_dec_ref(v_rhs_2184_);
lean_dec_ref(v_lhs_2183_);
v_a_2244_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2216_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2216_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
else
{
lean_object* v_toCold_2288_; lean_object* v_inheritedTraceOptions_2289_; lean_object* v___x_2290_; 
lean_dec(v___x_2211_);
lean_dec(v_val_2210_);
lean_dec_ref(v_P_2188_);
lean_dec_ref(v_lhs_2183_);
v_toCold_2288_ = lean_ctor_get(v___y_2197_, 0);
v_inheritedTraceOptions_2289_ = lean_ctor_get(v_toCold_2288_, 11);
lean_inc(v___y_2198_);
lean_inc_ref(v___y_2197_);
lean_inc(v___y_2196_);
lean_inc_ref(v___y_2195_);
lean_inc(v___y_2194_);
lean_inc_ref(v___y_2193_);
lean_inc(v___y_2192_);
lean_inc_ref(v___y_2191_);
lean_inc(v___y_2190_);
lean_inc_ref(v_inheritedTraceOptions_2289_);
v___x_2290_ = lean_apply_11(v___f_2186_, v_inheritedTraceOptions_2289_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, lean_box(0));
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; uint8_t v___x_2292_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2291_);
lean_dec_ref_known(v___x_2290_, 1);
v___x_2292_ = lean_unbox(v_a_2291_);
lean_dec(v_a_2291_);
if (v___x_2292_ == 0)
{
lean_dec(v_cls_2187_);
lean_dec_ref(v_rhs_2184_);
goto v___jp_2203_;
}
else
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2293_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_2294_ = l_Lean_indentExpr(v_rhs_2184_);
v___x_2295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2293_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
v___x_2296_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2187_, v___x_2295_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_dec_ref_known(v___x_2296_, 1);
goto v___jp_2203_;
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2296_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2296_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec(v_cls_2187_);
lean_dec_ref(v_rhs_2184_);
v_a_2305_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2290_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2290_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
else
{
lean_object* v_toCold_2313_; lean_object* v_inheritedTraceOptions_2314_; lean_object* v___x_2315_; 
lean_dec(v___x_2209_);
lean_dec_ref(v_P_2188_);
lean_dec_ref(v_rhs_2184_);
v_toCold_2313_ = lean_ctor_get(v___y_2197_, 0);
v_inheritedTraceOptions_2314_ = lean_ctor_get(v_toCold_2313_, 11);
lean_inc(v___y_2198_);
lean_inc_ref(v___y_2197_);
lean_inc(v___y_2196_);
lean_inc_ref(v___y_2195_);
lean_inc(v___y_2194_);
lean_inc_ref(v___y_2193_);
lean_inc(v___y_2192_);
lean_inc_ref(v___y_2191_);
lean_inc(v___y_2190_);
lean_inc_ref(v_inheritedTraceOptions_2314_);
v___x_2315_ = lean_apply_11(v___f_2186_, v_inheritedTraceOptions_2314_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, lean_box(0));
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; uint8_t v___x_2317_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v___x_2317_ = lean_unbox(v_a_2316_);
lean_dec(v_a_2316_);
if (v___x_2317_ == 0)
{
lean_dec(v_cls_2187_);
lean_dec_ref(v_lhs_2183_);
goto v___jp_2206_;
}
else
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2318_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_2319_ = l_Lean_indentExpr(v_lhs_2183_);
v___x_2320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2318_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2187_, v___x_2320_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_dec_ref_known(v___x_2321_, 1);
goto v___jp_2206_;
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2321_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2321_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
lean_dec(v_cls_2187_);
lean_dec_ref(v_lhs_2183_);
v_a_2330_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2332_ = v___x_2315_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2315_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2330_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
v___jp_2200_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2201_, 0, v___x_2185_);
lean_ctor_set_uint8(v___x_2201_, 1, v___x_2185_);
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
return v___x_2202_;
}
v___jp_2203_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2204_, 0, v___x_2185_);
lean_ctor_set_uint8(v___x_2204_, 1, v___x_2185_);
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
return v___x_2205_;
}
v___jp_2206_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2207_, 0, v___x_2185_);
lean_ctor_set_uint8(v___x_2207_, 1, v___x_2185_);
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
return v___x_2208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___boxed(lean_object** _args){
lean_object* v_lhs_2338_ = _args[0];
lean_object* v_rhs_2339_ = _args[1];
lean_object* v___x_2340_ = _args[2];
lean_object* v___f_2341_ = _args[3];
lean_object* v_cls_2342_ = _args[4];
lean_object* v_P_2343_ = _args[5];
lean_object* v_____r_2344_ = _args[6];
lean_object* v___y_2345_ = _args[7];
lean_object* v___y_2346_ = _args[8];
lean_object* v___y_2347_ = _args[9];
lean_object* v___y_2348_ = _args[10];
lean_object* v___y_2349_ = _args[11];
lean_object* v___y_2350_ = _args[12];
lean_object* v___y_2351_ = _args[13];
lean_object* v___y_2352_ = _args[14];
lean_object* v___y_2353_ = _args[15];
lean_object* v___y_2354_ = _args[16];
_start:
{
uint8_t v___x_187767__boxed_2355_; lean_object* v_res_2356_; 
v___x_187767__boxed_2355_ = lean_unbox(v___x_2340_);
v_res_2356_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2338_, v_rhs_2339_, v___x_187767__boxed_2355_, v___f_2341_, v_cls_2342_, v_P_2343_, v_____r_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(lean_object* v_val_2357_, lean_object* v_lhs_2358_, lean_object* v_rhs_2359_, lean_object* v_P_2360_, uint8_t v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v___x_2370_; 
lean_inc_ref(v_lhs_2358_);
lean_inc_ref(v_val_2357_);
v___x_2370_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_2357_, v_lhs_2358_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v_fst_2372_; lean_object* v_snd_2373_; lean_object* v___x_2374_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_a_2371_);
lean_dec_ref_known(v___x_2370_, 1);
v_fst_2372_ = lean_ctor_get(v_a_2371_, 0);
lean_inc(v_fst_2372_);
v_snd_2373_ = lean_ctor_get(v_a_2371_, 1);
lean_inc(v_snd_2373_);
lean_dec(v_a_2371_);
lean_inc_ref(v_rhs_2359_);
lean_inc_ref(v_val_2357_);
v___x_2374_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_2357_, v_rhs_2359_, v_snd_2373_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v_fst_2376_; lean_object* v_snd_2377_; lean_object* v___x_2378_; lean_object* v_a_2379_; lean_object* v_fst_2380_; lean_object* v_snd_2381_; lean_object* v_common_2382_; lean_object* v_x_2383_; lean_object* v_y_2384_; lean_object* v___x_2385_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___x_2374_, 1);
v_fst_2376_ = lean_ctor_get(v_a_2375_, 0);
lean_inc(v_fst_2376_);
v_snd_2377_ = lean_ctor_get(v_a_2375_, 1);
lean_inc(v_snd_2377_);
lean_dec(v_a_2375_);
v___x_2378_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_2372_, v_fst_2376_, v_snd_2377_);
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref(v___x_2378_);
v_fst_2380_ = lean_ctor_get(v_a_2379_, 0);
lean_inc(v_fst_2380_);
v_snd_2381_ = lean_ctor_get(v_a_2379_, 1);
lean_inc(v_snd_2381_);
lean_dec(v_a_2379_);
v_common_2382_ = lean_ctor_get(v_fst_2380_, 0);
lean_inc_ref(v_common_2382_);
v_x_2383_ = lean_ctor_get(v_fst_2380_, 1);
lean_inc_ref(v_x_2383_);
v_y_2384_ = lean_ctor_get(v_fst_2380_, 2);
lean_inc_ref(v_y_2384_);
lean_dec(v_fst_2380_);
lean_inc_ref(v_val_2357_);
v___x_2385_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_2382_, v_val_2357_, v_snd_2381_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec_ref(v_common_2382_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v_fst_2387_; lean_object* v_snd_2388_; lean_object* v___x_2389_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_a_2386_);
lean_dec_ref_known(v___x_2385_, 1);
v_fst_2387_ = lean_ctor_get(v_a_2386_, 0);
lean_inc(v_fst_2387_);
v_snd_2388_ = lean_ctor_get(v_a_2386_, 1);
lean_inc(v_snd_2388_);
lean_dec(v_a_2386_);
lean_inc_ref(v_val_2357_);
v___x_2389_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_2383_, v_val_2357_, v_snd_2388_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec_ref(v_x_2383_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v_fst_2391_; lean_object* v_snd_2392_; lean_object* v___x_2393_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2389_, 1);
v_fst_2391_ = lean_ctor_get(v_a_2390_, 0);
lean_inc(v_fst_2391_);
v_snd_2392_ = lean_ctor_get(v_a_2390_, 1);
lean_inc(v_snd_2392_);
lean_dec(v_a_2390_);
lean_inc_ref(v_val_2357_);
v___x_2393_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_2384_, v_val_2357_, v_snd_2392_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec_ref(v_y_2384_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2458_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2396_ = v___x_2393_;
v_isShared_2397_ = v_isSharedCheck_2458_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2393_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2458_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v_fst_2398_; lean_object* v_snd_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2457_; 
v_fst_2398_ = lean_ctor_get(v_a_2394_, 0);
v_snd_2399_ = lean_ctor_get(v_a_2394_, 1);
v_isSharedCheck_2457_ = !lean_is_exclusive(v_a_2394_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2401_ = v_a_2394_;
v_isShared_2402_ = v_isSharedCheck_2457_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_snd_2399_);
lean_inc(v_fst_2398_);
lean_dec(v_a_2394_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2457_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___x_2447_; lean_object* v___f_2448_; lean_object* v___y_2450_; lean_object* v___x_2454_; 
lean_inc_ref(v_val_2357_);
v___x_2447_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2357_);
v___f_2448_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_2448_, 0, v___x_2447_);
lean_inc(v_fst_2387_);
lean_inc_ref(v___f_2448_);
v___x_2454_ = l_Option_merge___redArg(v___f_2448_, v_fst_2387_, v_fst_2391_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v___x_2455_; 
lean_inc_ref(v_val_2357_);
v___x_2455_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_2357_);
v___y_2450_ = v___x_2455_;
goto v___jp_2449_;
}
else
{
lean_object* v_val_2456_; 
v_val_2456_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_val_2456_);
lean_dec_ref_known(v___x_2454_, 1);
v___y_2450_ = v_val_2456_;
goto v___jp_2449_;
}
v___jp_2403_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; uint8_t v___x_2408_; 
lean_inc_ref(v_P_2360_);
v___x_2406_ = l_Lean_mkAppB(v_P_2360_, v_lhs_2358_, v_rhs_2359_);
v___x_2407_ = l_Lean_mkAppB(v_P_2360_, v___y_2404_, v___y_2405_);
v___x_2408_ = lean_expr_eqv(v___x_2406_, v___x_2407_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; 
lean_del_object(v___x_2396_);
lean_inc_ref(v___x_2407_);
v___x_2409_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_2406_, v___x_2407_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2411_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref_known(v___x_2409_, 1);
v___x_2411_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2407_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2423_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2414_ = v___x_2411_;
v_isShared_2415_ = v_isSharedCheck_2423_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2411_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2423_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2416_; lean_object* v___x_2418_; 
v___x_2416_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2416_, 0, v_a_2412_);
lean_ctor_set(v___x_2416_, 1, v_a_2410_);
lean_ctor_set_uint8(v___x_2416_, sizeof(void*)*2, v___x_2408_);
lean_ctor_set_uint8(v___x_2416_, sizeof(void*)*2 + 1, v___x_2408_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 0, v___x_2416_);
v___x_2418_ = v___x_2401_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2416_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_snd_2399_);
v___x_2418_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
lean_object* v___x_2420_; 
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 0, v___x_2418_);
v___x_2420_ = v___x_2414_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2418_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
lean_dec(v_a_2410_);
lean_del_object(v___x_2401_);
lean_dec(v_snd_2399_);
v_a_2424_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2411_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2411_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
lean_dec_ref(v___x_2407_);
lean_del_object(v___x_2401_);
lean_dec(v_snd_2399_);
v_a_2432_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2409_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2409_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
else
{
lean_object* v___x_2440_; lean_object* v___x_2442_; 
lean_dec_ref(v___x_2407_);
lean_dec_ref(v___x_2406_);
v___x_2440_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2440_, 0, v___y_2361_);
lean_ctor_set_uint8(v___x_2440_, 1, v___y_2361_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 0, v___x_2440_);
v___x_2442_ = v___x_2401_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2440_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v_snd_2399_);
v___x_2442_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
lean_object* v___x_2444_; 
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2442_);
v___x_2444_ = v___x_2396_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2442_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
v___jp_2449_:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Option_merge___redArg(v___f_2448_, v_fst_2387_, v_fst_2398_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v___x_2452_; 
v___x_2452_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_2357_);
v___y_2404_ = v___y_2450_;
v___y_2405_ = v___x_2452_;
goto v___jp_2403_;
}
else
{
lean_object* v_val_2453_; 
lean_dec_ref(v_val_2357_);
v_val_2453_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_val_2453_);
lean_dec_ref_known(v___x_2451_, 1);
v___y_2404_ = v___y_2450_;
v___y_2405_ = v_val_2453_;
goto v___jp_2403_;
}
}
}
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec(v_fst_2391_);
lean_dec(v_fst_2387_);
lean_dec_ref(v_P_2360_);
lean_dec_ref(v_rhs_2359_);
lean_dec_ref(v_lhs_2358_);
lean_dec_ref(v_val_2357_);
v_a_2459_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2393_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2393_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec(v_fst_2387_);
lean_dec_ref(v_y_2384_);
lean_dec_ref(v_P_2360_);
lean_dec_ref(v_rhs_2359_);
lean_dec_ref(v_lhs_2358_);
lean_dec_ref(v_val_2357_);
v_a_2467_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2389_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2389_);
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
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec_ref(v_y_2384_);
lean_dec_ref(v_x_2383_);
lean_dec_ref(v_P_2360_);
lean_dec_ref(v_rhs_2359_);
lean_dec_ref(v_lhs_2358_);
lean_dec_ref(v_val_2357_);
v_a_2475_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2385_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2385_);
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
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec(v_fst_2372_);
lean_dec_ref(v_P_2360_);
lean_dec_ref(v_rhs_2359_);
lean_dec_ref(v_lhs_2358_);
lean_dec_ref(v_val_2357_);
v_a_2483_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2374_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2374_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec_ref(v_P_2360_);
lean_dec_ref(v_rhs_2359_);
lean_dec_ref(v_lhs_2358_);
lean_dec_ref(v_val_2357_);
v_a_2491_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2370_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2370_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed(lean_object* v_val_2499_, lean_object* v_lhs_2500_, lean_object* v_rhs_2501_, lean_object* v_P_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
uint8_t v___y_188096__boxed_2512_; lean_object* v_res_2513_; 
v___y_188096__boxed_2512_ = lean_unbox(v___y_2503_);
v_res_2513_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(v_val_2499_, v_lhs_2500_, v_rhs_2501_, v_P_2502_, v___y_188096__boxed_2512_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(lean_object* v_lhs_2514_, lean_object* v_rhs_2515_, lean_object* v_P_2516_, lean_object* v_cls_2517_, uint8_t v___x_2518_, lean_object* v___f_2519_, uint8_t v___x_2520_, lean_object* v_____r_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v___x_2538_; 
lean_inc_ref(v_lhs_2514_);
v___x_2538_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2514_);
if (lean_obj_tag(v___x_2538_) == 1)
{
lean_object* v_val_2539_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; uint8_t v___y_2553_; lean_object* v___x_2578_; 
v_val_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_val_2539_);
lean_dec_ref_known(v___x_2538_, 1);
lean_inc_ref(v_rhs_2515_);
v___x_2578_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2515_);
if (lean_obj_tag(v___x_2578_) == 1)
{
lean_object* v_val_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2627_; 
v_val_2579_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2581_ = v___x_2578_;
v_isShared_2582_ = v_isSharedCheck_2627_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_val_2579_);
lean_dec(v___x_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2627_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
uint8_t v___x_2583_; 
v___x_2583_ = lean_expr_eqv(v_val_2539_, v_val_2579_);
if (v___x_2583_ == 0)
{
if (v___x_2518_ == 0)
{
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_dec_ref(v___f_2519_);
v___y_2553_ = v___x_2518_;
goto v___jp_2552_;
}
else
{
lean_object* v_toCold_2589_; lean_object* v_inheritedTraceOptions_2590_; lean_object* v___x_2591_; 
lean_dec_ref(v_P_2516_);
v_toCold_2589_ = lean_ctor_get(v___y_2529_, 0);
v_inheritedTraceOptions_2590_ = lean_ctor_get(v_toCold_2589_, 11);
lean_inc(v___y_2530_);
lean_inc_ref(v___y_2529_);
lean_inc(v___y_2528_);
lean_inc_ref(v___y_2527_);
lean_inc(v___y_2526_);
lean_inc_ref(v___y_2525_);
lean_inc(v___y_2524_);
lean_inc_ref(v___y_2523_);
lean_inc(v___y_2522_);
lean_inc_ref(v_inheritedTraceOptions_2590_);
v___x_2591_ = lean_apply_11(v___f_2519_, v_inheritedTraceOptions_2590_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, lean_box(0));
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; uint8_t v___x_2593_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2591_, 1);
v___x_2593_ = lean_unbox(v_a_2592_);
lean_dec(v_a_2592_);
if (v___x_2593_ == 0)
{
lean_dec(v_val_2579_);
lean_dec(v_val_2539_);
lean_dec(v_cls_2517_);
lean_dec_ref(v_rhs_2515_);
lean_dec_ref(v_lhs_2514_);
goto v___jp_2584_;
}
else
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2594_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1);
v___x_2595_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2539_);
v___x_2596_ = l_Lean_MessageData_ofExpr(v___x_2595_);
v___x_2597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2594_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v___x_2598_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3);
v___x_2599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2597_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = l_Lean_indentExpr(v_lhs_2514_);
v___x_2601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2599_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
v___x_2602_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5);
v___x_2603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2601_);
lean_ctor_set(v___x_2603_, 1, v___x_2602_);
v___x_2604_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2579_);
v___x_2605_ = l_Lean_MessageData_ofExpr(v___x_2604_);
v___x_2606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2603_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
v___x_2607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
lean_ctor_set(v___x_2607_, 1, v___x_2598_);
v___x_2608_ = l_Lean_indentExpr(v_rhs_2515_);
v___x_2609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2607_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
v___x_2610_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2517_, v___x_2609_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_dec_ref_known(v___x_2610_, 1);
goto v___jp_2584_;
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_del_object(v___x_2581_);
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2610_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2610_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_dec(v_val_2539_);
lean_dec(v_cls_2517_);
lean_dec_ref(v_rhs_2515_);
lean_dec_ref(v_lhs_2514_);
v_a_2619_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2591_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2591_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
}
else
{
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_dec_ref(v___f_2519_);
v___y_2553_ = v___x_2520_;
goto v___jp_2552_;
}
v___jp_2584_:
{
lean_object* v___x_2585_; lean_object* v___x_2587_; 
v___x_2585_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2585_, 0, v___x_2583_);
lean_ctor_set_uint8(v___x_2585_, 1, v___x_2583_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set_tag(v___x_2581_, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2585_);
v___x_2587_ = v___x_2581_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
else
{
lean_object* v_toCold_2628_; lean_object* v_inheritedTraceOptions_2629_; lean_object* v___x_2630_; 
lean_dec(v___x_2578_);
lean_dec(v_val_2539_);
lean_dec_ref(v_P_2516_);
lean_dec_ref(v_lhs_2514_);
v_toCold_2628_ = lean_ctor_get(v___y_2529_, 0);
v_inheritedTraceOptions_2629_ = lean_ctor_get(v_toCold_2628_, 11);
lean_inc(v___y_2530_);
lean_inc_ref(v___y_2529_);
lean_inc(v___y_2528_);
lean_inc_ref(v___y_2527_);
lean_inc(v___y_2526_);
lean_inc_ref(v___y_2525_);
lean_inc(v___y_2524_);
lean_inc_ref(v___y_2523_);
lean_inc(v___y_2522_);
lean_inc_ref(v_inheritedTraceOptions_2629_);
v___x_2630_ = lean_apply_11(v___f_2519_, v_inheritedTraceOptions_2629_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, lean_box(0));
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; uint8_t v___x_2632_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v___x_2630_, 1);
v___x_2632_ = lean_unbox(v_a_2631_);
lean_dec(v_a_2631_);
if (v___x_2632_ == 0)
{
lean_dec(v_cls_2517_);
lean_dec_ref(v_rhs_2515_);
goto v___jp_2532_;
}
else
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2633_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_2634_ = l_Lean_indentExpr(v_rhs_2515_);
v___x_2635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2633_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2517_, v___x_2635_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_dec_ref_known(v___x_2636_, 1);
goto v___jp_2532_;
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2636_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2636_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec(v_cls_2517_);
lean_dec_ref(v_rhs_2515_);
v_a_2645_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2630_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2630_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
v___jp_2540_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2548_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7);
v___x_2549_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8));
v___x_2550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2550_, 0, v_val_2539_);
lean_ctor_set(v___x_2550_, 1, v___x_2548_);
lean_ctor_set(v___x_2550_, 2, v___x_2549_);
v___x_2551_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___y_2541_, v___x_2550_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
return v___x_2551_;
}
v___jp_2552_:
{
lean_object* v_toCold_2554_; lean_object* v_options_2555_; lean_object* v_inheritedTraceOptions_2556_; uint8_t v_hasTrace_2557_; lean_object* v___x_2558_; lean_object* v___f_2559_; 
v_toCold_2554_ = lean_ctor_get(v___y_2529_, 0);
v_options_2555_ = lean_ctor_get(v_toCold_2554_, 2);
v_inheritedTraceOptions_2556_ = lean_ctor_get(v_toCold_2554_, 11);
v_hasTrace_2557_ = lean_ctor_get_uint8(v_options_2555_, sizeof(void*)*1);
v___x_2558_ = lean_box(v___y_2553_);
lean_inc(v_val_2539_);
v___f_2559_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed), 13, 5);
lean_closure_set(v___f_2559_, 0, v_val_2539_);
lean_closure_set(v___f_2559_, 1, v_lhs_2514_);
lean_closure_set(v___f_2559_, 2, v_rhs_2515_);
lean_closure_set(v___f_2559_, 3, v_P_2516_);
lean_closure_set(v___f_2559_, 4, v___x_2558_);
if (v_hasTrace_2557_ == 0)
{
lean_dec(v_cls_2517_);
v___y_2541_ = v___f_2559_;
v___y_2542_ = v___y_2525_;
v___y_2543_ = v___y_2526_;
v___y_2544_ = v___y_2527_;
v___y_2545_ = v___y_2528_;
v___y_2546_ = v___y_2529_;
v___y_2547_ = v___y_2530_;
goto v___jp_2540_;
}
else
{
lean_object* v___x_2560_; lean_object* v___x_2561_; uint8_t v___x_2562_; 
v___x_2560_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2517_);
v___x_2561_ = l_Lean_Name_append(v___x_2560_, v_cls_2517_);
v___x_2562_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2556_, v_options_2555_, v___x_2561_);
lean_dec(v___x_2561_);
if (v___x_2562_ == 0)
{
lean_dec(v_cls_2517_);
v___y_2541_ = v___f_2559_;
v___y_2542_ = v___y_2525_;
v___y_2543_ = v___y_2526_;
v___y_2544_ = v___y_2527_;
v___y_2545_ = v___y_2528_;
v___y_2546_ = v___y_2529_;
v___y_2547_ = v___y_2530_;
goto v___jp_2540_;
}
else
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2563_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10);
lean_inc(v_val_2539_);
v___x_2564_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2539_);
v___x_2565_ = l_Lean_MessageData_ofExpr(v___x_2564_);
v___x_2566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2563_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12);
v___x_2568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2566_);
lean_ctor_set(v___x_2568_, 1, v___x_2567_);
v___x_2569_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2517_, v___x_2568_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_dec_ref_known(v___x_2569_, 1);
v___y_2541_ = v___f_2559_;
v___y_2542_ = v___y_2525_;
v___y_2543_ = v___y_2526_;
v___y_2544_ = v___y_2527_;
v___y_2545_ = v___y_2528_;
v___y_2546_ = v___y_2529_;
v___y_2547_ = v___y_2530_;
goto v___jp_2540_;
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_dec_ref(v___f_2559_);
lean_dec(v_val_2539_);
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_2653_; lean_object* v_inheritedTraceOptions_2654_; lean_object* v___x_2655_; 
lean_dec(v___x_2538_);
lean_dec_ref(v_P_2516_);
lean_dec_ref(v_rhs_2515_);
v_toCold_2653_ = lean_ctor_get(v___y_2529_, 0);
v_inheritedTraceOptions_2654_ = lean_ctor_get(v_toCold_2653_, 11);
lean_inc(v___y_2530_);
lean_inc_ref(v___y_2529_);
lean_inc(v___y_2528_);
lean_inc_ref(v___y_2527_);
lean_inc(v___y_2526_);
lean_inc_ref(v___y_2525_);
lean_inc(v___y_2524_);
lean_inc_ref(v___y_2523_);
lean_inc(v___y_2522_);
lean_inc_ref(v_inheritedTraceOptions_2654_);
v___x_2655_ = lean_apply_11(v___f_2519_, v_inheritedTraceOptions_2654_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, lean_box(0));
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; uint8_t v___x_2657_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2655_, 1);
v___x_2657_ = lean_unbox(v_a_2656_);
lean_dec(v_a_2656_);
if (v___x_2657_ == 0)
{
lean_dec(v_cls_2517_);
lean_dec_ref(v_lhs_2514_);
goto v___jp_2535_;
}
else
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2658_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_2659_ = l_Lean_indentExpr(v_lhs_2514_);
v___x_2660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2658_);
lean_ctor_set(v___x_2660_, 1, v___x_2659_);
v___x_2661_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2517_, v___x_2660_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_dec_ref_known(v___x_2661_, 1);
goto v___jp_2535_;
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2661_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2661_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
lean_dec(v_cls_2517_);
lean_dec_ref(v_lhs_2514_);
v_a_2670_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2655_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2655_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
v___jp_2532_:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2533_, 0, v___x_2520_);
lean_ctor_set_uint8(v___x_2533_, 1, v___x_2520_);
v___x_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2533_);
return v___x_2534_;
}
v___jp_2535_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2536_, 0, v___x_2520_);
lean_ctor_set_uint8(v___x_2536_, 1, v___x_2520_);
v___x_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
return v___x_2537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___boxed(lean_object** _args){
lean_object* v_lhs_2678_ = _args[0];
lean_object* v_rhs_2679_ = _args[1];
lean_object* v_P_2680_ = _args[2];
lean_object* v_cls_2681_ = _args[3];
lean_object* v___x_2682_ = _args[4];
lean_object* v___f_2683_ = _args[5];
lean_object* v___x_2684_ = _args[6];
lean_object* v_____r_2685_ = _args[7];
lean_object* v___y_2686_ = _args[8];
lean_object* v___y_2687_ = _args[9];
lean_object* v___y_2688_ = _args[10];
lean_object* v___y_2689_ = _args[11];
lean_object* v___y_2690_ = _args[12];
lean_object* v___y_2691_ = _args[13];
lean_object* v___y_2692_ = _args[14];
lean_object* v___y_2693_ = _args[15];
lean_object* v___y_2694_ = _args[16];
lean_object* v___y_2695_ = _args[17];
_start:
{
uint8_t v___x_188418__boxed_2696_; uint8_t v___x_188420__boxed_2697_; lean_object* v_res_2698_; 
v___x_188418__boxed_2696_ = lean_unbox(v___x_2682_);
v___x_188420__boxed_2697_ = lean_unbox(v___x_2684_);
v_res_2698_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2678_, v_rhs_2679_, v_P_2680_, v_cls_2681_, v___x_188418__boxed_2696_, v___f_2683_, v___x_188420__boxed_2697_, v_____r_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
return v_res_2698_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(lean_object* v_e_2699_){
_start:
{
if (lean_obj_tag(v_e_2699_) == 0)
{
uint8_t v___x_2700_; 
v___x_2700_ = 2;
return v___x_2700_;
}
else
{
uint8_t v___x_2701_; 
v___x_2701_ = 0;
return v___x_2701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5___boxed(lean_object* v_e_2702_){
_start:
{
uint8_t v_res_2703_; lean_object* v_r_2704_; 
v_res_2703_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_e_2702_);
lean_dec_ref(v_e_2702_);
v_r_2704_ = lean_box(v_res_2703_);
return v_r_2704_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(lean_object* v_x_2705_){
_start:
{
if (lean_obj_tag(v_x_2705_) == 0)
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
v_a_2707_ = lean_ctor_get(v_x_2705_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_x_2705_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v_x_2705_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v_x_2705_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
lean_ctor_set_tag(v___x_2709_, 1);
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
else
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
v_a_2715_ = lean_ctor_get(v_x_2705_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v_x_2705_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v_x_2705_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v_x_2705_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
lean_ctor_set_tag(v___x_2717_, 0);
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
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
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg___boxed(lean_object* v_x_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_2723_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(lean_object* v_opts_2726_, lean_object* v_opt_2727_){
_start:
{
lean_object* v_name_2728_; lean_object* v_defValue_2729_; lean_object* v_map_2730_; lean_object* v___x_2731_; 
v_name_2728_ = lean_ctor_get(v_opt_2727_, 0);
v_defValue_2729_ = lean_ctor_get(v_opt_2727_, 1);
v_map_2730_ = lean_ctor_get(v_opts_2726_, 0);
v___x_2731_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2730_, v_name_2728_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_inc(v_defValue_2729_);
return v_defValue_2729_;
}
else
{
lean_object* v_val_2732_; 
v_val_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_val_2732_);
lean_dec_ref_known(v___x_2731_, 1);
if (lean_obj_tag(v_val_2732_) == 3)
{
lean_object* v_v_2733_; 
v_v_2733_ = lean_ctor_get(v_val_2732_, 0);
lean_inc(v_v_2733_);
lean_dec_ref_known(v_val_2732_, 1);
return v_v_2733_;
}
else
{
lean_dec(v_val_2732_);
lean_inc(v_defValue_2729_);
return v_defValue_2729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6___boxed(lean_object* v_opts_2734_, lean_object* v_opt_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2734_, v_opt_2735_);
lean_dec_ref(v_opt_2735_);
lean_dec_ref(v_opts_2734_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(size_t v_sz_2737_, size_t v_i_2738_, lean_object* v_bs_2739_){
_start:
{
uint8_t v___x_2740_; 
v___x_2740_ = lean_usize_dec_lt(v_i_2738_, v_sz_2737_);
if (v___x_2740_ == 0)
{
return v_bs_2739_;
}
else
{
lean_object* v_v_2741_; lean_object* v_msg_2742_; lean_object* v___x_2743_; lean_object* v_bs_x27_2744_; size_t v___x_2745_; size_t v___x_2746_; lean_object* v___x_2747_; 
v_v_2741_ = lean_array_uget_borrowed(v_bs_2739_, v_i_2738_);
v_msg_2742_ = lean_ctor_get(v_v_2741_, 1);
lean_inc_ref(v_msg_2742_);
v___x_2743_ = lean_unsigned_to_nat(0u);
v_bs_x27_2744_ = lean_array_uset(v_bs_2739_, v_i_2738_, v___x_2743_);
v___x_2745_ = ((size_t)1ULL);
v___x_2746_ = lean_usize_add(v_i_2738_, v___x_2745_);
v___x_2747_ = lean_array_uset(v_bs_x27_2744_, v_i_2738_, v_msg_2742_);
v_i_2738_ = v___x_2746_;
v_bs_2739_ = v___x_2747_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2749_, lean_object* v_i_2750_, lean_object* v_bs_2751_){
_start:
{
size_t v_sz_boxed_2752_; size_t v_i_boxed_2753_; lean_object* v_res_2754_; 
v_sz_boxed_2752_ = lean_unbox_usize(v_sz_2749_);
lean_dec(v_sz_2749_);
v_i_boxed_2753_ = lean_unbox_usize(v_i_2750_);
lean_dec(v_i_2750_);
v_res_2754_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_boxed_2752_, v_i_boxed_2753_, v_bs_2751_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(lean_object* v_oldTraces_2755_, lean_object* v_data_2756_, lean_object* v_ref_2757_, lean_object* v_msg_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v_toCold_2764_; lean_object* v_currRecDepth_2765_; lean_object* v_ref_2766_; uint8_t v_diag_2767_; uint8_t v_suppressElabErrors_2768_; lean_object* v___x_2769_; lean_object* v_traceState_2770_; lean_object* v_traces_2771_; lean_object* v_ref_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; size_t v_sz_2775_; size_t v___x_2776_; lean_object* v___x_2777_; lean_object* v_msg_2778_; lean_object* v___x_2779_; lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2817_; 
v_toCold_2764_ = lean_ctor_get(v___y_2761_, 0);
v_currRecDepth_2765_ = lean_ctor_get(v___y_2761_, 1);
v_ref_2766_ = lean_ctor_get(v___y_2761_, 2);
v_diag_2767_ = lean_ctor_get_uint8(v___y_2761_, sizeof(void*)*3);
v_suppressElabErrors_2768_ = lean_ctor_get_uint8(v___y_2761_, sizeof(void*)*3 + 1);
v___x_2769_ = lean_st_ref_get(v___y_2762_);
v_traceState_2770_ = lean_ctor_get(v___x_2769_, 4);
lean_inc_ref(v_traceState_2770_);
lean_dec(v___x_2769_);
v_traces_2771_ = lean_ctor_get(v_traceState_2770_, 0);
lean_inc_ref(v_traces_2771_);
lean_dec_ref(v_traceState_2770_);
v_ref_2772_ = l_Lean_replaceRef(v_ref_2757_, v_ref_2766_);
lean_inc(v_currRecDepth_2765_);
lean_inc_ref(v_toCold_2764_);
v___x_2773_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2773_, 0, v_toCold_2764_);
lean_ctor_set(v___x_2773_, 1, v_currRecDepth_2765_);
lean_ctor_set(v___x_2773_, 2, v_ref_2772_);
lean_ctor_set_uint8(v___x_2773_, sizeof(void*)*3, v_diag_2767_);
lean_ctor_set_uint8(v___x_2773_, sizeof(void*)*3 + 1, v_suppressElabErrors_2768_);
v___x_2774_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2771_);
lean_dec_ref(v_traces_2771_);
v_sz_2775_ = lean_array_size(v___x_2774_);
v___x_2776_ = ((size_t)0ULL);
v___x_2777_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_2775_, v___x_2776_, v___x_2774_);
v_msg_2778_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2778_, 0, v_data_2756_);
lean_ctor_set(v_msg_2778_, 1, v_msg_2758_);
lean_ctor_set(v_msg_2778_, 2, v___x_2777_);
v___x_2779_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2778_, v___y_2759_, v___y_2760_, v___x_2773_, v___y_2762_);
lean_dec_ref_known(v___x_2773_, 3);
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2782_ = v___x_2779_;
v_isShared_2783_ = v_isSharedCheck_2817_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2779_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2817_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; lean_object* v_traceState_2785_; lean_object* v_env_2786_; lean_object* v_nextMacroScope_2787_; lean_object* v_ngen_2788_; lean_object* v_auxDeclNGen_2789_; lean_object* v_cache_2790_; lean_object* v_messages_2791_; lean_object* v_infoState_2792_; lean_object* v_snapshotTasks_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2816_; 
v___x_2784_ = lean_st_ref_take(v___y_2762_);
v_traceState_2785_ = lean_ctor_get(v___x_2784_, 4);
v_env_2786_ = lean_ctor_get(v___x_2784_, 0);
v_nextMacroScope_2787_ = lean_ctor_get(v___x_2784_, 1);
v_ngen_2788_ = lean_ctor_get(v___x_2784_, 2);
v_auxDeclNGen_2789_ = lean_ctor_get(v___x_2784_, 3);
v_cache_2790_ = lean_ctor_get(v___x_2784_, 5);
v_messages_2791_ = lean_ctor_get(v___x_2784_, 6);
v_infoState_2792_ = lean_ctor_get(v___x_2784_, 7);
v_snapshotTasks_2793_ = lean_ctor_get(v___x_2784_, 8);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2795_ = v___x_2784_;
v_isShared_2796_ = v_isSharedCheck_2816_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_snapshotTasks_2793_);
lean_inc(v_infoState_2792_);
lean_inc(v_messages_2791_);
lean_inc(v_cache_2790_);
lean_inc(v_traceState_2785_);
lean_inc(v_auxDeclNGen_2789_);
lean_inc(v_ngen_2788_);
lean_inc(v_nextMacroScope_2787_);
lean_inc(v_env_2786_);
lean_dec(v___x_2784_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2816_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
uint64_t v_tid_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2814_; 
v_tid_2797_ = lean_ctor_get_uint64(v_traceState_2785_, sizeof(void*)*1);
v_isSharedCheck_2814_ = !lean_is_exclusive(v_traceState_2785_);
if (v_isSharedCheck_2814_ == 0)
{
lean_object* v_unused_2815_; 
v_unused_2815_ = lean_ctor_get(v_traceState_2785_, 0);
lean_dec(v_unused_2815_);
v___x_2799_ = v_traceState_2785_;
v_isShared_2800_ = v_isSharedCheck_2814_;
goto v_resetjp_2798_;
}
else
{
lean_dec(v_traceState_2785_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2814_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2804_; 
v___x_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2801_, 0, v_ref_2757_);
lean_ctor_set(v___x_2801_, 1, v_a_2780_);
v___x_2802_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2755_, v___x_2801_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___x_2802_);
v___x_2804_ = v___x_2799_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2802_);
lean_ctor_set_uint64(v_reuseFailAlloc_2813_, sizeof(void*)*1, v_tid_2797_);
v___x_2804_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
lean_object* v___x_2806_; 
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 4, v___x_2804_);
v___x_2806_ = v___x_2795_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_env_2786_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_nextMacroScope_2787_);
lean_ctor_set(v_reuseFailAlloc_2812_, 2, v_ngen_2788_);
lean_ctor_set(v_reuseFailAlloc_2812_, 3, v_auxDeclNGen_2789_);
lean_ctor_set(v_reuseFailAlloc_2812_, 4, v___x_2804_);
lean_ctor_set(v_reuseFailAlloc_2812_, 5, v_cache_2790_);
lean_ctor_set(v_reuseFailAlloc_2812_, 6, v_messages_2791_);
lean_ctor_set(v_reuseFailAlloc_2812_, 7, v_infoState_2792_);
lean_ctor_set(v_reuseFailAlloc_2812_, 8, v_snapshotTasks_2793_);
v___x_2806_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2810_; 
v___x_2807_ = lean_st_ref_put(v___y_2762_, v___x_2806_);
v___x_2808_ = lean_box(0);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v___x_2808_);
v___x_2810_ = v___x_2782_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2808_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_2818_, lean_object* v_data_2819_, lean_object* v_ref_2820_, lean_object* v_msg_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v_res_2827_; 
v_res_2827_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_2818_, v_data_2819_, v_ref_2820_, v_msg_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
return v_res_2827_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__0));
v___x_2830_ = l_Lean_stringToMessageData(v___x_2829_);
return v___x_2830_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2831_; double v___x_2832_; 
v___x_2831_ = lean_unsigned_to_nat(1000u);
v___x_2832_ = lean_float_of_nat(v___x_2831_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(lean_object* v_cls_2833_, uint8_t v_collapsed_2834_, lean_object* v_tag_2835_, lean_object* v_opts_2836_, uint8_t v_clsEnabled_2837_, lean_object* v_oldTraces_2838_, lean_object* v_msg_2839_, lean_object* v_resStartStop_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v_fst_2851_; lean_object* v_snd_2852_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v_data_2856_; lean_object* v_fst_2867_; lean_object* v_snd_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; lean_object* v___y_2872_; lean_object* v_a_2873_; uint8_t v___y_2888_; double v___y_2919_; 
v_fst_2851_ = lean_ctor_get(v_resStartStop_2840_, 0);
lean_inc(v_fst_2851_);
v_snd_2852_ = lean_ctor_get(v_resStartStop_2840_, 1);
lean_inc(v_snd_2852_);
lean_dec_ref(v_resStartStop_2840_);
v_fst_2867_ = lean_ctor_get(v_snd_2852_, 0);
lean_inc(v_fst_2867_);
v_snd_2868_ = lean_ctor_get(v_snd_2852_, 1);
lean_inc(v_snd_2868_);
lean_dec(v_snd_2852_);
v___x_2869_ = l_Lean_trace_profiler;
v___x_2870_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_2836_, v___x_2869_);
if (v___x_2870_ == 0)
{
v___y_2888_ = v___x_2870_;
goto v___jp_2887_;
}
else
{
lean_object* v___x_2924_; uint8_t v___x_2925_; 
v___x_2924_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2925_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_2836_, v___x_2924_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2926_; lean_object* v___x_2927_; double v___x_2928_; double v___x_2929_; double v___x_2930_; 
v___x_2926_ = l_Lean_trace_profiler_threshold;
v___x_2927_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2836_, v___x_2926_);
v___x_2928_ = lean_float_of_nat(v___x_2927_);
v___x_2929_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2);
v___x_2930_ = lean_float_div(v___x_2928_, v___x_2929_);
v___y_2919_ = v___x_2930_;
goto v___jp_2918_;
}
else
{
lean_object* v___x_2931_; lean_object* v___x_2932_; double v___x_2933_; 
v___x_2931_ = l_Lean_trace_profiler_threshold;
v___x_2932_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2836_, v___x_2931_);
v___x_2933_ = lean_float_of_nat(v___x_2932_);
v___y_2919_ = v___x_2933_;
goto v___jp_2918_;
}
}
v___jp_2853_:
{
lean_object* v___x_2857_; 
lean_inc(v___y_2855_);
v___x_2857_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_2838_, v_data_2856_, v___y_2855_, v___y_2854_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v___x_2858_; 
lean_dec_ref_known(v___x_2857_, 1);
v___x_2858_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_fst_2851_);
return v___x_2858_;
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
lean_dec(v_fst_2851_);
v_a_2859_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v___x_2857_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2857_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2859_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
v___jp_2871_:
{
uint8_t v_result_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; double v___x_2877_; lean_object* v_data_2878_; 
v_result_2874_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_fst_2851_);
v___x_2875_ = lean_box(v_result_2874_);
v___x_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
v___x_2877_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2835_);
lean_inc_ref(v___x_2876_);
lean_inc(v_cls_2833_);
v_data_2878_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2878_, 0, v_cls_2833_);
lean_ctor_set(v_data_2878_, 1, v___x_2876_);
lean_ctor_set(v_data_2878_, 2, v_tag_2835_);
lean_ctor_set_float(v_data_2878_, sizeof(void*)*3, v___x_2877_);
lean_ctor_set_float(v_data_2878_, sizeof(void*)*3 + 8, v___x_2877_);
lean_ctor_set_uint8(v_data_2878_, sizeof(void*)*3 + 16, v_collapsed_2834_);
if (v___x_2870_ == 0)
{
lean_dec_ref_known(v___x_2876_, 1);
lean_dec(v_snd_2868_);
lean_dec(v_fst_2867_);
lean_dec_ref(v_tag_2835_);
lean_dec(v_cls_2833_);
v___y_2854_ = v_a_2873_;
v___y_2855_ = v___y_2872_;
v_data_2856_ = v_data_2878_;
goto v___jp_2853_;
}
else
{
lean_object* v_data_2879_; double v___x_2880_; double v___x_2881_; 
lean_dec_ref_known(v_data_2878_, 3);
v_data_2879_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2879_, 0, v_cls_2833_);
lean_ctor_set(v_data_2879_, 1, v___x_2876_);
lean_ctor_set(v_data_2879_, 2, v_tag_2835_);
v___x_2880_ = lean_unbox_float(v_fst_2867_);
lean_dec(v_fst_2867_);
lean_ctor_set_float(v_data_2879_, sizeof(void*)*3, v___x_2880_);
v___x_2881_ = lean_unbox_float(v_snd_2868_);
lean_dec(v_snd_2868_);
lean_ctor_set_float(v_data_2879_, sizeof(void*)*3 + 8, v___x_2881_);
lean_ctor_set_uint8(v_data_2879_, sizeof(void*)*3 + 16, v_collapsed_2834_);
v___y_2854_ = v_a_2873_;
v___y_2855_ = v___y_2872_;
v_data_2856_ = v_data_2879_;
goto v___jp_2853_;
}
}
v___jp_2882_:
{
lean_object* v_ref_2883_; lean_object* v___x_2884_; 
v_ref_2883_ = lean_ctor_get(v___y_2848_, 2);
lean_inc(v___y_2849_);
lean_inc_ref(v___y_2848_);
lean_inc(v___y_2847_);
lean_inc_ref(v___y_2846_);
lean_inc(v___y_2845_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc_ref(v___y_2842_);
lean_inc(v___y_2841_);
lean_inc(v_fst_2851_);
v___x_2884_ = lean_apply_11(v_msg_2839_, v_fst_2851_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, lean_box(0));
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
lean_dec_ref_known(v___x_2884_, 1);
v___y_2872_ = v_ref_2883_;
v_a_2873_ = v_a_2885_;
goto v___jp_2871_;
}
else
{
lean_object* v___x_2886_; 
lean_dec_ref_known(v___x_2884_, 1);
v___x_2886_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1);
v___y_2872_ = v_ref_2883_;
v_a_2873_ = v___x_2886_;
goto v___jp_2871_;
}
}
v___jp_2887_:
{
if (v_clsEnabled_2837_ == 0)
{
if (v___y_2888_ == 0)
{
lean_object* v___x_2889_; lean_object* v_traceState_2890_; lean_object* v_env_2891_; lean_object* v_nextMacroScope_2892_; lean_object* v_ngen_2893_; lean_object* v_auxDeclNGen_2894_; lean_object* v_cache_2895_; lean_object* v_messages_2896_; lean_object* v_infoState_2897_; lean_object* v_snapshotTasks_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2917_; 
lean_dec(v_snd_2868_);
lean_dec(v_fst_2867_);
lean_dec_ref(v_msg_2839_);
lean_dec_ref(v_tag_2835_);
lean_dec(v_cls_2833_);
v___x_2889_ = lean_st_ref_take(v___y_2849_);
v_traceState_2890_ = lean_ctor_get(v___x_2889_, 4);
v_env_2891_ = lean_ctor_get(v___x_2889_, 0);
v_nextMacroScope_2892_ = lean_ctor_get(v___x_2889_, 1);
v_ngen_2893_ = lean_ctor_get(v___x_2889_, 2);
v_auxDeclNGen_2894_ = lean_ctor_get(v___x_2889_, 3);
v_cache_2895_ = lean_ctor_get(v___x_2889_, 5);
v_messages_2896_ = lean_ctor_get(v___x_2889_, 6);
v_infoState_2897_ = lean_ctor_get(v___x_2889_, 7);
v_snapshotTasks_2898_ = lean_ctor_get(v___x_2889_, 8);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2900_ = v___x_2889_;
v_isShared_2901_ = v_isSharedCheck_2917_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_snapshotTasks_2898_);
lean_inc(v_infoState_2897_);
lean_inc(v_messages_2896_);
lean_inc(v_cache_2895_);
lean_inc(v_traceState_2890_);
lean_inc(v_auxDeclNGen_2894_);
lean_inc(v_ngen_2893_);
lean_inc(v_nextMacroScope_2892_);
lean_inc(v_env_2891_);
lean_dec(v___x_2889_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2917_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
uint64_t v_tid_2902_; lean_object* v_traces_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2916_; 
v_tid_2902_ = lean_ctor_get_uint64(v_traceState_2890_, sizeof(void*)*1);
v_traces_2903_ = lean_ctor_get(v_traceState_2890_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_traceState_2890_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2905_ = v_traceState_2890_;
v_isShared_2906_ = v_isSharedCheck_2916_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_traces_2903_);
lean_dec(v_traceState_2890_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2916_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2907_; lean_object* v___x_2909_; 
v___x_2907_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2838_, v_traces_2903_);
lean_dec_ref(v_traces_2903_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v___x_2907_);
v___x_2909_ = v___x_2905_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2907_);
lean_ctor_set_uint64(v_reuseFailAlloc_2915_, sizeof(void*)*1, v_tid_2902_);
v___x_2909_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
lean_object* v___x_2911_; 
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 4, v___x_2909_);
v___x_2911_ = v___x_2900_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_env_2891_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v_nextMacroScope_2892_);
lean_ctor_set(v_reuseFailAlloc_2914_, 2, v_ngen_2893_);
lean_ctor_set(v_reuseFailAlloc_2914_, 3, v_auxDeclNGen_2894_);
lean_ctor_set(v_reuseFailAlloc_2914_, 4, v___x_2909_);
lean_ctor_set(v_reuseFailAlloc_2914_, 5, v_cache_2895_);
lean_ctor_set(v_reuseFailAlloc_2914_, 6, v_messages_2896_);
lean_ctor_set(v_reuseFailAlloc_2914_, 7, v_infoState_2897_);
lean_ctor_set(v_reuseFailAlloc_2914_, 8, v_snapshotTasks_2898_);
v___x_2911_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = lean_st_ref_put(v___y_2849_, v___x_2911_);
v___x_2913_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_fst_2851_);
return v___x_2913_;
}
}
}
}
}
else
{
goto v___jp_2882_;
}
}
else
{
goto v___jp_2882_;
}
}
v___jp_2918_:
{
double v___x_2920_; double v___x_2921_; double v___x_2922_; uint8_t v___x_2923_; 
v___x_2920_ = lean_unbox_float(v_snd_2868_);
v___x_2921_ = lean_unbox_float(v_fst_2867_);
v___x_2922_ = lean_float_sub(v___x_2920_, v___x_2921_);
v___x_2923_ = lean_float_decLt(v___y_2919_, v___x_2922_);
v___y_2888_ = v___x_2923_;
goto v___jp_2887_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___boxed(lean_object** _args){
lean_object* v_cls_2934_ = _args[0];
lean_object* v_collapsed_2935_ = _args[1];
lean_object* v_tag_2936_ = _args[2];
lean_object* v_opts_2937_ = _args[3];
lean_object* v_clsEnabled_2938_ = _args[4];
lean_object* v_oldTraces_2939_ = _args[5];
lean_object* v_msg_2940_ = _args[6];
lean_object* v_resStartStop_2941_ = _args[7];
lean_object* v___y_2942_ = _args[8];
lean_object* v___y_2943_ = _args[9];
lean_object* v___y_2944_ = _args[10];
lean_object* v___y_2945_ = _args[11];
lean_object* v___y_2946_ = _args[12];
lean_object* v___y_2947_ = _args[13];
lean_object* v___y_2948_ = _args[14];
lean_object* v___y_2949_ = _args[15];
lean_object* v___y_2950_ = _args[16];
lean_object* v___y_2951_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2952_; uint8_t v_clsEnabled_boxed_2953_; lean_object* v_res_2954_; 
v_collapsed_boxed_2952_ = lean_unbox(v_collapsed_2935_);
v_clsEnabled_boxed_2953_ = lean_unbox(v_clsEnabled_2938_);
v_res_2954_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_2934_, v_collapsed_boxed_2952_, v_tag_2936_, v_opts_2937_, v_clsEnabled_boxed_2953_, v_oldTraces_2939_, v_msg_2940_, v_resStartStop_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec_ref(v_opts_2937_);
return v_res_2954_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3(void){
_start:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2960_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2));
v___x_2961_ = l_Lean_stringToMessageData(v___x_2960_);
return v___x_2961_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5(void){
_start:
{
lean_object* v___x_2963_; double v___x_2964_; 
v___x_2963_ = lean_unsigned_to_nat(1000000000u);
v___x_2964_ = lean_float_of_nat(v___x_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(lean_object* v_P_2965_, lean_object* v_lhs_2966_, lean_object* v_rhs_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_){
_start:
{
uint8_t v___y_2979_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v_toCold_3001_; lean_object* v_options_3002_; lean_object* v_inheritedTraceOptions_3003_; uint8_t v_hasTrace_3004_; lean_object* v_cls_3005_; lean_object* v___f_3006_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; uint8_t v_____do__lift_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; 
v_toCold_3001_ = lean_ctor_get(v_a_2975_, 0);
v_options_3002_ = lean_ctor_get(v_toCold_3001_, 2);
v_inheritedTraceOptions_3003_ = lean_ctor_get(v_toCold_3001_, 11);
v_hasTrace_3004_ = lean_ctor_get_uint8(v_options_3002_, sizeof(void*)*1);
v_cls_3005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___f_3006_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1));
if (v_hasTrace_3004_ == 0)
{
lean_object* v___x_3134_; lean_object* v_a_3135_; uint8_t v___x_3136_; 
v___x_3134_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3005_, v_inheritedTraceOptions_3003_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_a_3135_);
lean_dec_ref(v___x_3134_);
v___x_3136_ = lean_unbox(v_a_3135_);
lean_dec(v_a_3135_);
v_____do__lift_3111_ = v___x_3136_;
v___y_3112_ = v_a_2968_;
v___y_3113_ = v_a_2969_;
v___y_3114_ = v_a_2970_;
v___y_3115_ = v_a_2971_;
v___y_3116_ = v_a_2972_;
v___y_3117_ = v_a_2973_;
v___y_3118_ = v_a_2974_;
v___y_3119_ = v_a_2975_;
v___y_3120_ = v_a_2976_;
goto v___jp_3110_;
}
else
{
lean_object* v___f_3137_; uint8_t v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; uint8_t v___x_3141_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v_a_3145_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v_a_3157_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v_a_3175_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v_a_3190_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; 
v___f_3137_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4));
v___x_3138_ = 0;
v___x_3139_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_3140_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3141_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3003_, v_options_3002_, v___x_3140_);
if (v___x_3141_ == 0)
{
lean_object* v___x_3238_; uint8_t v___x_3239_; 
v___x_3238_ = l_Lean_trace_profiler;
v___x_3239_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_3002_, v___x_3238_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; lean_object* v_a_3241_; uint8_t v___x_3242_; 
v___x_3240_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3005_, v_inheritedTraceOptions_3003_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
lean_inc(v_a_3241_);
lean_dec_ref(v___x_3240_);
v___x_3242_ = lean_unbox(v_a_3241_);
lean_dec(v_a_3241_);
v_____do__lift_3111_ = v___x_3242_;
v___y_3112_ = v_a_2968_;
v___y_3113_ = v_a_2969_;
v___y_3114_ = v_a_2970_;
v___y_3115_ = v_a_2971_;
v___y_3116_ = v_a_2972_;
v___y_3117_ = v_a_2973_;
v___y_3118_ = v_a_2974_;
v___y_3119_ = v_a_2975_;
v___y_3120_ = v_a_2976_;
goto v___jp_3110_;
}
else
{
goto v___jp_3205_;
}
}
else
{
goto v___jp_3205_;
}
v___jp_3142_:
{
lean_object* v___x_3146_; double v___x_3147_; double v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3146_ = lean_io_get_num_heartbeats();
v___x_3147_ = lean_float_of_nat(v___y_3143_);
v___x_3148_ = lean_float_of_nat(v___x_3146_);
v___x_3149_ = lean_box_float(v___x_3147_);
v___x_3150_ = lean_box_float(v___x_3148_);
v___x_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3149_);
lean_ctor_set(v___x_3151_, 1, v___x_3150_);
v___x_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3152_, 0, v_a_3145_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
v___x_3153_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_3005_, v___x_3138_, v___x_3139_, v_options_3002_, v___x_3141_, v___y_3144_, v___f_3137_, v___x_3152_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
return v___x_3153_;
}
v___jp_3154_:
{
lean_object* v___x_3158_; 
v___x_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3158_, 0, v_a_3157_);
v___y_3143_ = v___y_3155_;
v___y_3144_ = v___y_3156_;
v_a_3145_ = v___x_3158_;
goto v___jp_3142_;
}
v___jp_3159_:
{
if (lean_obj_tag(v___y_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
v_a_3163_ = lean_ctor_get(v___y_3162_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___y_3162_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___y_3162_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___y_3162_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
lean_ctor_set_tag(v___x_3165_, 1);
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
v___y_3143_ = v___y_3160_;
v___y_3144_ = v___y_3161_;
v_a_3145_ = v___x_3168_;
goto v___jp_3142_;
}
}
}
else
{
lean_object* v_a_3171_; 
v_a_3171_ = lean_ctor_get(v___y_3162_, 0);
lean_inc(v_a_3171_);
lean_dec_ref_known(v___y_3162_, 1);
v___y_3155_ = v___y_3160_;
v___y_3156_ = v___y_3161_;
v_a_3157_ = v_a_3171_;
goto v___jp_3154_;
}
}
v___jp_3172_:
{
lean_object* v___x_3176_; double v___x_3177_; double v___x_3178_; double v___x_3179_; double v___x_3180_; double v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3176_ = lean_io_mono_nanos_now();
v___x_3177_ = lean_float_of_nat(v___y_3173_);
v___x_3178_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5);
v___x_3179_ = lean_float_div(v___x_3177_, v___x_3178_);
v___x_3180_ = lean_float_of_nat(v___x_3176_);
v___x_3181_ = lean_float_div(v___x_3180_, v___x_3178_);
v___x_3182_ = lean_box_float(v___x_3179_);
v___x_3183_ = lean_box_float(v___x_3181_);
v___x_3184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3182_);
lean_ctor_set(v___x_3184_, 1, v___x_3183_);
v___x_3185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3185_, 0, v_a_3175_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
v___x_3186_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_3005_, v___x_3138_, v___x_3139_, v_options_3002_, v___x_3141_, v___y_3174_, v___f_3137_, v___x_3185_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
return v___x_3186_;
}
v___jp_3187_:
{
lean_object* v___x_3191_; 
v___x_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3191_, 0, v_a_3190_);
v___y_3173_ = v___y_3188_;
v___y_3174_ = v___y_3189_;
v_a_3175_ = v___x_3191_;
goto v___jp_3172_;
}
v___jp_3192_:
{
if (lean_obj_tag(v___y_3195_) == 0)
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
v_a_3196_ = lean_ctor_get(v___y_3195_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___y_3195_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___y_3195_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___y_3195_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
lean_ctor_set_tag(v___x_3198_, 1);
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
v___y_3173_ = v___y_3193_;
v___y_3174_ = v___y_3194_;
v_a_3175_ = v___x_3201_;
goto v___jp_3172_;
}
}
}
else
{
lean_object* v_a_3204_; 
v_a_3204_ = lean_ctor_get(v___y_3195_, 0);
lean_inc(v_a_3204_);
lean_dec_ref_known(v___y_3195_, 1);
v___y_3188_ = v___y_3193_;
v___y_3189_ = v___y_3194_;
v_a_3190_ = v_a_3204_;
goto v___jp_3187_;
}
}
v___jp_3205_:
{
lean_object* v___x_3206_; lean_object* v_a_3207_; lean_object* v___x_3208_; uint8_t v___x_3209_; 
v___x_3206_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v_a_2976_);
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
lean_inc(v_a_3207_);
lean_dec_ref(v___x_3206_);
v___x_3208_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3209_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_3002_, v___x_3208_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v_a_3212_; uint8_t v___x_3213_; 
v___x_3210_ = lean_io_mono_nanos_now();
v___x_3211_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3005_, v_inheritedTraceOptions_3003_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_a_3212_);
lean_dec_ref(v___x_3211_);
v___x_3213_ = lean_unbox(v_a_3212_);
lean_dec(v_a_3212_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3214_ = lean_box(0);
v___x_3215_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2966_, v_rhs_2967_, v___x_3209_, v___f_3006_, v_cls_3005_, v_P_2965_, v___x_3214_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
v___y_3193_ = v___x_3210_;
v___y_3194_ = v_a_3207_;
v___y_3195_ = v___x_3215_;
goto v___jp_3192_;
}
else
{
lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3216_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_2967_);
lean_inc_ref(v_lhs_2966_);
lean_inc_ref(v_P_2965_);
v___x_3217_ = l_Lean_mkAppB(v_P_2965_, v_lhs_2966_, v_rhs_2967_);
v___x_3218_ = l_Lean_indentExpr(v___x_3217_);
v___x_3219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3216_);
lean_ctor_set(v___x_3219_, 1, v___x_3218_);
v___x_3220_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3005_, v___x_3219_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; lean_object* v___x_3222_; 
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3221_);
lean_dec_ref_known(v___x_3220_, 1);
v___x_3222_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2966_, v_rhs_2967_, v___x_3209_, v___f_3006_, v_cls_3005_, v_P_2965_, v_a_3221_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
v___y_3193_ = v___x_3210_;
v___y_3194_ = v_a_3207_;
v___y_3195_ = v___x_3222_;
goto v___jp_3192_;
}
else
{
lean_object* v_a_3223_; 
lean_dec_ref(v_rhs_2967_);
lean_dec_ref(v_lhs_2966_);
lean_dec_ref(v_P_2965_);
v_a_3223_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3223_);
lean_dec_ref_known(v___x_3220_, 1);
v___y_3188_ = v___x_3210_;
v___y_3189_ = v_a_3207_;
v_a_3190_ = v_a_3223_;
goto v___jp_3187_;
}
}
}
else
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v_a_3226_; uint8_t v___x_3227_; 
v___x_3224_ = lean_io_get_num_heartbeats();
v___x_3225_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3005_, v_inheritedTraceOptions_3003_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_a_3226_);
lean_dec_ref(v___x_3225_);
v___x_3227_ = lean_unbox(v_a_3226_);
lean_dec(v_a_3226_);
if (v___x_3227_ == 0)
{
lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3228_ = lean_box(0);
v___x_3229_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2966_, v_rhs_2967_, v_P_2965_, v_cls_3005_, v___x_3209_, v___f_3006_, v___x_3138_, v___x_3228_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
v___y_3160_ = v___x_3224_;
v___y_3161_ = v_a_3207_;
v___y_3162_ = v___x_3229_;
goto v___jp_3159_;
}
else
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3230_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_2967_);
lean_inc_ref(v_lhs_2966_);
lean_inc_ref(v_P_2965_);
v___x_3231_ = l_Lean_mkAppB(v_P_2965_, v_lhs_2966_, v_rhs_2967_);
v___x_3232_ = l_Lean_indentExpr(v___x_3231_);
v___x_3233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3230_);
lean_ctor_set(v___x_3233_, 1, v___x_3232_);
v___x_3234_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3005_, v___x_3233_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___x_3236_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_a_3235_);
lean_dec_ref_known(v___x_3234_, 1);
v___x_3236_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2966_, v_rhs_2967_, v_P_2965_, v_cls_3005_, v___x_3209_, v___f_3006_, v___x_3138_, v_a_3235_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
v___y_3160_ = v___x_3224_;
v___y_3161_ = v_a_3207_;
v___y_3162_ = v___x_3236_;
goto v___jp_3159_;
}
else
{
lean_object* v_a_3237_; 
lean_dec_ref(v_rhs_2967_);
lean_dec_ref(v_lhs_2966_);
lean_dec_ref(v_P_2965_);
v_a_3237_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_a_3237_);
lean_dec_ref_known(v___x_3234_, 1);
v___y_3155_ = v___x_3224_;
v___y_3156_ = v_a_3207_;
v_a_3157_ = v_a_3237_;
goto v___jp_3154_;
}
}
}
}
}
v___jp_2978_:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2980_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2980_, 0, v___y_2979_);
lean_ctor_set_uint8(v___x_2980_, 1, v___y_2979_);
v___x_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
return v___x_2981_;
}
v___jp_2982_:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2983_);
return v___x_2984_;
}
v___jp_2985_:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
return v___x_2987_;
}
v___jp_2988_:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2997_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7);
v___x_2998_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8));
v___x_2999_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2999_, 0, v___y_2990_);
lean_ctor_set(v___x_2999_, 1, v___x_2997_);
lean_ctor_set(v___x_2999_, 2, v___x_2998_);
v___x_3000_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___y_2989_, v___x_2999_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
return v___x_3000_;
}
v___jp_3007_:
{
lean_object* v___x_3017_; 
lean_inc_ref(v_lhs_2966_);
v___x_3017_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2966_);
if (lean_obj_tag(v___x_3017_) == 1)
{
lean_object* v_val_3018_; lean_object* v___x_3019_; 
v_val_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_val_3018_);
lean_dec_ref_known(v___x_3017_, 1);
lean_inc_ref(v_rhs_2967_);
v___x_3019_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2967_);
if (lean_obj_tag(v___x_3019_) == 1)
{
lean_object* v_val_3020_; uint8_t v___x_3021_; 
v_val_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_val_3020_);
lean_dec_ref_known(v___x_3019_, 1);
v___x_3021_ = lean_expr_eqv(v_val_3018_, v_val_3020_);
if (v___x_3021_ == 0)
{
lean_object* v_toCold_3022_; lean_object* v_inheritedTraceOptions_3023_; lean_object* v___x_3024_; lean_object* v_a_3025_; uint8_t v___x_3026_; 
lean_dec_ref(v_P_2965_);
v_toCold_3022_ = lean_ctor_get(v___y_3015_, 0);
v_inheritedTraceOptions_3023_ = lean_ctor_get(v_toCold_3022_, 11);
v___x_3024_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3005_, v_inheritedTraceOptions_3023_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref(v___x_3024_);
v___x_3026_ = lean_unbox(v_a_3025_);
lean_dec(v_a_3025_);
if (v___x_3026_ == 0)
{
lean_dec(v_val_3020_);
lean_dec(v_val_3018_);
lean_dec_ref(v_rhs_2967_);
lean_dec_ref(v_lhs_2966_);
v___y_2979_ = v___x_3021_;
goto v___jp_2978_;
}
else
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3027_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1);
v___x_3028_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3018_);
v___x_3029_ = l_Lean_MessageData_ofExpr(v___x_3028_);
v___x_3030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3027_);
lean_ctor_set(v___x_3030_, 1, v___x_3029_);
v___x_3031_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3);
v___x_3032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3030_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = l_Lean_indentExpr(v_lhs_2966_);
v___x_3034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3032_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
v___x_3035_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5);
v___x_3036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3034_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
v___x_3037_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3020_);
v___x_3038_ = l_Lean_MessageData_ofExpr(v___x_3037_);
v___x_3039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3036_);
lean_ctor_set(v___x_3039_, 1, v___x_3038_);
v___x_3040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
lean_ctor_set(v___x_3040_, 1, v___x_3031_);
v___x_3041_ = l_Lean_indentExpr(v_rhs_2967_);
v___x_3042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3040_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
v___x_3043_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3005_, v___x_3042_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_dec_ref_known(v___x_3043_, 1);
v___y_2979_ = v___x_3021_;
goto v___jp_2978_;
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3043_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3043_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
}
else
{
lean_object* v_toCold_3052_; lean_object* v_options_3053_; lean_object* v_inheritedTraceOptions_3054_; uint8_t v_hasTrace_3055_; uint8_t v___x_3056_; lean_object* v___x_3057_; lean_object* v___f_3058_; 
lean_dec(v_val_3020_);
v_toCold_3052_ = lean_ctor_get(v___y_3015_, 0);
v_options_3053_ = lean_ctor_get(v_toCold_3052_, 2);
v_inheritedTraceOptions_3054_ = lean_ctor_get(v_toCold_3052_, 11);
v_hasTrace_3055_ = lean_ctor_get_uint8(v_options_3053_, sizeof(void*)*1);
v___x_3056_ = 0;
v___x_3057_ = lean_box(v___x_3056_);
lean_inc(v_val_3018_);
v___f_3058_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 13, 5);
lean_closure_set(v___f_3058_, 0, v_val_3018_);
lean_closure_set(v___f_3058_, 1, v_lhs_2966_);
lean_closure_set(v___f_3058_, 2, v_rhs_2967_);
lean_closure_set(v___f_3058_, 3, v_P_2965_);
lean_closure_set(v___f_3058_, 4, v___x_3057_);
if (v_hasTrace_3055_ == 0)
{
v___y_2989_ = v___f_3058_;
v___y_2990_ = v_val_3018_;
v___y_2991_ = v___y_3011_;
v___y_2992_ = v___y_3012_;
v___y_2993_ = v___y_3013_;
v___y_2994_ = v___y_3014_;
v___y_2995_ = v___y_3015_;
v___y_2996_ = v___y_3016_;
goto v___jp_2988_;
}
else
{
lean_object* v___x_3059_; uint8_t v___x_3060_; 
v___x_3059_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3060_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3054_, v_options_3053_, v___x_3059_);
if (v___x_3060_ == 0)
{
v___y_2989_ = v___f_3058_;
v___y_2990_ = v_val_3018_;
v___y_2991_ = v___y_3011_;
v___y_2992_ = v___y_3012_;
v___y_2993_ = v___y_3013_;
v___y_2994_ = v___y_3014_;
v___y_2995_ = v___y_3015_;
v___y_2996_ = v___y_3016_;
goto v___jp_2988_;
}
else
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3061_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10);
lean_inc(v_val_3018_);
v___x_3062_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3018_);
v___x_3063_ = l_Lean_MessageData_ofExpr(v___x_3062_);
v___x_3064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3061_);
lean_ctor_set(v___x_3064_, 1, v___x_3063_);
v___x_3065_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12);
v___x_3066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3064_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v___x_3067_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3005_, v___x_3066_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_dec_ref_known(v___x_3067_, 1);
v___y_2989_ = v___f_3058_;
v___y_2990_ = v_val_3018_;
v___y_2991_ = v___y_3011_;
v___y_2992_ = v___y_3012_;
v___y_2993_ = v___y_3013_;
v___y_2994_ = v___y_3014_;
v___y_2995_ = v___y_3015_;
v___y_2996_ = v___y_3016_;
goto v___jp_2988_;
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec_ref(v___f_3058_);
lean_dec(v_val_3018_);
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3067_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3067_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_3076_; lean_object* v_inheritedTraceOptions_3077_; lean_object* v___x_3078_; lean_object* v_a_3079_; uint8_t v___x_3080_; 
lean_dec(v___x_3019_);
lean_dec(v_val_3018_);
lean_dec_ref(v_lhs_2966_);
lean_dec_ref(v_P_2965_);
v_toCold_3076_ = lean_ctor_get(v___y_3015_, 0);
v_inheritedTraceOptions_3077_ = lean_ctor_get(v_toCold_3076_, 11);
v___x_3078_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3005_, v_inheritedTraceOptions_3077_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_a_3079_);
lean_dec_ref(v___x_3078_);
v___x_3080_ = lean_unbox(v_a_3079_);
lean_dec(v_a_3079_);
if (v___x_3080_ == 0)
{
lean_dec_ref(v_rhs_2967_);
goto v___jp_2985_;
}
else
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3081_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_3082_ = l_Lean_indentExpr(v_rhs_2967_);
v___x_3083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3081_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
v___x_3084_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3005_, v___x_3083_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_dec_ref_known(v___x_3084_, 1);
goto v___jp_2985_;
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3093_; lean_object* v_inheritedTraceOptions_3094_; lean_object* v___x_3095_; lean_object* v_a_3096_; uint8_t v___x_3097_; 
lean_dec(v___x_3017_);
lean_dec_ref(v_rhs_2967_);
lean_dec_ref(v_P_2965_);
v_toCold_3093_ = lean_ctor_get(v___y_3015_, 0);
v_inheritedTraceOptions_3094_ = lean_ctor_get(v_toCold_3093_, 11);
v___x_3095_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3005_, v_inheritedTraceOptions_3094_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3096_);
lean_dec_ref(v___x_3095_);
v___x_3097_ = lean_unbox(v_a_3096_);
lean_dec(v_a_3096_);
if (v___x_3097_ == 0)
{
lean_dec_ref(v_lhs_2966_);
goto v___jp_2982_;
}
else
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3098_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_3099_ = l_Lean_indentExpr(v_lhs_2966_);
v___x_3100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3098_);
lean_ctor_set(v___x_3100_, 1, v___x_3099_);
v___x_3101_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3005_, v___x_3100_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_dec_ref_known(v___x_3101_, 1);
goto v___jp_2982_;
}
else
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_3101_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3101_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3105_ == 0)
{
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
}
}
v___jp_3110_:
{
if (v_____do__lift_3111_ == 0)
{
v___y_3008_ = v___y_3112_;
v___y_3009_ = v___y_3113_;
v___y_3010_ = v___y_3114_;
v___y_3011_ = v___y_3115_;
v___y_3012_ = v___y_3116_;
v___y_3013_ = v___y_3117_;
v___y_3014_ = v___y_3118_;
v___y_3015_ = v___y_3119_;
v___y_3016_ = v___y_3120_;
goto v___jp_3007_;
}
else
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3121_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_2967_);
lean_inc_ref(v_lhs_2966_);
lean_inc_ref(v_P_2965_);
v___x_3122_ = l_Lean_mkAppB(v_P_2965_, v_lhs_2966_, v_rhs_2967_);
v___x_3123_ = l_Lean_indentExpr(v___x_3122_);
v___x_3124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3121_);
lean_ctor_set(v___x_3124_, 1, v___x_3123_);
v___x_3125_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3005_, v___x_3124_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_dec_ref_known(v___x_3125_, 1);
v___y_3008_ = v___y_3112_;
v___y_3009_ = v___y_3113_;
v___y_3010_ = v___y_3114_;
v___y_3011_ = v___y_3115_;
v___y_3012_ = v___y_3116_;
v___y_3013_ = v___y_3117_;
v___y_3014_ = v___y_3118_;
v___y_3015_ = v___y_3119_;
v___y_3016_ = v___y_3120_;
goto v___jp_3007_;
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec_ref(v_rhs_2967_);
lean_dec_ref(v_lhs_2966_);
lean_dec_ref(v_P_2965_);
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3125_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3125_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___boxed(lean_object* v_P_3243_, lean_object* v_lhs_3244_, lean_object* v_rhs_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v_P_3243_, v_lhs_3244_, v_rhs_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_);
lean_dec(v_a_3254_);
lean_dec_ref(v_a_3253_);
lean_dec(v_a_3252_);
lean_dec_ref(v_a_3251_);
lean_dec(v_a_3250_);
lean_dec_ref(v_a_3249_);
lean_dec(v_a_3248_);
lean_dec_ref(v_a_3247_);
lean_dec(v_a_3246_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(lean_object* v_cls_3257_, lean_object* v_msg_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
lean_object* v___x_3269_; 
v___x_3269_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3257_, v_msg_3258_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object* v_cls_3270_, lean_object* v_msg_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(v_cls_3270_, v_msg_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(lean_object* v_00_u03b1_3283_, lean_object* v_x_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_3284_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___boxed(lean_object* v_00_u03b1_3296_, lean_object* v_x_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(v_00_u03b1_3296_, v_x_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(lean_object* v_oldTraces_3309_, lean_object* v_data_3310_, lean_object* v_ref_3311_, lean_object* v_msg_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v___x_3323_; 
v___x_3323_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_3309_, v_data_3310_, v_ref_3311_, v_msg_3312_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___boxed(lean_object* v_oldTraces_3324_, lean_object* v_data_3325_, lean_object* v_ref_3326_, lean_object* v_msg_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(v_oldTraces_3324_, v_data_3325_, v_ref_3326_, v_msg_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec(v___y_3328_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(lean_object* v_x_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3350_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_3351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0___boxed(lean_object* v_x_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_){
_start:
{
lean_object* v_res_3363_; 
v_res_3363_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v_x_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec(v___y_3353_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(lean_object* v_arg_3369_, lean_object* v_arg_3370_, lean_object* v_arg_3371_, lean_object* v_arg_3372_, lean_object* v_____r_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v___x_3384_; 
lean_inc_ref(v_arg_3369_);
v___x_3384_ = l_Lean_Meta_getDecLevel(v_arg_3369_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3384_, 1);
v___x_3386_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2));
v___x_3387_ = lean_box(0);
v___x_3388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3388_, 0, v_a_3385_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
v___x_3389_ = l_Lean_Expr_const___override(v___x_3386_, v___x_3388_);
v___x_3390_ = l_Lean_mkAppB(v___x_3389_, v_arg_3369_, v_arg_3370_);
v___x_3391_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3390_, v_arg_3371_, v_arg_3372_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
return v___x_3391_;
}
else
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
lean_dec_ref(v_arg_3372_);
lean_dec_ref(v_arg_3371_);
lean_dec_ref(v_arg_3370_);
lean_dec_ref(v_arg_3369_);
v_a_3392_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3394_ = v___x_3384_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3384_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___boxed(lean_object* v_arg_3400_, lean_object* v_arg_3401_, lean_object* v_arg_3402_, lean_object* v_arg_3403_, lean_object* v_____r_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
lean_object* v_res_3415_; 
v_res_3415_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3400_, v_arg_3401_, v_arg_3402_, v_arg_3403_, v_____r_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(lean_object* v_arg_3419_, lean_object* v_arg_3420_, lean_object* v_arg_3421_, lean_object* v_____r_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v___x_3433_; 
lean_inc_ref(v_arg_3419_);
v___x_3433_ = l_Lean_Meta_getLevel(v_arg_3419_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3434_);
lean_dec_ref_known(v___x_3433_, 1);
v___x_3435_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1));
v___x_3436_ = lean_box(0);
v___x_3437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3437_, 0, v_a_3434_);
lean_ctor_set(v___x_3437_, 1, v___x_3436_);
v___x_3438_ = l_Lean_Expr_const___override(v___x_3435_, v___x_3437_);
v___x_3439_ = l_Lean_Expr_app___override(v___x_3438_, v_arg_3419_);
v___x_3440_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3439_, v_arg_3420_, v_arg_3421_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
return v___x_3440_;
}
else
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3448_; 
lean_dec_ref(v_arg_3421_);
lean_dec_ref(v_arg_3420_);
lean_dec_ref(v_arg_3419_);
v_a_3441_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3443_ = v___x_3433_;
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3433_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3446_; 
if (v_isShared_3444_ == 0)
{
v___x_3446_ = v___x_3443_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_a_3441_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___boxed(lean_object* v_arg_3449_, lean_object* v_arg_3450_, lean_object* v_arg_3451_, lean_object* v_____r_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3449_, v_arg_3450_, v_arg_3451_, v_____r_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3453_);
return v_res_3463_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1(void){
_start:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3465_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0));
v___x_3466_ = l_Lean_stringToMessageData(v___x_3465_);
return v___x_3466_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2(void){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3467_ = l_Lean_checkEmoji;
v___x_3468_ = l_Lean_stringToMessageData(v___x_3467_);
return v___x_3468_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3(void){
_start:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3469_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2);
v___x_3470_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1);
v___x_3471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
lean_ctor_set(v___x_3471_, 1, v___x_3469_);
return v___x_3471_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5(void){
_start:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3473_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4));
v___x_3474_ = l_Lean_stringToMessageData(v___x_3473_);
return v___x_3474_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6(void){
_start:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3475_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5);
v___x_3476_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3);
v___x_3477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
lean_ctor_set(v___x_3477_, 1, v___x_3475_);
return v___x_3477_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8(void){
_start:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3479_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7));
v___x_3480_ = l_Lean_stringToMessageData(v___x_3479_);
return v___x_3480_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9(void){
_start:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3481_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8);
v___x_3482_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3);
v___x_3483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
lean_ctor_set(v___x_3483_, 1, v___x_3481_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(lean_object* v_e_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_){
_start:
{
lean_object* v___y_3496_; lean_object* v___x_3528_; 
v___x_3528_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3484_, v_a_3491_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3530_; uint8_t v___x_3531_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3529_);
lean_dec_ref_known(v___x_3528_, 1);
v___x_3530_ = l_Lean_Expr_cleanupAnnotations(v_a_3529_);
v___x_3531_ = l_Lean_Expr_isApp(v___x_3530_);
if (v___x_3531_ == 0)
{
lean_object* v___x_3532_; lean_object* v___x_3533_; 
lean_dec_ref(v___x_3530_);
v___x_3532_ = lean_box(0);
v___x_3533_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3532_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
v___y_3496_ = v___x_3533_;
goto v___jp_3495_;
}
else
{
lean_object* v_arg_3534_; lean_object* v___x_3535_; uint8_t v___x_3536_; 
v_arg_3534_ = lean_ctor_get(v___x_3530_, 1);
lean_inc_ref(v_arg_3534_);
v___x_3535_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3530_);
v___x_3536_ = l_Lean_Expr_isApp(v___x_3535_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
lean_dec_ref(v___x_3535_);
lean_dec_ref(v_arg_3534_);
v___x_3537_ = lean_box(0);
v___x_3538_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3537_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
v___y_3496_ = v___x_3538_;
goto v___jp_3495_;
}
else
{
lean_object* v_arg_3539_; lean_object* v___x_3540_; uint8_t v___x_3541_; 
v_arg_3539_ = lean_ctor_get(v___x_3535_, 1);
lean_inc_ref(v_arg_3539_);
v___x_3540_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3535_);
v___x_3541_ = l_Lean_Expr_isApp(v___x_3540_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
lean_dec_ref(v___x_3540_);
lean_dec_ref(v_arg_3539_);
lean_dec_ref(v_arg_3534_);
v___x_3542_ = lean_box(0);
v___x_3543_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3542_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
v___y_3496_ = v___x_3543_;
goto v___jp_3495_;
}
else
{
lean_object* v_arg_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; uint8_t v___x_3547_; 
v_arg_3544_ = lean_ctor_get(v___x_3540_, 1);
lean_inc_ref(v_arg_3544_);
v___x_3545_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3540_);
v___x_3546_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1));
v___x_3547_ = l_Lean_Expr_isConstOf(v___x_3545_, v___x_3546_);
if (v___x_3547_ == 0)
{
uint8_t v___x_3548_; 
v___x_3548_ = l_Lean_Expr_isApp(v___x_3545_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
lean_dec_ref(v___x_3545_);
lean_dec_ref(v_arg_3544_);
lean_dec_ref(v_arg_3539_);
lean_dec_ref(v_arg_3534_);
v___x_3549_ = lean_box(0);
v___x_3550_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3549_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
v___y_3496_ = v___x_3550_;
goto v___jp_3495_;
}
else
{
lean_object* v_arg_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; 
v_arg_3551_ = lean_ctor_get(v___x_3545_, 1);
lean_inc_ref(v_arg_3551_);
v___x_3552_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3545_);
v___x_3553_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2));
v___x_3554_ = l_Lean_Expr_isConstOf(v___x_3552_, v___x_3553_);
lean_dec_ref(v___x_3552_);
if (v___x_3554_ == 0)
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
lean_dec_ref(v_arg_3551_);
lean_dec_ref(v_arg_3544_);
lean_dec_ref(v_arg_3539_);
lean_dec_ref(v_arg_3534_);
v___x_3555_ = lean_box(0);
v___x_3556_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3555_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
v___y_3496_ = v___x_3556_;
goto v___jp_3495_;
}
else
{
lean_object* v_toCold_3557_; lean_object* v_options_3558_; lean_object* v_inheritedTraceOptions_3559_; uint8_t v_hasTrace_3560_; 
v_toCold_3557_ = lean_ctor_get(v_a_3492_, 0);
v_options_3558_ = lean_ctor_get(v_toCold_3557_, 2);
v_inheritedTraceOptions_3559_ = lean_ctor_get(v_toCold_3557_, 11);
v_hasTrace_3560_ = lean_ctor_get_uint8(v_options_3558_, sizeof(void*)*1);
if (v_hasTrace_3560_ == 0)
{
goto v___jp_3561_;
}
else
{
lean_object* v___x_3564_; lean_object* v___x_3565_; uint8_t v___x_3566_; 
v___x_3564_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3565_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3566_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3559_, v_options_3558_, v___x_3565_);
if (v___x_3566_ == 0)
{
goto v___jp_3561_;
}
else
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3567_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6);
v___x_3568_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3564_, v___x_3567_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3570_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc(v_a_3569_);
lean_dec_ref_known(v___x_3568_, 1);
v___x_3570_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3551_, v_arg_3544_, v_arg_3539_, v_arg_3534_, v_a_3569_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
v___y_3496_ = v___x_3570_;
goto v___jp_3495_;
}
else
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3578_; 
lean_dec_ref(v_arg_3551_);
lean_dec_ref(v_arg_3544_);
lean_dec_ref(v_arg_3539_);
lean_dec_ref(v_arg_3534_);
v_a_3571_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3573_ = v___x_3568_;
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3568_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3574_ == 0)
{
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3571_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
}
v___jp_3561_:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3562_ = lean_box(0);
v___x_3563_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3551_, v_arg_3544_, v_arg_3539_, v_arg_3534_, v___x_3562_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
v___y_3496_ = v___x_3563_;
goto v___jp_3495_;
}
}
}
}
else
{
lean_object* v_toCold_3579_; lean_object* v_options_3580_; lean_object* v_inheritedTraceOptions_3581_; uint8_t v_hasTrace_3582_; 
lean_dec_ref(v___x_3545_);
v_toCold_3579_ = lean_ctor_get(v_a_3492_, 0);
v_options_3580_ = lean_ctor_get(v_toCold_3579_, 2);
v_inheritedTraceOptions_3581_ = lean_ctor_get(v_toCold_3579_, 11);
v_hasTrace_3582_ = lean_ctor_get_uint8(v_options_3580_, sizeof(void*)*1);
if (v_hasTrace_3582_ == 0)
{
goto v___jp_3583_;
}
else
{
lean_object* v___x_3586_; lean_object* v___x_3587_; uint8_t v___x_3588_; 
v___x_3586_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3587_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3588_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3581_, v_options_3580_, v___x_3587_);
if (v___x_3588_ == 0)
{
goto v___jp_3583_;
}
else
{
lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3589_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9);
v___x_3590_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3586_, v___x_3589_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v___x_3592_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_a_3591_);
lean_dec_ref_known(v___x_3590_, 1);
v___x_3592_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3544_, v_arg_3539_, v_arg_3534_, v_a_3591_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
v___y_3496_ = v___x_3592_;
goto v___jp_3495_;
}
else
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3600_; 
lean_dec_ref(v_arg_3544_);
lean_dec_ref(v_arg_3539_);
lean_dec_ref(v_arg_3534_);
v_a_3593_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3595_ = v___x_3590_;
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v___x_3590_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3598_; 
if (v_isShared_3596_ == 0)
{
v___x_3598_ = v___x_3595_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3593_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
}
}
v___jp_3583_:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3584_ = lean_box(0);
v___x_3585_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3544_, v_arg_3539_, v_arg_3534_, v___x_3584_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
v___y_3496_ = v___x_3585_;
goto v___jp_3495_;
}
}
}
}
}
}
else
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
v_a_3601_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3603_ = v___x_3528_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3528_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
v___jp_3495_:
{
if (lean_obj_tag(v___y_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3527_; 
v_a_3497_ = lean_ctor_get(v___y_3496_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___y_3496_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3499_ = v___y_3496_;
v_isShared_3500_ = v_isSharedCheck_3527_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___y_3496_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3527_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
if (lean_obj_tag(v_a_3497_) == 0)
{
uint8_t v_contextDependent_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3512_; 
v_contextDependent_3501_ = lean_ctor_get_uint8(v_a_3497_, 1);
v_isSharedCheck_3512_ = !lean_is_exclusive(v_a_3497_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3503_ = v_a_3497_;
v_isShared_3504_ = v_isSharedCheck_3512_;
goto v_resetjp_3502_;
}
else
{
lean_dec(v_a_3497_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3512_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
uint8_t v___x_3505_; lean_object* v___x_3507_; 
v___x_3505_ = 1;
if (v_isShared_3504_ == 0)
{
v___x_3507_ = v___x_3503_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_3511_, 1, v_contextDependent_3501_);
v___x_3507_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
lean_object* v___x_3509_; 
lean_ctor_set_uint8(v___x_3507_, 0, v___x_3505_);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v___x_3507_);
v___x_3509_ = v___x_3499_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3507_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
else
{
lean_object* v_e_x27_3513_; lean_object* v_proof_3514_; uint8_t v_contextDependent_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3526_; 
v_e_x27_3513_ = lean_ctor_get(v_a_3497_, 0);
v_proof_3514_ = lean_ctor_get(v_a_3497_, 1);
v_contextDependent_3515_ = lean_ctor_get_uint8(v_a_3497_, sizeof(void*)*2 + 1);
v_isSharedCheck_3526_ = !lean_is_exclusive(v_a_3497_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3517_ = v_a_3497_;
v_isShared_3518_ = v_isSharedCheck_3526_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_proof_3514_);
lean_inc(v_e_x27_3513_);
lean_dec(v_a_3497_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3526_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
uint8_t v___x_3519_; lean_object* v___x_3521_; 
v___x_3519_ = 1;
if (v_isShared_3518_ == 0)
{
v___x_3521_ = v___x_3517_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_e_x27_3513_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v_proof_3514_);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, sizeof(void*)*2 + 1, v_contextDependent_3515_);
v___x_3521_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
lean_object* v___x_3523_; 
lean_ctor_set_uint8(v___x_3521_, sizeof(void*)*2, v___x_3519_);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v___x_3521_);
v___x_3523_ = v___x_3499_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3521_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
}
}
else
{
return v___y_3496_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed(lean_object* v_e_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(v_e_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_);
lean_dec(v_a_3618_);
lean_dec_ref(v_a_3617_);
lean_dec(v_a_3616_);
lean_dec_ref(v_a_3615_);
lean_dec(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec(v_a_3612_);
lean_dec_ref(v_a_3611_);
lean_dec(v_a_3610_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(lean_object* v_x_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v___x_3634_; 
lean_inc(v___y_3628_);
lean_inc_ref(v___y_3627_);
lean_inc(v___y_3626_);
lean_inc_ref(v___y_3625_);
lean_inc(v___y_3624_);
lean_inc(v___y_3623_);
lean_inc_ref(v___y_3622_);
v___x_3634_ = lean_apply_12(v_x_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, lean_box(0));
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed(lean_object* v_x_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(v_x_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object* v_mvarId_3649_, lean_object* v_x_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
lean_object* v___f_3663_; lean_object* v___x_3664_; 
lean_inc(v___y_3657_);
lean_inc_ref(v___y_3656_);
lean_inc(v___y_3655_);
lean_inc_ref(v___y_3654_);
lean_inc(v___y_3653_);
lean_inc(v___y_3652_);
lean_inc_ref(v___y_3651_);
v___f_3663_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_3663_, 0, v_x_3650_);
lean_closure_set(v___f_3663_, 1, v___y_3651_);
lean_closure_set(v___f_3663_, 2, v___y_3652_);
lean_closure_set(v___f_3663_, 3, v___y_3653_);
lean_closure_set(v___f_3663_, 4, v___y_3654_);
lean_closure_set(v___f_3663_, 5, v___y_3655_);
lean_closure_set(v___f_3663_, 6, v___y_3656_);
lean_closure_set(v___f_3663_, 7, v___y_3657_);
v___x_3664_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3649_, v___f_3663_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
if (lean_obj_tag(v___x_3664_) == 0)
{
return v___x_3664_;
}
else
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___x_3664_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3664_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object* v_mvarId_3673_, lean_object* v_x_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_mvarId_3673_, v_x_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec(v___y_3677_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(lean_object* v_00_u03b1_3688_, lean_object* v_mvarId_3689_, lean_object* v_x_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
lean_object* v___x_3703_; 
v___x_3703_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_mvarId_3689_, v_x_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object* v_00_u03b1_3704_, lean_object* v_mvarId_3705_, lean_object* v_x_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(v_00_u03b1_3704_, v_mvarId_3705_, v_x_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0(lean_object* v_x_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3731_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3731_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0___boxed(lean_object* v_x_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0(v_x_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
lean_dec(v___y_3734_);
lean_dec_ref(v_x_3733_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(lean_object* v_snd_3745_, lean_object* v_a_3746_, lean_object* v___x_3747_, lean_object* v_____r_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3761_ = lean_array_push(v_snd_3745_, v_a_3746_);
v___x_3762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3747_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3762_);
v___x_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3763_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1___boxed(lean_object* v_snd_3765_, lean_object* v_a_3766_, lean_object* v___x_3767_, lean_object* v_____r_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v_res_3781_; 
v_res_3781_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(v_snd_3765_, v_a_3766_, v___x_3767_, v_____r_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec(v___y_3777_);
lean_dec_ref(v___y_3776_);
lean_dec(v___y_3775_);
lean_dec_ref(v___y_3774_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
lean_dec(v___y_3771_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
return v_res_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object* v_cls_3782_, lean_object* v_msg_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v_ref_3789_; lean_object* v___x_3790_; lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3835_; 
v_ref_3789_ = lean_ctor_get(v___y_3786_, 2);
v___x_3790_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3793_ = v___x_3790_;
v_isShared_3794_ = v_isSharedCheck_3835_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3790_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3835_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3795_; lean_object* v_traceState_3796_; lean_object* v_env_3797_; lean_object* v_nextMacroScope_3798_; lean_object* v_ngen_3799_; lean_object* v_auxDeclNGen_3800_; lean_object* v_cache_3801_; lean_object* v_messages_3802_; lean_object* v_infoState_3803_; lean_object* v_snapshotTasks_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3834_; 
v___x_3795_ = lean_st_ref_take(v___y_3787_);
v_traceState_3796_ = lean_ctor_get(v___x_3795_, 4);
v_env_3797_ = lean_ctor_get(v___x_3795_, 0);
v_nextMacroScope_3798_ = lean_ctor_get(v___x_3795_, 1);
v_ngen_3799_ = lean_ctor_get(v___x_3795_, 2);
v_auxDeclNGen_3800_ = lean_ctor_get(v___x_3795_, 3);
v_cache_3801_ = lean_ctor_get(v___x_3795_, 5);
v_messages_3802_ = lean_ctor_get(v___x_3795_, 6);
v_infoState_3803_ = lean_ctor_get(v___x_3795_, 7);
v_snapshotTasks_3804_ = lean_ctor_get(v___x_3795_, 8);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3806_ = v___x_3795_;
v_isShared_3807_ = v_isSharedCheck_3834_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_snapshotTasks_3804_);
lean_inc(v_infoState_3803_);
lean_inc(v_messages_3802_);
lean_inc(v_cache_3801_);
lean_inc(v_traceState_3796_);
lean_inc(v_auxDeclNGen_3800_);
lean_inc(v_ngen_3799_);
lean_inc(v_nextMacroScope_3798_);
lean_inc(v_env_3797_);
lean_dec(v___x_3795_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3834_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
uint64_t v_tid_3808_; lean_object* v_traces_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3833_; 
v_tid_3808_ = lean_ctor_get_uint64(v_traceState_3796_, sizeof(void*)*1);
v_traces_3809_ = lean_ctor_get(v_traceState_3796_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v_traceState_3796_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3811_ = v_traceState_3796_;
v_isShared_3812_ = v_isSharedCheck_3833_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_traces_3809_);
lean_dec(v_traceState_3796_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3833_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3813_; double v___x_3814_; uint8_t v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3823_; 
v___x_3813_ = lean_box(0);
v___x_3814_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_3815_ = 0;
v___x_3816_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_3817_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3817_, 0, v_cls_3782_);
lean_ctor_set(v___x_3817_, 1, v___x_3813_);
lean_ctor_set(v___x_3817_, 2, v___x_3816_);
lean_ctor_set_float(v___x_3817_, sizeof(void*)*3, v___x_3814_);
lean_ctor_set_float(v___x_3817_, sizeof(void*)*3 + 8, v___x_3814_);
lean_ctor_set_uint8(v___x_3817_, sizeof(void*)*3 + 16, v___x_3815_);
v___x_3818_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_3819_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3817_);
lean_ctor_set(v___x_3819_, 1, v_a_3791_);
lean_ctor_set(v___x_3819_, 2, v___x_3818_);
lean_inc(v_ref_3789_);
v___x_3820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3820_, 0, v_ref_3789_);
lean_ctor_set(v___x_3820_, 1, v___x_3819_);
v___x_3821_ = l_Lean_PersistentArray_push___redArg(v_traces_3809_, v___x_3820_);
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 0, v___x_3821_);
v___x_3823_ = v___x_3811_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3821_);
lean_ctor_set_uint64(v_reuseFailAlloc_3832_, sizeof(void*)*1, v_tid_3808_);
v___x_3823_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
lean_object* v___x_3825_; 
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 4, v___x_3823_);
v___x_3825_ = v___x_3806_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_env_3797_);
lean_ctor_set(v_reuseFailAlloc_3831_, 1, v_nextMacroScope_3798_);
lean_ctor_set(v_reuseFailAlloc_3831_, 2, v_ngen_3799_);
lean_ctor_set(v_reuseFailAlloc_3831_, 3, v_auxDeclNGen_3800_);
lean_ctor_set(v_reuseFailAlloc_3831_, 4, v___x_3823_);
lean_ctor_set(v_reuseFailAlloc_3831_, 5, v_cache_3801_);
lean_ctor_set(v_reuseFailAlloc_3831_, 6, v_messages_3802_);
lean_ctor_set(v_reuseFailAlloc_3831_, 7, v_infoState_3803_);
lean_ctor_set(v_reuseFailAlloc_3831_, 8, v_snapshotTasks_3804_);
v___x_3825_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3829_; 
v___x_3826_ = lean_st_ref_put(v___y_3787_, v___x_3825_);
v___x_3827_ = lean_box(0);
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 0, v___x_3827_);
v___x_3829_ = v___x_3793_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3827_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object* v_cls_3836_, lean_object* v_msg_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_cls_3836_, v_msg_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(uint8_t v___x_3844_, lean_object* v___f_3845_, lean_object* v_____r_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v___x_3859_; lean_object* v_caches_3860_; lean_object* v_typeAnalysis_3861_; lean_object* v_target_3862_; lean_object* v_hypotheses_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3873_; 
v___x_3859_ = lean_st_ref_take(v___y_3848_);
v_caches_3860_ = lean_ctor_get(v___x_3859_, 0);
v_typeAnalysis_3861_ = lean_ctor_get(v___x_3859_, 1);
v_target_3862_ = lean_ctor_get(v___x_3859_, 2);
v_hypotheses_3863_ = lean_ctor_get(v___x_3859_, 3);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3865_ = v___x_3859_;
v_isShared_3866_ = v_isSharedCheck_3873_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_hypotheses_3863_);
lean_inc(v_target_3862_);
lean_inc(v_typeAnalysis_3861_);
lean_inc(v_caches_3860_);
lean_dec(v___x_3859_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3873_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_caches_3860_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v_typeAnalysis_3861_);
lean_ctor_set(v_reuseFailAlloc_3872_, 2, v_target_3862_);
lean_ctor_set(v_reuseFailAlloc_3872_, 3, v_hypotheses_3863_);
v___x_3868_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
lean_ctor_set_uint8(v___x_3868_, sizeof(void*)*4, v___x_3844_);
v___x_3869_ = lean_st_ref_put(v___y_3848_, v___x_3868_);
v___x_3870_ = lean_box(0);
lean_inc(v___y_3857_);
lean_inc_ref(v___y_3856_);
lean_inc(v___y_3855_);
lean_inc_ref(v___y_3854_);
lean_inc(v___y_3853_);
lean_inc_ref(v___y_3852_);
lean_inc(v___y_3851_);
lean_inc_ref(v___y_3850_);
lean_inc(v___y_3849_);
lean_inc(v___y_3848_);
lean_inc_ref(v___y_3847_);
v___x_3871_ = lean_apply_13(v___f_3845_, v___x_3870_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, lean_box(0));
return v___x_3871_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2___boxed(lean_object* v___x_3874_, lean_object* v___f_3875_, lean_object* v_____r_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_){
_start:
{
uint8_t v___x_10026__boxed_3889_; lean_object* v_res_3890_; 
v___x_10026__boxed_3889_ = lean_unbox(v___x_3874_);
v_res_3890_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_10026__boxed_3889_, v___f_3875_, v_____r_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
return v_res_3890_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3892_; lean_object* v___f_3893_; lean_object* v_methods_3894_; 
v___x_3892_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed), 11, 0);
v___f_3893_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__0));
v_methods_3894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_methods_3894_, 0, v___f_3893_);
lean_ctor_set(v_methods_3894_, 1, v___x_3892_);
return v_methods_3894_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3896_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__2));
v___x_3897_ = l_Lean_stringToMessageData(v___x_3896_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object* v_upperBound_3898_, lean_object* v___x_3899_, lean_object* v_config_3900_, lean_object* v_a_3901_, lean_object* v_b_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v___y_3916_; uint8_t v___x_3938_; 
v___x_3938_ = lean_nat_dec_lt(v_a_3901_, v_upperBound_3898_);
if (v___x_3938_ == 0)
{
lean_object* v___x_3939_; 
lean_dec(v_a_3901_);
lean_dec_ref(v_config_3900_);
v___x_3939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3939_, 0, v_b_3902_);
return v___x_3939_;
}
else
{
uint8_t v___x_3940_; lean_object* v_methods_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v___x_3940_ = 1;
v_methods_3941_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1);
v___x_3942_ = lean_array_fget_borrowed(v___x_3899_, v_a_3901_);
lean_inc(v___x_3942_);
lean_inc_ref(v_config_3900_);
v___x_3943_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v___x_3940_, v_methods_3941_, v_config_3900_, v___x_3942_, v___y_3904_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v_snd_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_4008_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref_known(v___x_3943_, 1);
v_snd_3945_ = lean_ctor_get(v_b_3902_, 1);
v_isSharedCheck_4008_ = !lean_is_exclusive(v_b_3902_);
if (v_isSharedCheck_4008_ == 0)
{
lean_object* v_unused_4009_; 
v_unused_4009_ = lean_ctor_get(v_b_3902_, 0);
lean_dec(v_unused_4009_);
v___x_3947_ = v_b_3902_;
v_isShared_3948_ = v_isSharedCheck_4008_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_snd_3945_);
lean_dec(v_b_3902_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_4008_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v_type_3949_; lean_object* v_value_3950_; uint8_t v___x_3951_; 
v_type_3949_ = lean_ctor_get(v_a_3944_, 1);
v_value_3950_ = lean_ctor_get(v_a_3944_, 2);
lean_inc_ref(v_type_3949_);
v___x_3951_ = l_Lean_Expr_isFalse(v_type_3949_);
if (v___x_3951_ == 0)
{
lean_object* v_type_3952_; lean_object* v___x_3953_; lean_object* v___f_3954_; uint8_t v___x_3983_; 
lean_del_object(v___x_3947_);
v_type_3952_ = lean_ctor_get(v___x_3942_, 1);
v___x_3953_ = lean_box(0);
lean_inc(v_a_3944_);
lean_inc(v_snd_3945_);
v___f_3954_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1___boxed), 16, 3);
lean_closure_set(v___f_3954_, 0, v_snd_3945_);
lean_closure_set(v___f_3954_, 1, v_a_3944_);
lean_closure_set(v___f_3954_, 2, v___x_3953_);
v___x_3983_ = lean_expr_eqv(v_type_3952_, v_type_3949_);
if (v___x_3983_ == 0)
{
lean_inc_ref(v_type_3949_);
lean_dec(v_snd_3945_);
lean_dec(v_a_3944_);
goto v___jp_3958_;
}
else
{
if (v___x_3951_ == 0)
{
lean_object* v___x_3984_; lean_object* v___x_3985_; 
lean_dec_ref(v___f_3954_);
v___x_3984_ = lean_box(0);
v___x_3985_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(v_snd_3945_, v_a_3944_, v___x_3953_, v___x_3984_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
v___y_3916_ = v___x_3985_;
goto v___jp_3915_;
}
else
{
lean_inc_ref(v_type_3949_);
lean_dec(v_snd_3945_);
lean_dec(v_a_3944_);
goto v___jp_3958_;
}
}
v___jp_3955_:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3956_ = lean_box(0);
v___x_3957_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_3938_, v___f_3954_, v___x_3956_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
v___y_3916_ = v___x_3957_;
goto v___jp_3915_;
}
v___jp_3958_:
{
lean_object* v_toCold_3959_; lean_object* v_options_3960_; uint8_t v_hasTrace_3961_; 
v_toCold_3959_ = lean_ctor_get(v___y_3912_, 0);
v_options_3960_ = lean_ctor_get(v_toCold_3959_, 2);
v_hasTrace_3961_ = lean_ctor_get_uint8(v_options_3960_, sizeof(void*)*1);
if (v_hasTrace_3961_ == 0)
{
lean_dec_ref(v_type_3949_);
goto v___jp_3955_;
}
else
{
lean_object* v_inheritedTraceOptions_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; uint8_t v___x_3965_; 
v_inheritedTraceOptions_3962_ = lean_ctor_get(v_toCold_3959_, 11);
v___x_3963_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3964_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3965_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3962_, v_options_3960_, v___x_3964_);
if (v___x_3965_ == 0)
{
lean_dec_ref(v_type_3949_);
goto v___jp_3955_;
}
else
{
lean_object* v_type_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v_type_3966_ = lean_ctor_get(v___x_3942_, 1);
lean_inc_ref(v_type_3966_);
v___x_3967_ = l_Lean_MessageData_ofExpr(v_type_3966_);
v___x_3968_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3);
v___x_3969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3967_);
lean_ctor_set(v___x_3969_, 1, v___x_3968_);
v___x_3970_ = l_Lean_MessageData_ofExpr(v_type_3949_);
v___x_3971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3969_);
lean_ctor_set(v___x_3971_, 1, v___x_3970_);
v___x_3972_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v___x_3963_, v___x_3971_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; lean_object* v___x_3974_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_a_3973_);
lean_dec_ref_known(v___x_3972_, 1);
v___x_3974_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_3938_, v___f_3954_, v_a_3973_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
v___y_3916_ = v___x_3974_;
goto v___jp_3915_;
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3982_; 
lean_dec_ref(v___f_3954_);
lean_dec(v_a_3901_);
lean_dec_ref(v_config_3900_);
v_a_3975_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3977_ = v___x_3972_;
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3972_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3980_; 
if (v_isShared_3978_ == 0)
{
v___x_3980_ = v___x_3977_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_a_3975_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3986_; 
lean_inc_ref(v_value_3950_);
lean_dec(v_a_3944_);
lean_dec(v_a_3901_);
lean_dec_ref(v_config_3900_);
v___x_3986_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_3950_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3998_; 
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_3998_ == 0)
{
lean_object* v_unused_3999_; 
v_unused_3999_ = lean_ctor_get(v___x_3986_, 0);
lean_dec(v_unused_3999_);
v___x_3988_ = v___x_3986_;
v_isShared_3989_ = v_isSharedCheck_3998_;
goto v_resetjp_3987_;
}
else
{
lean_dec(v___x_3986_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3998_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3993_; 
v___x_3990_ = lean_box(v___x_3938_);
v___x_3991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
if (v_isShared_3948_ == 0)
{
lean_ctor_set(v___x_3947_, 0, v___x_3991_);
v___x_3993_ = v___x_3947_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v___x_3991_);
lean_ctor_set(v_reuseFailAlloc_3997_, 1, v_snd_3945_);
v___x_3993_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
lean_object* v___x_3995_; 
if (v_isShared_3989_ == 0)
{
lean_ctor_set(v___x_3988_, 0, v___x_3993_);
v___x_3995_ = v___x_3988_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v___x_3993_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
else
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
lean_del_object(v___x_3947_);
lean_dec(v_snd_3945_);
v_a_4000_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4002_ = v___x_3986_;
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3986_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4005_; 
if (v_isShared_4003_ == 0)
{
v___x_4005_ = v___x_4002_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_4000_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
}
}
}
else
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
lean_dec_ref(v_b_3902_);
lean_dec(v_a_3901_);
lean_dec_ref(v_config_3900_);
v_a_4010_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_3943_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_3943_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4015_; 
if (v_isShared_4013_ == 0)
{
v___x_4015_ = v___x_4012_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
}
v___jp_3915_:
{
if (lean_obj_tag(v___y_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3929_; 
v_a_3917_ = lean_ctor_get(v___y_3916_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___y_3916_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3919_ = v___y_3916_;
v_isShared_3920_ = v_isSharedCheck_3929_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_dec(v___y_3916_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3929_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
if (lean_obj_tag(v_a_3917_) == 0)
{
lean_object* v_a_3921_; lean_object* v___x_3923_; 
lean_dec(v_a_3901_);
lean_dec_ref(v_config_3900_);
v_a_3921_ = lean_ctor_get(v_a_3917_, 0);
lean_inc(v_a_3921_);
lean_dec_ref_known(v_a_3917_, 1);
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 0, v_a_3921_);
v___x_3923_ = v___x_3919_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3921_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
lean_del_object(v___x_3919_);
v_a_3925_ = lean_ctor_get(v_a_3917_, 0);
lean_inc(v_a_3925_);
lean_dec_ref_known(v_a_3917_, 1);
v___x_3926_ = lean_unsigned_to_nat(1u);
v___x_3927_ = lean_nat_add(v_a_3901_, v___x_3926_);
lean_dec(v_a_3901_);
v_a_3901_ = v___x_3927_;
v_b_3902_ = v_a_3925_;
goto _start;
}
}
}
else
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3937_; 
lean_dec(v_a_3901_);
lean_dec_ref(v_config_3900_);
v_a_3930_ = lean_ctor_get(v___y_3916_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___y_3916_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3932_ = v___y_3916_;
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___y_3916_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3930_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_4018_ = _args[0];
lean_object* v___x_4019_ = _args[1];
lean_object* v_config_4020_ = _args[2];
lean_object* v_a_4021_ = _args[3];
lean_object* v_b_4022_ = _args[4];
lean_object* v___y_4023_ = _args[5];
lean_object* v___y_4024_ = _args[6];
lean_object* v___y_4025_ = _args[7];
lean_object* v___y_4026_ = _args[8];
lean_object* v___y_4027_ = _args[9];
lean_object* v___y_4028_ = _args[10];
lean_object* v___y_4029_ = _args[11];
lean_object* v___y_4030_ = _args[12];
lean_object* v___y_4031_ = _args[13];
lean_object* v___y_4032_ = _args[14];
lean_object* v___y_4033_ = _args[15];
lean_object* v___y_4034_ = _args[16];
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_upperBound_4018_, v___x_4019_, v_config_4020_, v_a_4021_, v_b_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec_ref(v___x_4019_);
lean_dec(v_upperBound_4018_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(lean_object* v_config_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_){
_start:
{
lean_object* v___x_4049_; lean_object* v_hypotheses_4050_; lean_object* v___x_4051_; lean_object* v_newHyps_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4049_ = lean_st_ref_get(v___y_4038_);
v_hypotheses_4050_ = lean_ctor_get(v___x_4049_, 3);
lean_inc_ref(v_hypotheses_4050_);
lean_dec(v___x_4049_);
v___x_4051_ = lean_array_get_size(v_hypotheses_4050_);
v_newHyps_4052_ = lean_mk_empty_array_with_capacity(v___x_4051_);
v___x_4053_ = lean_unsigned_to_nat(0u);
v___x_4054_ = lean_box(0);
v___x_4055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4054_);
lean_ctor_set(v___x_4055_, 1, v_newHyps_4052_);
v___x_4056_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v___x_4051_, v_hypotheses_4050_, v_config_4036_, v___x_4053_, v___x_4055_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
lean_dec_ref(v_hypotheses_4050_);
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4086_; 
v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4059_ = v___x_4056_;
v_isShared_4060_ = v_isSharedCheck_4086_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v___x_4056_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4086_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v_fst_4061_; 
v_fst_4061_ = lean_ctor_get(v_a_4057_, 0);
if (lean_obj_tag(v_fst_4061_) == 0)
{
lean_object* v_snd_4062_; lean_object* v___x_4063_; lean_object* v_caches_4064_; lean_object* v_typeAnalysis_4065_; lean_object* v_target_4066_; uint8_t v_didChange_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4080_; 
v_snd_4062_ = lean_ctor_get(v_a_4057_, 1);
lean_inc(v_snd_4062_);
lean_dec(v_a_4057_);
v___x_4063_ = lean_st_ref_take(v___y_4038_);
v_caches_4064_ = lean_ctor_get(v___x_4063_, 0);
v_typeAnalysis_4065_ = lean_ctor_get(v___x_4063_, 1);
v_target_4066_ = lean_ctor_get(v___x_4063_, 2);
v_didChange_4067_ = lean_ctor_get_uint8(v___x_4063_, sizeof(void*)*4);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4080_ == 0)
{
lean_object* v_unused_4081_; 
v_unused_4081_ = lean_ctor_get(v___x_4063_, 3);
lean_dec(v_unused_4081_);
v___x_4069_ = v___x_4063_;
v_isShared_4070_ = v_isSharedCheck_4080_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_target_4066_);
lean_inc(v_typeAnalysis_4065_);
lean_inc(v_caches_4064_);
lean_dec(v___x_4063_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4080_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
lean_ctor_set(v___x_4069_, 3, v_snd_4062_);
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_caches_4064_);
lean_ctor_set(v_reuseFailAlloc_4079_, 1, v_typeAnalysis_4065_);
lean_ctor_set(v_reuseFailAlloc_4079_, 2, v_target_4066_);
lean_ctor_set(v_reuseFailAlloc_4079_, 3, v_snd_4062_);
lean_ctor_set_uint8(v_reuseFailAlloc_4079_, sizeof(void*)*4, v_didChange_4067_);
v___x_4072_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
lean_object* v___x_4073_; uint8_t v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4077_; 
v___x_4073_ = lean_st_ref_put(v___y_4038_, v___x_4072_);
v___x_4074_ = 0;
v___x_4075_ = lean_box(v___x_4074_);
if (v_isShared_4060_ == 0)
{
lean_ctor_set(v___x_4059_, 0, v___x_4075_);
v___x_4077_ = v___x_4059_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v___x_4075_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
}
}
else
{
lean_object* v_val_4082_; lean_object* v___x_4084_; 
lean_inc_ref(v_fst_4061_);
lean_dec(v_a_4057_);
v_val_4082_ = lean_ctor_get(v_fst_4061_, 0);
lean_inc(v_val_4082_);
lean_dec_ref_known(v_fst_4061_, 1);
if (v_isShared_4060_ == 0)
{
lean_ctor_set(v___x_4059_, 0, v_val_4082_);
v___x_4084_ = v___x_4059_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_val_4082_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4094_; 
v_a_4087_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4089_ = v___x_4056_;
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4056_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_a_4087_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed(lean_object* v_config_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(v_config_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
return v_res_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v_config_4121_; lean_object* v___x_4122_; lean_object* v_maxSteps_4123_; lean_object* v_target_4124_; lean_object* v___x_4125_; lean_object* v_config_4126_; lean_object* v___f_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v_config_4121_ = lean_ctor_get(v___y_4109_, 0);
v___x_4122_ = lean_st_ref_get(v___y_4110_);
v_maxSteps_4123_ = lean_ctor_get(v_config_4121_, 1);
v_target_4124_ = lean_ctor_get(v___x_4122_, 2);
lean_inc_ref(v_target_4124_);
lean_dec(v___x_4122_);
v___x_4125_ = lean_unsigned_to_nat(2u);
lean_inc(v_maxSteps_4123_);
v_config_4126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_config_4126_, 0, v_maxSteps_4123_);
lean_ctor_set(v_config_4126_, 1, v___x_4125_);
v___f_4127_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed), 13, 1);
lean_closure_set(v___f_4127_, 0, v_config_4126_);
v___x_4128_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_4124_);
lean_dec_ref(v_target_4124_);
v___x_4129_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v___x_4128_, v___f_4127_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___boxed(lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec(v___y_4132_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
return v_res_4142_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(lean_object* v_cls_4151_, lean_object* v_msg_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v___x_4165_; 
v___x_4165_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_cls_4151_, v_msg_4152_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
return v___x_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___boxed(lean_object* v_cls_4166_, lean_object* v_msg_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(v_cls_4166_, v_msg_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec(v___y_4170_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(lean_object* v_upperBound_4181_, lean_object* v___x_4182_, lean_object* v_config_4183_, lean_object* v_inst_4184_, lean_object* v_R_4185_, lean_object* v_a_4186_, lean_object* v_b_4187_, lean_object* v_c_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v___x_4201_; 
v___x_4201_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_upperBound_4181_, v___x_4182_, v_config_4183_, v_a_4186_, v_b_4187_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_4202_ = _args[0];
lean_object* v___x_4203_ = _args[1];
lean_object* v_config_4204_ = _args[2];
lean_object* v_inst_4205_ = _args[3];
lean_object* v_R_4206_ = _args[4];
lean_object* v_a_4207_ = _args[5];
lean_object* v_b_4208_ = _args[6];
lean_object* v_c_4209_ = _args[7];
lean_object* v___y_4210_ = _args[8];
lean_object* v___y_4211_ = _args[9];
lean_object* v___y_4212_ = _args[10];
lean_object* v___y_4213_ = _args[11];
lean_object* v___y_4214_ = _args[12];
lean_object* v___y_4215_ = _args[13];
lean_object* v___y_4216_ = _args[14];
lean_object* v___y_4217_ = _args[15];
lean_object* v___y_4218_ = _args[16];
lean_object* v___y_4219_ = _args[17];
lean_object* v___y_4220_ = _args[18];
lean_object* v___y_4221_ = _args[19];
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(v_upperBound_4202_, v___x_4203_, v_config_4204_, v_inst_4205_, v_R_4206_, v_a_4207_, v_b_4208_, v_c_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec_ref(v___x_4203_);
lean_dec(v_upperBound_4202_);
return v_res_4222_;
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
