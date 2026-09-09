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
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v_nbuckets_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_294_ = lean_array_get_size(v_data_293_);
v___x_295_ = lean_unsigned_to_nat(2u);
v_nbuckets_296_ = lean_nat_mul(v___x_294_, v___x_295_);
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = lean_box(0);
v___x_299_ = lean_mk_array(v_nbuckets_296_, v___x_298_);
v___x_300_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(v___x_297_, v_data_293_, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(lean_object* v_m_301_, lean_object* v_a_302_, lean_object* v_b_303_){
_start:
{
lean_object* v_size_304_; lean_object* v_buckets_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_348_; 
v_size_304_ = lean_ctor_get(v_m_301_, 0);
v_buckets_305_ = lean_ctor_get(v_m_301_, 1);
v_isSharedCheck_348_ = !lean_is_exclusive(v_m_301_);
if (v_isSharedCheck_348_ == 0)
{
v___x_307_ = v_m_301_;
v_isShared_308_ = v_isSharedCheck_348_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_buckets_305_);
lean_inc(v_size_304_);
lean_dec(v_m_301_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_348_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; uint64_t v___x_310_; uint64_t v___x_311_; uint64_t v___x_312_; uint64_t v_fold_313_; uint64_t v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; size_t v___x_317_; size_t v___x_318_; size_t v___x_319_; size_t v___x_320_; size_t v___x_321_; lean_object* v_bkt_322_; uint8_t v___x_323_; 
v___x_309_ = lean_array_get_size(v_buckets_305_);
v___x_310_ = l_Lean_Expr_hash(v_a_302_);
v___x_311_ = 32ULL;
v___x_312_ = lean_uint64_shift_right(v___x_310_, v___x_311_);
v_fold_313_ = lean_uint64_xor(v___x_310_, v___x_312_);
v___x_314_ = 16ULL;
v___x_315_ = lean_uint64_shift_right(v_fold_313_, v___x_314_);
v___x_316_ = lean_uint64_xor(v_fold_313_, v___x_315_);
v___x_317_ = lean_uint64_to_usize(v___x_316_);
v___x_318_ = lean_usize_of_nat(v___x_309_);
v___x_319_ = ((size_t)1ULL);
v___x_320_ = lean_usize_sub(v___x_318_, v___x_319_);
v___x_321_ = lean_usize_land(v___x_317_, v___x_320_);
v_bkt_322_ = lean_array_uget_borrowed(v_buckets_305_, v___x_321_);
v___x_323_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_302_, v_bkt_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v_size_x27_325_; lean_object* v___x_326_; lean_object* v_buckets_x27_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_324_ = lean_unsigned_to_nat(1u);
v_size_x27_325_ = lean_nat_add(v_size_304_, v___x_324_);
lean_dec(v_size_304_);
lean_inc(v_bkt_322_);
v___x_326_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_326_, 0, v_a_302_);
lean_ctor_set(v___x_326_, 1, v_b_303_);
lean_ctor_set(v___x_326_, 2, v_bkt_322_);
v_buckets_x27_327_ = lean_array_uset(v_buckets_305_, v___x_321_, v___x_326_);
v___x_328_ = lean_unsigned_to_nat(4u);
v___x_329_ = lean_nat_mul(v_size_x27_325_, v___x_328_);
v___x_330_ = lean_unsigned_to_nat(3u);
v___x_331_ = lean_nat_div(v___x_329_, v___x_330_);
lean_dec(v___x_329_);
v___x_332_ = lean_array_get_size(v_buckets_x27_327_);
v___x_333_ = lean_nat_dec_le(v___x_331_, v___x_332_);
lean_dec(v___x_331_);
if (v___x_333_ == 0)
{
lean_object* v_val_334_; lean_object* v___x_336_; 
v_val_334_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(v_buckets_x27_327_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v_val_334_);
lean_ctor_set(v___x_307_, 0, v_size_x27_325_);
v___x_336_ = v___x_307_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_size_x27_325_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_val_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
else
{
lean_object* v___x_339_; 
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v_buckets_x27_327_);
lean_ctor_set(v___x_307_, 0, v_size_x27_325_);
v___x_339_ = v___x_307_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_size_x27_325_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_buckets_x27_327_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
else
{
lean_object* v___x_341_; lean_object* v_buckets_x27_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_346_; 
lean_inc(v_bkt_322_);
v___x_341_ = lean_box(0);
v_buckets_x27_342_ = lean_array_uset(v_buckets_305_, v___x_321_, v___x_341_);
v___x_343_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_302_, v_b_303_, v_bkt_322_);
v___x_344_ = lean_array_uset(v_buckets_x27_342_, v___x_321_, v___x_343_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___x_344_);
v___x_346_ = v___x_307_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_size_304_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(lean_object* v_a_349_, lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_350_) == 0)
{
lean_object* v___x_351_; 
v___x_351_ = lean_box(0);
return v___x_351_;
}
else
{
lean_object* v_key_352_; lean_object* v_value_353_; lean_object* v_tail_354_; uint8_t v___x_355_; 
v_key_352_ = lean_ctor_get(v_x_350_, 0);
v_value_353_ = lean_ctor_get(v_x_350_, 1);
v_tail_354_ = lean_ctor_get(v_x_350_, 2);
v___x_355_ = lean_expr_eqv(v_key_352_, v_a_349_);
if (v___x_355_ == 0)
{
v_x_350_ = v_tail_354_;
goto _start;
}
else
{
lean_object* v___x_357_; 
lean_inc(v_value_353_);
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v_value_353_);
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_358_, lean_object* v_x_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_358_, v_x_359_);
lean_dec(v_x_359_);
lean_dec_ref(v_a_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(lean_object* v_m_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_buckets_363_; lean_object* v___x_364_; uint64_t v___x_365_; uint64_t v___x_366_; uint64_t v___x_367_; uint64_t v_fold_368_; uint64_t v___x_369_; uint64_t v___x_370_; uint64_t v___x_371_; size_t v___x_372_; size_t v___x_373_; size_t v___x_374_; size_t v___x_375_; size_t v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_buckets_363_ = lean_ctor_get(v_m_361_, 1);
v___x_364_ = lean_array_get_size(v_buckets_363_);
v___x_365_ = l_Lean_Expr_hash(v_a_362_);
v___x_366_ = 32ULL;
v___x_367_ = lean_uint64_shift_right(v___x_365_, v___x_366_);
v_fold_368_ = lean_uint64_xor(v___x_365_, v___x_367_);
v___x_369_ = 16ULL;
v___x_370_ = lean_uint64_shift_right(v_fold_368_, v___x_369_);
v___x_371_ = lean_uint64_xor(v_fold_368_, v___x_370_);
v___x_372_ = lean_uint64_to_usize(v___x_371_);
v___x_373_ = lean_usize_of_nat(v___x_364_);
v___x_374_ = ((size_t)1ULL);
v___x_375_ = lean_usize_sub(v___x_373_, v___x_374_);
v___x_376_ = lean_usize_land(v___x_372_, v___x_375_);
v___x_377_ = lean_array_uget_borrowed(v_buckets_363_, v___x_376_);
v___x_378_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_362_, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg___boxed(lean_object* v_m_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_m_379_, v_a_380_);
lean_dec_ref(v_a_380_);
lean_dec_ref(v_m_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(lean_object* v_e_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_op_385_; lean_object* v_exprToVarIndex_386_; lean_object* v_varToExpr_387_; lean_object* v___x_388_; 
v_op_385_ = lean_ctor_get(v_a_383_, 0);
v_exprToVarIndex_386_ = lean_ctor_get(v_a_383_, 1);
v_varToExpr_387_ = lean_ctor_get(v_a_383_, 2);
v___x_388_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_exprToVarIndex_386_, v_e_382_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_400_; 
lean_inc_ref(v_varToExpr_387_);
lean_inc_ref(v_exprToVarIndex_386_);
lean_inc_ref(v_op_385_);
v_isSharedCheck_400_ = !lean_is_exclusive(v_a_383_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; lean_object* v_unused_402_; lean_object* v_unused_403_; 
v_unused_401_ = lean_ctor_get(v_a_383_, 2);
lean_dec(v_unused_401_);
v_unused_402_ = lean_ctor_get(v_a_383_, 1);
lean_dec(v_unused_402_);
v_unused_403_ = lean_ctor_get(v_a_383_, 0);
lean_dec(v_unused_403_);
v___x_390_ = v_a_383_;
v_isShared_391_ = v_isSharedCheck_400_;
goto v_resetjp_389_;
}
else
{
lean_dec(v_a_383_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_400_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v_size_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v_size_392_ = lean_ctor_get(v_exprToVarIndex_386_, 0);
lean_inc_n(v_size_392_, 2);
lean_inc_ref(v_e_382_);
v___x_393_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(v_exprToVarIndex_386_, v_e_382_, v_size_392_);
v___x_394_ = lean_array_push(v_varToExpr_387_, v_e_382_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 2, v___x_394_);
lean_ctor_set(v___x_390_, 1, v___x_393_);
v___x_396_ = v___x_390_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_op_385_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v___x_394_);
v___x_396_ = v_reuseFailAlloc_399_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v_size_392_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
}
}
else
{
lean_object* v_val_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_412_; 
lean_dec_ref(v_e_382_);
v_val_404_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_412_ == 0)
{
v___x_406_ = v___x_388_;
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_val_404_);
lean_dec(v___x_388_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v_val_404_);
lean_ctor_set(v___x_408_, 1, v_a_383_);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 0);
lean_ctor_set(v___x_406_, 0, v___x_408_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg___boxed(lean_object* v_e_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_413_, v_a_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar(lean_object* v_e_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_417_, v_a_418_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___boxed(lean_object* v_e_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar(v_e_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0(lean_object* v_00_u03b2_437_, lean_object* v_m_438_, lean_object* v_a_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_m_438_, v_a_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___boxed(lean_object* v_00_u03b2_441_, lean_object* v_m_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0(v_00_u03b2_441_, v_m_442_, v_a_443_);
lean_dec_ref(v_a_443_);
lean_dec_ref(v_m_442_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1(lean_object* v_00_u03b2_445_, lean_object* v_m_446_, lean_object* v_a_447_, lean_object* v_b_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(v_m_446_, v_a_447_, v_b_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0(lean_object* v_00_u03b2_450_, lean_object* v_a_451_, lean_object* v_x_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_451_, v_x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_454_, lean_object* v_a_455_, lean_object* v_x_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0(v_00_u03b2_454_, v_a_455_, v_x_456_);
lean_dec(v_x_456_);
lean_dec_ref(v_a_455_);
return v_res_457_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2(lean_object* v_00_u03b2_458_, lean_object* v_a_459_, lean_object* v_x_460_){
_start:
{
uint8_t v___x_461_; 
v___x_461_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_459_, v_x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_462_, lean_object* v_a_463_, lean_object* v_x_464_){
_start:
{
uint8_t v_res_465_; lean_object* v_r_466_; 
v_res_465_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2(v_00_u03b2_462_, v_a_463_, v_x_464_);
lean_dec(v_x_464_);
lean_dec_ref(v_a_463_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3(lean_object* v_00_u03b2_467_, lean_object* v_data_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(v_data_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4(lean_object* v_00_u03b2_470_, lean_object* v_a_471_, lean_object* v_b_472_, lean_object* v_x_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_471_, v_b_472_, v_x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_475_, lean_object* v_i_476_, lean_object* v_source_477_, lean_object* v_target_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(v_i_476_, v_source_477_, v_target_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_480_, lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(v_x_481_, v_x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(lean_object* v_msgData_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v___x_490_; lean_object* v_env_491_; lean_object* v___x_492_; lean_object* v_mctx_493_; lean_object* v_lctx_494_; lean_object* v_options_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_490_ = lean_st_ref_get(v___y_488_);
v_env_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc_ref(v_env_491_);
lean_dec(v___x_490_);
v___x_492_ = lean_st_ref_get(v___y_486_);
v_mctx_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc_ref(v_mctx_493_);
lean_dec(v___x_492_);
v_lctx_494_ = lean_ctor_get(v___y_485_, 2);
v_options_495_ = lean_ctor_get(v___y_487_, 1);
lean_inc_ref(v_options_495_);
lean_inc_ref(v_lctx_494_);
v___x_496_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_496_, 0, v_env_491_);
lean_ctor_set(v___x_496_, 1, v_mctx_493_);
lean_ctor_set(v___x_496_, 2, v_lctx_494_);
lean_ctor_set(v___x_496_, 3, v_options_495_);
v___x_497_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v_msgData_484_);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1___boxed(lean_object* v_msgData_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msgData_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(lean_object* v_msg_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_ref_512_; lean_object* v___x_513_; lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_522_; 
v_ref_512_ = lean_ctor_get(v___y_509_, 4);
v___x_513_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_522_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_520_; 
lean_inc(v_ref_512_);
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v_ref_512_);
lean_ctor_set(v___x_518_, 1, v_a_514_);
if (v_isShared_517_ == 0)
{
lean_ctor_set_tag(v___x_516_, 1);
lean_ctor_set(v___x_516_, 0, v___x_518_);
v___x_520_ = v___x_516_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg___boxed(lean_object* v_msg_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__0(lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
if (lean_obj_tag(v_a_530_) == 0)
{
lean_object* v___x_532_; 
v___x_532_ = l_List_reverse___redArg(v_a_531_);
return v___x_532_;
}
else
{
lean_object* v_head_533_; lean_object* v_tail_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_543_; 
v_head_533_ = lean_ctor_get(v_a_530_, 0);
v_tail_534_ = lean_ctor_get(v_a_530_, 1);
v_isSharedCheck_543_ = !lean_is_exclusive(v_a_530_);
if (v_isSharedCheck_543_ == 0)
{
v___x_536_ = v_a_530_;
v_isShared_537_ = v_isSharedCheck_543_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_tail_534_);
lean_inc(v_head_533_);
lean_dec(v_a_530_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_543_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = l_Lean_MessageData_ofExpr(v_head_533_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 1, v_a_531_);
lean_ctor_set(v___x_536_, 0, v___x_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_a_531_);
v___x_540_ = v_reuseFailAlloc_542_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
v_a_530_ = v_tail_534_;
v_a_531_ = v___x_540_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__0));
v___x_546_ = l_Lean_stringToMessageData(v___x_545_);
return v___x_546_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__2));
v___x_549_ = l_Lean_stringToMessageData(v___x_548_);
return v___x_549_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__4));
v___x_552_ = l_Lean_stringToMessageData(v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(lean_object* v_idx_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_varToExpr_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v_varToExpr_562_ = lean_ctor_get(v_a_554_, 2);
v___x_563_ = lean_array_get_size(v_varToExpr_562_);
v___x_564_ = lean_nat_dec_lt(v_idx_553_, v___x_563_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
lean_inc_ref(v_varToExpr_562_);
lean_dec_ref(v_a_554_);
v___x_565_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1);
v___x_566_ = l_Nat_reprFast(v_idx_553_);
v___x_567_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
v___x_568_ = l_Lean_MessageData_ofFormat(v___x_567_);
v___x_569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_565_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3);
v___x_571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_569_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = l_Nat_reprFast(v___x_563_);
v___x_573_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
v___x_574_ = l_Lean_MessageData_ofFormat(v___x_573_);
v___x_575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_571_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5);
v___x_577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = lean_array_to_list(v_varToExpr_562_);
v___x_579_ = lean_box(0);
v___x_580_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__0(v___x_578_, v___x_579_);
v___x_581_ = l_Lean_MessageData_ofList(v___x_580_);
v___x_582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_577_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v___x_582_, v_a_557_, v_a_558_, v_a_559_, v_a_560_);
return v___x_583_;
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = lean_array_fget(v_varToExpr_562_, v_idx_553_);
lean_dec(v_idx_553_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v_a_554_);
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
return v___x_586_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___boxed(lean_object* v_idx_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(v_idx_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(lean_object* v_00_u03b1_597_, lean_object* v_msg_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_598_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___boxed(lean_object* v_00_u03b1_608_, lean_object* v_msg_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(v_00_u03b1_608_, v_msg_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec_ref(v___y_610_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(lean_object* v_c_619_){
_start:
{
lean_object* v___y_621_; 
if (lean_obj_tag(v_c_619_) == 0)
{
lean_object* v___x_625_; 
v___x_625_ = lean_unsigned_to_nat(0u);
v___y_621_ = v___x_625_;
goto v___jp_620_;
}
else
{
lean_object* v_val_626_; 
v_val_626_ = lean_ctor_get(v_c_619_, 0);
v___y_621_ = v_val_626_;
goto v___jp_620_;
}
v___jp_620_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = lean_unsigned_to_nat(1u);
v___x_623_ = lean_nat_add(v___y_621_, v___x_622_);
v___x_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0___boxed(lean_object* v_c_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v_c_627_);
lean_dec(v_c_627_);
return v_res_628_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_box(0);
v___x_630_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(lean_object* v_a_631_, lean_object* v_x_632_){
_start:
{
if (lean_obj_tag(v_x_632_) == 0)
{
lean_object* v___x_633_; lean_object* v_val_634_; lean_object* v___x_635_; 
v___x_633_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0, &l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0);
v_val_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_val_634_);
v___x_635_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_635_, 0, v_a_631_);
lean_ctor_set(v___x_635_, 1, v_val_634_);
lean_ctor_set(v___x_635_, 2, v_x_632_);
return v___x_635_;
}
else
{
lean_object* v_key_636_; lean_object* v_value_637_; lean_object* v_tail_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_653_; 
v_key_636_ = lean_ctor_get(v_x_632_, 0);
v_value_637_ = lean_ctor_get(v_x_632_, 1);
v_tail_638_ = lean_ctor_get(v_x_632_, 2);
v_isSharedCheck_653_ = !lean_is_exclusive(v_x_632_);
if (v_isSharedCheck_653_ == 0)
{
v___x_640_ = v_x_632_;
v_isShared_641_ = v_isSharedCheck_653_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_tail_638_);
lean_inc(v_value_637_);
lean_inc(v_key_636_);
lean_dec(v_x_632_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_653_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
uint8_t v___x_642_; 
v___x_642_ = lean_nat_dec_eq(v_key_636_, v_a_631_);
if (v___x_642_ == 0)
{
lean_object* v_tail_643_; lean_object* v___x_645_; 
v_tail_643_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(v_a_631_, v_tail_638_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 2, v_tail_643_);
v___x_645_ = v___x_640_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_key_636_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_value_637_);
lean_ctor_set(v_reuseFailAlloc_646_, 2, v_tail_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v_val_649_; lean_object* v___x_651_; 
lean_dec(v_key_636_);
v___x_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_647_, 0, v_value_637_);
v___x_648_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v___x_647_);
lean_dec_ref_known(v___x_647_, 1);
v_val_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_val_649_);
lean_dec(v___x_648_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v_val_649_);
lean_ctor_set(v___x_640_, 0, v_a_631_);
v___x_651_ = v___x_640_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_631_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_val_649_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v_tail_638_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_654_, lean_object* v_x_655_){
_start:
{
if (lean_obj_tag(v_x_655_) == 0)
{
return v_x_654_;
}
else
{
lean_object* v_key_656_; lean_object* v_value_657_; lean_object* v_tail_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_681_; 
v_key_656_ = lean_ctor_get(v_x_655_, 0);
v_value_657_ = lean_ctor_get(v_x_655_, 1);
v_tail_658_ = lean_ctor_get(v_x_655_, 2);
v_isSharedCheck_681_ = !lean_is_exclusive(v_x_655_);
if (v_isSharedCheck_681_ == 0)
{
v___x_660_ = v_x_655_;
v_isShared_661_ = v_isSharedCheck_681_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_tail_658_);
lean_inc(v_value_657_);
lean_inc(v_key_656_);
lean_dec(v_x_655_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_681_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; uint64_t v___x_663_; uint64_t v___x_664_; uint64_t v___x_665_; uint64_t v_fold_666_; uint64_t v___x_667_; uint64_t v___x_668_; uint64_t v___x_669_; size_t v___x_670_; size_t v___x_671_; size_t v___x_672_; size_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_662_ = lean_array_get_size(v_x_654_);
v___x_663_ = lean_uint64_of_nat(v_key_656_);
v___x_664_ = 32ULL;
v___x_665_ = lean_uint64_shift_right(v___x_663_, v___x_664_);
v_fold_666_ = lean_uint64_xor(v___x_663_, v___x_665_);
v___x_667_ = 16ULL;
v___x_668_ = lean_uint64_shift_right(v_fold_666_, v___x_667_);
v___x_669_ = lean_uint64_xor(v_fold_666_, v___x_668_);
v___x_670_ = lean_uint64_to_usize(v___x_669_);
v___x_671_ = lean_usize_of_nat(v___x_662_);
v___x_672_ = ((size_t)1ULL);
v___x_673_ = lean_usize_sub(v___x_671_, v___x_672_);
v___x_674_ = lean_usize_land(v___x_670_, v___x_673_);
v___x_675_ = lean_array_uget_borrowed(v_x_654_, v___x_674_);
lean_inc(v___x_675_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 2, v___x_675_);
v___x_677_ = v___x_660_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_key_656_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_value_657_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v___x_675_);
v___x_677_ = v_reuseFailAlloc_680_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; 
v___x_678_ = lean_array_uset(v_x_654_, v___x_674_, v___x_677_);
v_x_654_ = v___x_678_;
v_x_655_ = v_tail_658_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(lean_object* v_i_682_, lean_object* v_source_683_, lean_object* v_target_684_){
_start:
{
lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_685_ = lean_array_get_size(v_source_683_);
v___x_686_ = lean_nat_dec_lt(v_i_682_, v___x_685_);
if (v___x_686_ == 0)
{
lean_dec_ref(v_source_683_);
lean_dec(v_i_682_);
return v_target_684_;
}
else
{
lean_object* v_es_687_; lean_object* v___x_688_; lean_object* v_source_689_; lean_object* v_target_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_es_687_ = lean_array_fget(v_source_683_, v_i_682_);
v___x_688_ = lean_box(0);
v_source_689_ = lean_array_fset(v_source_683_, v_i_682_, v___x_688_);
v_target_690_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(v_target_684_, v_es_687_);
v___x_691_ = lean_unsigned_to_nat(1u);
v___x_692_ = lean_nat_add(v_i_682_, v___x_691_);
lean_dec(v_i_682_);
v_i_682_ = v___x_692_;
v_source_683_ = v_source_689_;
v_target_684_ = v_target_690_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(lean_object* v_data_694_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v_nbuckets_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_695_ = lean_array_get_size(v_data_694_);
v___x_696_ = lean_unsigned_to_nat(2u);
v_nbuckets_697_ = lean_nat_mul(v___x_695_, v___x_696_);
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_box(0);
v___x_700_ = lean_mk_array(v_nbuckets_697_, v___x_699_);
v___x_701_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(v___x_698_, v_data_694_, v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(lean_object* v_a_702_, lean_object* v_x_703_){
_start:
{
if (lean_obj_tag(v_x_703_) == 0)
{
uint8_t v___x_704_; 
v___x_704_ = 0;
return v___x_704_;
}
else
{
lean_object* v_key_705_; lean_object* v_tail_706_; uint8_t v___x_707_; 
v_key_705_ = lean_ctor_get(v_x_703_, 0);
v_tail_706_ = lean_ctor_get(v_x_703_, 2);
v___x_707_ = lean_nat_dec_eq(v_key_705_, v_a_702_);
if (v___x_707_ == 0)
{
v_x_703_ = v_tail_706_;
goto _start;
}
else
{
return v___x_707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_709_, lean_object* v_x_710_){
_start:
{
uint8_t v_res_711_; lean_object* v_r_712_; 
v_res_711_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_709_, v_x_710_);
lean_dec(v_x_710_);
lean_dec(v_a_709_);
v_r_712_ = lean_box(v_res_711_);
return v_r_712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(lean_object* v_m_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_size_715_; lean_object* v_buckets_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_764_; 
v_size_715_ = lean_ctor_get(v_m_713_, 0);
v_buckets_716_ = lean_ctor_get(v_m_713_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v_m_713_);
if (v_isSharedCheck_764_ == 0)
{
v___x_718_ = v_m_713_;
v_isShared_719_ = v_isSharedCheck_764_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_buckets_716_);
lean_inc(v_size_715_);
lean_dec(v_m_713_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_764_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; uint64_t v___x_721_; uint64_t v___x_722_; uint64_t v___x_723_; uint64_t v_fold_724_; uint64_t v___x_725_; uint64_t v___x_726_; uint64_t v___x_727_; size_t v___x_728_; size_t v___x_729_; size_t v___x_730_; size_t v___x_731_; size_t v___x_732_; lean_object* v_bkt_733_; uint8_t v___x_734_; 
v___x_720_ = lean_array_get_size(v_buckets_716_);
v___x_721_ = lean_uint64_of_nat(v_a_714_);
v___x_722_ = 32ULL;
v___x_723_ = lean_uint64_shift_right(v___x_721_, v___x_722_);
v_fold_724_ = lean_uint64_xor(v___x_721_, v___x_723_);
v___x_725_ = 16ULL;
v___x_726_ = lean_uint64_shift_right(v_fold_724_, v___x_725_);
v___x_727_ = lean_uint64_xor(v_fold_724_, v___x_726_);
v___x_728_ = lean_uint64_to_usize(v___x_727_);
v___x_729_ = lean_usize_of_nat(v___x_720_);
v___x_730_ = ((size_t)1ULL);
v___x_731_ = lean_usize_sub(v___x_729_, v___x_730_);
v___x_732_ = lean_usize_land(v___x_728_, v___x_731_);
v_bkt_733_ = lean_array_uget_borrowed(v_buckets_716_, v___x_732_);
v___x_734_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_714_, v_bkt_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v_size_x27_736_; lean_object* v___x_737_; lean_object* v_buckets_x27_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_735_ = lean_unsigned_to_nat(1u);
v_size_x27_736_ = lean_nat_add(v_size_715_, v___x_735_);
lean_dec(v_size_715_);
lean_inc(v_bkt_733_);
v___x_737_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_737_, 0, v_a_714_);
lean_ctor_set(v___x_737_, 1, v___x_735_);
lean_ctor_set(v___x_737_, 2, v_bkt_733_);
v_buckets_x27_738_ = lean_array_uset(v_buckets_716_, v___x_732_, v___x_737_);
v___x_739_ = lean_unsigned_to_nat(4u);
v___x_740_ = lean_nat_mul(v_size_x27_736_, v___x_739_);
v___x_741_ = lean_unsigned_to_nat(3u);
v___x_742_ = lean_nat_div(v___x_740_, v___x_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_array_get_size(v_buckets_x27_738_);
v___x_744_ = lean_nat_dec_le(v___x_742_, v___x_743_);
lean_dec(v___x_742_);
if (v___x_744_ == 0)
{
lean_object* v_val_745_; lean_object* v___x_747_; 
v_val_745_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_738_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v_val_745_);
lean_ctor_set(v___x_718_, 0, v_size_x27_736_);
v___x_747_ = v___x_718_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_size_x27_736_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_val_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
else
{
lean_object* v___x_750_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v_buckets_x27_738_);
lean_ctor_set(v___x_718_, 0, v_size_x27_736_);
v___x_750_ = v___x_718_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_size_x27_736_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_buckets_x27_738_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
else
{
lean_object* v___x_752_; lean_object* v_buckets_x27_753_; lean_object* v_bkt_x27_754_; lean_object* v___y_756_; uint8_t v___x_761_; 
lean_inc(v_bkt_733_);
v___x_752_ = lean_box(0);
v_buckets_x27_753_ = lean_array_uset(v_buckets_716_, v___x_732_, v___x_752_);
lean_inc(v_a_714_);
v_bkt_x27_754_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(v_a_714_, v_bkt_733_);
v___x_761_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_714_, v_bkt_x27_754_);
lean_dec(v_a_714_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = lean_nat_sub(v_size_715_, v___x_762_);
lean_dec(v_size_715_);
v___y_756_ = v___x_763_;
goto v___jp_755_;
}
else
{
v___y_756_ = v_size_715_;
goto v___jp_755_;
}
v___jp_755_:
{
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = lean_array_uset(v_buckets_x27_753_, v___x_732_, v_bkt_x27_754_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v___x_757_);
lean_ctor_set(v___x_718_, 0, v___y_756_);
v___x_759_ = v___x_718_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___y_756_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(lean_object* v_coeff_765_, lean_object* v_e_766_, lean_object* v_a_767_){
_start:
{
lean_object* v___x_769_; lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_787_; 
v___x_769_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_766_, v_a_767_);
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_787_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_787_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_787_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_fst_774_; lean_object* v_snd_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_786_; 
v_fst_774_ = lean_ctor_get(v_a_770_, 0);
v_snd_775_ = lean_ctor_get(v_a_770_, 1);
v_isSharedCheck_786_ = !lean_is_exclusive(v_a_770_);
if (v_isSharedCheck_786_ == 0)
{
v___x_777_ = v_a_770_;
v_isShared_778_ = v_isSharedCheck_786_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_snd_775_);
lean_inc(v_fst_774_);
lean_dec(v_a_770_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_786_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_779_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(v_coeff_765_, v_fst_774_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_779_);
v___x_781_ = v___x_777_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_snd_775_);
v___x_781_ = v_reuseFailAlloc_785_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_783_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_781_);
v___x_783_ = v___x_772_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___boxed(lean_object* v_coeff_788_, lean_object* v_e_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_788_, v_e_789_, v_a_790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(lean_object* v_coeff_793_, lean_object* v_e_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_793_, v_e_794_, v_a_795_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___boxed(lean_object* v_coeff_804_, lean_object* v_e_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(v_coeff_804_, v_e_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
return v_res_814_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(lean_object* v_00_u03b2_815_, lean_object* v_a_816_, lean_object* v_x_817_){
_start:
{
uint8_t v___x_818_; 
v___x_818_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_816_, v_x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_819_, lean_object* v_a_820_, lean_object* v_x_821_){
_start:
{
uint8_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(v_00_u03b2_819_, v_a_820_, v_x_821_);
lean_dec(v_x_821_);
lean_dec(v_a_820_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1(lean_object* v_00_u03b2_824_, lean_object* v_data_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_data_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_827_, lean_object* v_i_828_, lean_object* v_source_829_, lean_object* v_target_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(v_i_828_, v_source_829_, v_target_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_832_, lean_object* v_x_833_, lean_object* v_x_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_833_, v_x_834_);
return v___x_835_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_836_; double v___x_837_; 
v___x_836_ = lean_unsigned_to_nat(0u);
v___x_837_ = lean_float_of_nat(v___x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(lean_object* v_cls_841_, lean_object* v_msg_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v_ref_849_; lean_object* v___x_850_; lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_896_; 
v_ref_849_ = lean_ctor_get(v___y_846_, 4);
v___x_850_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_842_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_896_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_896_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_896_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v_traceState_856_; lean_object* v_env_857_; lean_object* v_nextMacroScope_858_; lean_object* v_ngen_859_; lean_object* v_auxDeclNGen_860_; lean_object* v_cache_861_; lean_object* v_messages_862_; lean_object* v_infoState_863_; lean_object* v_snapshotTasks_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_895_; 
v___x_855_ = lean_st_ref_take(v___y_847_);
v_traceState_856_ = lean_ctor_get(v___x_855_, 4);
v_env_857_ = lean_ctor_get(v___x_855_, 0);
v_nextMacroScope_858_ = lean_ctor_get(v___x_855_, 1);
v_ngen_859_ = lean_ctor_get(v___x_855_, 2);
v_auxDeclNGen_860_ = lean_ctor_get(v___x_855_, 3);
v_cache_861_ = lean_ctor_get(v___x_855_, 5);
v_messages_862_ = lean_ctor_get(v___x_855_, 6);
v_infoState_863_ = lean_ctor_get(v___x_855_, 7);
v_snapshotTasks_864_ = lean_ctor_get(v___x_855_, 8);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_895_ == 0)
{
v___x_866_ = v___x_855_;
v_isShared_867_ = v_isSharedCheck_895_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_snapshotTasks_864_);
lean_inc(v_infoState_863_);
lean_inc(v_messages_862_);
lean_inc(v_cache_861_);
lean_inc(v_traceState_856_);
lean_inc(v_auxDeclNGen_860_);
lean_inc(v_ngen_859_);
lean_inc(v_nextMacroScope_858_);
lean_inc(v_env_857_);
lean_dec(v___x_855_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_895_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
uint64_t v_tid_868_; lean_object* v_traces_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_894_; 
v_tid_868_ = lean_ctor_get_uint64(v_traceState_856_, sizeof(void*)*1);
v_traces_869_ = lean_ctor_get(v_traceState_856_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v_traceState_856_);
if (v_isSharedCheck_894_ == 0)
{
v___x_871_ = v_traceState_856_;
v_isShared_872_ = v_isSharedCheck_894_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_traces_869_);
lean_dec(v_traceState_856_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_894_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; double v___x_874_; uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_873_ = lean_box(0);
v___x_874_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_875_ = 0;
v___x_876_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_877_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_877_, 0, v_cls_841_);
lean_ctor_set(v___x_877_, 1, v___x_873_);
lean_ctor_set(v___x_877_, 2, v___x_876_);
lean_ctor_set_float(v___x_877_, sizeof(void*)*3, v___x_874_);
lean_ctor_set_float(v___x_877_, sizeof(void*)*3 + 8, v___x_874_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*3 + 16, v___x_875_);
v___x_878_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_879_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v_a_851_);
lean_ctor_set(v___x_879_, 2, v___x_878_);
lean_inc(v_ref_849_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v_ref_849_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = l_Lean_PersistentArray_push___redArg(v_traces_869_, v___x_880_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_881_);
v___x_883_ = v___x_871_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_881_);
lean_ctor_set_uint64(v_reuseFailAlloc_893_, sizeof(void*)*1, v_tid_868_);
v___x_883_ = v_reuseFailAlloc_893_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 4, v___x_883_);
v___x_885_ = v___x_866_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_env_857_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_nextMacroScope_858_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v_ngen_859_);
lean_ctor_set(v_reuseFailAlloc_892_, 3, v_auxDeclNGen_860_);
lean_ctor_set(v_reuseFailAlloc_892_, 4, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_892_, 5, v_cache_861_);
lean_ctor_set(v_reuseFailAlloc_892_, 6, v_messages_862_);
lean_ctor_set(v_reuseFailAlloc_892_, 7, v_infoState_863_);
lean_ctor_set(v_reuseFailAlloc_892_, 8, v_snapshotTasks_864_);
v___x_885_ = v_reuseFailAlloc_892_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_886_ = lean_st_ref_put(v___y_847_, v___x_885_);
v___x_887_ = lean_box(0);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v___y_843_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_888_);
v___x_890_ = v___x_853_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___boxed(lean_object* v_cls_897_, lean_object* v_msg_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_897_, v_msg_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
return v_res_905_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6(void){
_start:
{
lean_object* v_cls_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v_cls_916_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_917_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_918_ = l_Lean_Name_append(v___x_917_, v_cls_916_);
return v___x_918_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__7));
v___x_921_ = l_Lean_stringToMessageData(v___x_920_);
return v___x_921_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__9));
v___x_924_ = l_Lean_stringToMessageData(v___x_923_);
return v___x_924_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__11));
v___x_927_ = l_Lean_stringToMessageData(v___x_926_);
return v___x_927_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__13));
v___x_930_ = l_Lean_stringToMessageData(v___x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(lean_object* v_op_931_, lean_object* v_coeff_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
if (lean_obj_tag(v_a_933_) == 5)
{
lean_object* v_fn_942_; 
v_fn_942_ = lean_ctor_get(v_a_933_, 0);
if (lean_obj_tag(v_fn_942_) == 5)
{
lean_object* v_arg_943_; lean_object* v_fn_944_; lean_object* v_arg_945_; uint8_t v___x_946_; 
v_arg_943_ = lean_ctor_get(v_a_933_, 1);
v_fn_944_ = lean_ctor_get(v_fn_942_, 0);
v_arg_945_ = lean_ctor_get(v_fn_942_, 1);
lean_inc_ref(v_fn_944_);
v___x_946_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(v_fn_944_);
if (v___x_946_ == 0)
{
lean_object* v_options_947_; uint8_t v_hasTrace_948_; 
v_options_947_ = lean_ctor_get(v_a_939_, 1);
v_hasTrace_948_ = lean_ctor_get_uint8(v_options_947_, sizeof(void*)*1);
if (v_hasTrace_948_ == 0)
{
lean_object* v___x_949_; 
lean_dec_ref(v_op_931_);
v___x_949_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_932_, v_a_933_, v_a_934_);
return v___x_949_;
}
else
{
lean_object* v_toCold_950_; lean_object* v_inheritedTraceOptions_951_; lean_object* v_cls_952_; lean_object* v___x_953_; uint8_t v___x_954_; 
v_toCold_950_ = lean_ctor_get(v_a_939_, 0);
v_inheritedTraceOptions_951_ = lean_ctor_get(v_toCold_950_, 4);
v_cls_952_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_953_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_954_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_951_, v_options_947_, v___x_953_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; 
lean_dec_ref(v_op_931_);
v___x_955_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_932_, v_a_933_, v_a_934_);
return v___x_955_;
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_956_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8);
lean_inc_ref(v_fn_944_);
v___x_957_ = l_Lean_MessageData_ofExpr(v_fn_944_);
v___x_958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_956_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10);
v___x_960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_958_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
lean_inc_ref(v_arg_945_);
v___x_961_ = l_Lean_MessageData_ofExpr(v_arg_945_);
v___x_962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v___x_959_);
lean_inc_ref(v_arg_943_);
v___x_964_ = l_Lean_MessageData_ofExpr(v_arg_943_);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_931_);
v___x_969_ = l_Lean_MessageData_ofExpr(v___x_968_);
v___x_970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_967_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14);
v___x_972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_952_, v___x_972_, v_a_934_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v_snd_975_; lean_object* v___x_976_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
v_snd_975_ = lean_ctor_get(v_a_974_, 1);
lean_inc(v_snd_975_);
lean_dec(v_a_974_);
v___x_976_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_932_, v_a_933_, v_snd_975_);
return v___x_976_;
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec_ref_known(v_a_933_, 2);
lean_dec_ref(v_coeff_932_);
v_a_977_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_973_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_973_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
}
else
{
lean_object* v___x_985_; 
lean_inc_ref(v_arg_945_);
lean_inc_ref(v_arg_943_);
lean_dec_ref_known(v_a_933_, 2);
lean_inc_ref(v_op_931_);
v___x_985_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_931_, v_coeff_932_, v_arg_945_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v_fst_987_; lean_object* v_snd_988_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_985_, 1);
v_fst_987_ = lean_ctor_get(v_a_986_, 0);
lean_inc(v_fst_987_);
v_snd_988_ = lean_ctor_get(v_a_986_, 1);
lean_inc(v_snd_988_);
lean_dec(v_a_986_);
v_coeff_932_ = v_fst_987_;
v_a_933_ = v_arg_943_;
v_a_934_ = v_snd_988_;
goto _start;
}
else
{
lean_dec_ref(v_arg_943_);
lean_dec_ref(v_op_931_);
return v___x_985_;
}
}
}
else
{
lean_object* v___x_990_; 
lean_dec_ref(v_op_931_);
v___x_990_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_932_, v_a_933_, v_a_934_);
return v___x_990_;
}
}
else
{
lean_object* v___x_991_; 
lean_dec_ref(v_op_931_);
v___x_991_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_932_, v_a_933_, v_a_934_);
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___boxed(lean_object* v_op_992_, lean_object* v_coeff_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_992_, v_coeff_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(lean_object* v_cls_1004_, lean_object* v_msg_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_1004_, v_msg_1005_, v___y_1006_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___boxed(lean_object* v_cls_1015_, lean_object* v_msg_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(v_cls_1015_, v_msg_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
return v_res_1025_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = lean_box(0);
v___x_1027_ = lean_unsigned_to_nat(16u);
v___x_1028_ = lean_mk_array(v___x_1027_, v___x_1026_);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1030_ = lean_unsigned_to_nat(0u);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v___x_1029_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(lean_object* v_op_1032_, lean_object* v_e_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1043_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_1032_, v___x_1042_, v_e_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___boxed(lean_object* v_op_1044_, lean_object* v_e_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_op_1044_, v_e_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(lean_object* v_a_1055_, lean_object* v_x_1056_){
_start:
{
if (lean_obj_tag(v_x_1056_) == 0)
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_box(0);
return v___x_1057_;
}
else
{
lean_object* v_key_1058_; lean_object* v_value_1059_; lean_object* v_tail_1060_; uint8_t v___x_1061_; 
v_key_1058_ = lean_ctor_get(v_x_1056_, 0);
v_value_1059_ = lean_ctor_get(v_x_1056_, 1);
v_tail_1060_ = lean_ctor_get(v_x_1056_, 2);
v___x_1061_ = lean_nat_dec_eq(v_key_1058_, v_a_1055_);
if (v___x_1061_ == 0)
{
v_x_1056_ = v_tail_1060_;
goto _start;
}
else
{
lean_object* v___x_1063_; 
lean_inc(v_value_1059_);
v___x_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1063_, 0, v_value_1059_);
return v___x_1063_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg___boxed(lean_object* v_a_1064_, lean_object* v_x_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1064_, v_x_1065_);
lean_dec(v_x_1065_);
lean_dec(v_a_1064_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(lean_object* v_m_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v_buckets_1069_; lean_object* v___x_1070_; uint64_t v___x_1071_; uint64_t v___x_1072_; uint64_t v___x_1073_; uint64_t v_fold_1074_; uint64_t v___x_1075_; uint64_t v___x_1076_; uint64_t v___x_1077_; size_t v___x_1078_; size_t v___x_1079_; size_t v___x_1080_; size_t v___x_1081_; size_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v_buckets_1069_ = lean_ctor_get(v_m_1067_, 1);
v___x_1070_ = lean_array_get_size(v_buckets_1069_);
v___x_1071_ = lean_uint64_of_nat(v_a_1068_);
v___x_1072_ = 32ULL;
v___x_1073_ = lean_uint64_shift_right(v___x_1071_, v___x_1072_);
v_fold_1074_ = lean_uint64_xor(v___x_1071_, v___x_1073_);
v___x_1075_ = 16ULL;
v___x_1076_ = lean_uint64_shift_right(v_fold_1074_, v___x_1075_);
v___x_1077_ = lean_uint64_xor(v_fold_1074_, v___x_1076_);
v___x_1078_ = lean_uint64_to_usize(v___x_1077_);
v___x_1079_ = lean_usize_of_nat(v___x_1070_);
v___x_1080_ = ((size_t)1ULL);
v___x_1081_ = lean_usize_sub(v___x_1079_, v___x_1080_);
v___x_1082_ = lean_usize_land(v___x_1078_, v___x_1081_);
v___x_1083_ = lean_array_uget_borrowed(v_buckets_1069_, v___x_1082_);
v___x_1084_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1068_, v___x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg___boxed(lean_object* v_m_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1085_, v_a_1086_);
lean_dec(v_a_1086_);
lean_dec_ref(v_m_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(lean_object* v_a_1088_, lean_object* v_b_1089_, lean_object* v_x_1090_){
_start:
{
if (lean_obj_tag(v_x_1090_) == 0)
{
lean_dec(v_b_1089_);
lean_dec(v_a_1088_);
return v_x_1090_;
}
else
{
lean_object* v_key_1091_; lean_object* v_value_1092_; lean_object* v_tail_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1105_; 
v_key_1091_ = lean_ctor_get(v_x_1090_, 0);
v_value_1092_ = lean_ctor_get(v_x_1090_, 1);
v_tail_1093_ = lean_ctor_get(v_x_1090_, 2);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_x_1090_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1095_ = v_x_1090_;
v_isShared_1096_ = v_isSharedCheck_1105_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_tail_1093_);
lean_inc(v_value_1092_);
lean_inc(v_key_1091_);
lean_dec(v_x_1090_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1105_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
uint8_t v___x_1097_; 
v___x_1097_ = lean_nat_dec_eq(v_key_1091_, v_a_1088_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1098_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1088_, v_b_1089_, v_tail_1093_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 2, v___x_1098_);
v___x_1100_ = v___x_1095_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_key_1091_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_value_1092_);
lean_ctor_set(v_reuseFailAlloc_1101_, 2, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
else
{
lean_object* v___x_1103_; 
lean_dec(v_value_1092_);
lean_dec(v_key_1091_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 1, v_b_1089_);
lean_ctor_set(v___x_1095_, 0, v_a_1088_);
v___x_1103_ = v___x_1095_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1088_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_b_1089_);
lean_ctor_set(v_reuseFailAlloc_1104_, 2, v_tail_1093_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(lean_object* v_m_1106_, lean_object* v_a_1107_, lean_object* v_b_1108_){
_start:
{
lean_object* v_size_1109_; lean_object* v_buckets_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1153_; 
v_size_1109_ = lean_ctor_get(v_m_1106_, 0);
v_buckets_1110_ = lean_ctor_get(v_m_1106_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_m_1106_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1112_ = v_m_1106_;
v_isShared_1113_ = v_isSharedCheck_1153_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_buckets_1110_);
lean_inc(v_size_1109_);
lean_dec(v_m_1106_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1153_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; uint64_t v___x_1115_; uint64_t v___x_1116_; uint64_t v___x_1117_; uint64_t v_fold_1118_; uint64_t v___x_1119_; uint64_t v___x_1120_; uint64_t v___x_1121_; size_t v___x_1122_; size_t v___x_1123_; size_t v___x_1124_; size_t v___x_1125_; size_t v___x_1126_; lean_object* v_bkt_1127_; uint8_t v___x_1128_; 
v___x_1114_ = lean_array_get_size(v_buckets_1110_);
v___x_1115_ = lean_uint64_of_nat(v_a_1107_);
v___x_1116_ = 32ULL;
v___x_1117_ = lean_uint64_shift_right(v___x_1115_, v___x_1116_);
v_fold_1118_ = lean_uint64_xor(v___x_1115_, v___x_1117_);
v___x_1119_ = 16ULL;
v___x_1120_ = lean_uint64_shift_right(v_fold_1118_, v___x_1119_);
v___x_1121_ = lean_uint64_xor(v_fold_1118_, v___x_1120_);
v___x_1122_ = lean_uint64_to_usize(v___x_1121_);
v___x_1123_ = lean_usize_of_nat(v___x_1114_);
v___x_1124_ = ((size_t)1ULL);
v___x_1125_ = lean_usize_sub(v___x_1123_, v___x_1124_);
v___x_1126_ = lean_usize_land(v___x_1122_, v___x_1125_);
v_bkt_1127_ = lean_array_uget_borrowed(v_buckets_1110_, v___x_1126_);
v___x_1128_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1107_, v_bkt_1127_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; lean_object* v_size_x27_1130_; lean_object* v___x_1131_; lean_object* v_buckets_x27_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1129_ = lean_unsigned_to_nat(1u);
v_size_x27_1130_ = lean_nat_add(v_size_1109_, v___x_1129_);
lean_dec(v_size_1109_);
lean_inc(v_bkt_1127_);
v___x_1131_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1131_, 0, v_a_1107_);
lean_ctor_set(v___x_1131_, 1, v_b_1108_);
lean_ctor_set(v___x_1131_, 2, v_bkt_1127_);
v_buckets_x27_1132_ = lean_array_uset(v_buckets_1110_, v___x_1126_, v___x_1131_);
v___x_1133_ = lean_unsigned_to_nat(4u);
v___x_1134_ = lean_nat_mul(v_size_x27_1130_, v___x_1133_);
v___x_1135_ = lean_unsigned_to_nat(3u);
v___x_1136_ = lean_nat_div(v___x_1134_, v___x_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_array_get_size(v_buckets_x27_1132_);
v___x_1138_ = lean_nat_dec_le(v___x_1136_, v___x_1137_);
lean_dec(v___x_1136_);
if (v___x_1138_ == 0)
{
lean_object* v_val_1139_; lean_object* v___x_1141_; 
v_val_1139_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_1132_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 1, v_val_1139_);
lean_ctor_set(v___x_1112_, 0, v_size_x27_1130_);
v___x_1141_ = v___x_1112_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_size_x27_1130_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_val_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
else
{
lean_object* v___x_1144_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 1, v_buckets_x27_1132_);
lean_ctor_set(v___x_1112_, 0, v_size_x27_1130_);
v___x_1144_ = v___x_1112_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_size_x27_1130_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_buckets_x27_1132_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
else
{
lean_object* v___x_1146_; lean_object* v_buckets_x27_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
lean_inc(v_bkt_1127_);
v___x_1146_ = lean_box(0);
v_buckets_x27_1147_ = lean_array_uset(v_buckets_1110_, v___x_1126_, v___x_1146_);
v___x_1148_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1107_, v_b_1108_, v_bkt_1127_);
v___x_1149_ = lean_array_uset(v_buckets_x27_1147_, v___x_1126_, v___x_1148_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 1, v___x_1149_);
v___x_1151_ = v___x_1112_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_size_1109_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(lean_object* v_snd_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_){
_start:
{
if (lean_obj_tag(v_x_1156_) == 0)
{
return v_x_1155_;
}
else
{
lean_object* v_key_1157_; lean_object* v_value_1158_; lean_object* v_tail_1159_; lean_object* v___y_1161_; lean_object* v___x_1164_; 
v_key_1157_ = lean_ctor_get(v_x_1156_, 0);
lean_inc(v_key_1157_);
v_value_1158_ = lean_ctor_get(v_x_1156_, 1);
lean_inc(v_value_1158_);
v_tail_1159_ = lean_ctor_get(v_x_1156_, 2);
lean_inc(v_tail_1159_);
lean_dec_ref_known(v_x_1156_, 3);
v___x_1164_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_snd_1154_, v_key_1157_);
if (lean_obj_tag(v___x_1164_) == 1)
{
lean_object* v_val_1165_; uint8_t v___x_1166_; 
v_val_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_val_1165_);
lean_dec_ref_known(v___x_1164_, 1);
v___x_1166_ = lean_nat_dec_le(v_value_1158_, v_val_1165_);
if (v___x_1166_ == 0)
{
lean_dec(v_value_1158_);
v___y_1161_ = v_val_1165_;
goto v___jp_1160_;
}
else
{
lean_dec(v_val_1165_);
v___y_1161_ = v_value_1158_;
goto v___jp_1160_;
}
}
else
{
lean_dec(v___x_1164_);
lean_dec(v_value_1158_);
lean_dec(v_key_1157_);
v_x_1156_ = v_tail_1159_;
goto _start;
}
v___jp_1160_:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(v_x_1155_, v_key_1157_, v___y_1161_);
v_x_1155_ = v___x_1162_;
v_x_1156_ = v_tail_1159_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5___boxed(lean_object* v_snd_1168_, lean_object* v_x_1169_, lean_object* v_x_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(v_snd_1168_, v_x_1169_, v_x_1170_);
lean_dec_ref(v_snd_1168_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(lean_object* v_snd_1172_, lean_object* v_as_1173_, size_t v_i_1174_, size_t v_stop_1175_, lean_object* v_b_1176_){
_start:
{
uint8_t v___x_1177_; 
v___x_1177_ = lean_usize_dec_eq(v_i_1174_, v_stop_1175_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; size_t v___x_1180_; size_t v___x_1181_; 
v___x_1178_ = lean_array_uget_borrowed(v_as_1173_, v_i_1174_);
lean_inc(v___x_1178_);
v___x_1179_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(v_snd_1172_, v_b_1176_, v___x_1178_);
v___x_1180_ = ((size_t)1ULL);
v___x_1181_ = lean_usize_add(v_i_1174_, v___x_1180_);
v_i_1174_ = v___x_1181_;
v_b_1176_ = v___x_1179_;
goto _start;
}
else
{
return v_b_1176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6___boxed(lean_object* v_snd_1183_, lean_object* v_as_1184_, lean_object* v_i_1185_, lean_object* v_stop_1186_, lean_object* v_b_1187_){
_start:
{
size_t v_i_boxed_1188_; size_t v_stop_boxed_1189_; lean_object* v_res_1190_; 
v_i_boxed_1188_ = lean_unbox_usize(v_i_1185_);
lean_dec(v_i_1185_);
v_stop_boxed_1189_ = lean_unbox_usize(v_stop_1186_);
lean_dec(v_stop_1186_);
v_res_1190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1183_, v_as_1184_, v_i_boxed_1188_, v_stop_boxed_1189_, v_b_1187_);
lean_dec_ref(v_as_1184_);
lean_dec_ref(v_snd_1183_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(lean_object* v_commonCnt_1191_, lean_object* v_a_1192_, lean_object* v_x_1193_){
_start:
{
if (lean_obj_tag(v_x_1193_) == 0)
{
lean_dec(v_a_1192_);
return v_x_1193_;
}
else
{
lean_object* v_key_1194_; lean_object* v_value_1195_; lean_object* v_tail_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1209_; 
v_key_1194_ = lean_ctor_get(v_x_1193_, 0);
v_value_1195_ = lean_ctor_get(v_x_1193_, 1);
v_tail_1196_ = lean_ctor_get(v_x_1193_, 2);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_x_1193_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1198_ = v_x_1193_;
v_isShared_1199_ = v_isSharedCheck_1209_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_tail_1196_);
lean_inc(v_value_1195_);
lean_inc(v_key_1194_);
lean_dec(v_x_1193_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1209_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
uint8_t v___x_1200_; 
v___x_1200_ = lean_nat_dec_eq(v_key_1194_, v_a_1192_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1201_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1191_, v_a_1192_, v_tail_1196_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 2, v___x_1201_);
v___x_1203_ = v___x_1198_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_key_1194_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_value_1195_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
else
{
lean_object* v___x_1205_; lean_object* v___x_1207_; 
lean_dec(v_key_1194_);
v___x_1205_ = lean_nat_sub(v_value_1195_, v_commonCnt_1191_);
lean_dec(v_value_1195_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 1, v___x_1205_);
lean_ctor_set(v___x_1198_, 0, v_a_1192_);
v___x_1207_ = v___x_1198_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1192_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1208_, 2, v_tail_1196_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0___boxed(lean_object* v_commonCnt_1210_, lean_object* v_a_1211_, lean_object* v_x_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1210_, v_a_1211_, v_x_1212_);
lean_dec(v_commonCnt_1210_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(lean_object* v_commonCnt_1214_, lean_object* v_m_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v_size_1217_; lean_object* v_buckets_1218_; lean_object* v___x_1219_; uint64_t v___x_1220_; uint64_t v___x_1221_; uint64_t v___x_1222_; uint64_t v_fold_1223_; uint64_t v___x_1224_; uint64_t v___x_1225_; uint64_t v___x_1226_; size_t v___x_1227_; size_t v___x_1228_; size_t v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; lean_object* v_bucket_1232_; uint8_t v___x_1233_; 
v_size_1217_ = lean_ctor_get(v_m_1215_, 0);
v_buckets_1218_ = lean_ctor_get(v_m_1215_, 1);
v___x_1219_ = lean_array_get_size(v_buckets_1218_);
v___x_1220_ = lean_uint64_of_nat(v_a_1216_);
v___x_1221_ = 32ULL;
v___x_1222_ = lean_uint64_shift_right(v___x_1220_, v___x_1221_);
v_fold_1223_ = lean_uint64_xor(v___x_1220_, v___x_1222_);
v___x_1224_ = 16ULL;
v___x_1225_ = lean_uint64_shift_right(v_fold_1223_, v___x_1224_);
v___x_1226_ = lean_uint64_xor(v_fold_1223_, v___x_1225_);
v___x_1227_ = lean_uint64_to_usize(v___x_1226_);
v___x_1228_ = lean_usize_of_nat(v___x_1219_);
v___x_1229_ = ((size_t)1ULL);
v___x_1230_ = lean_usize_sub(v___x_1228_, v___x_1229_);
v___x_1231_ = lean_usize_land(v___x_1227_, v___x_1230_);
v_bucket_1232_ = lean_array_uget_borrowed(v_buckets_1218_, v___x_1231_);
v___x_1233_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1216_, v_bucket_1232_);
if (v___x_1233_ == 0)
{
lean_dec(v_a_1216_);
return v_m_1215_;
}
else
{
lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1244_; 
lean_inc(v_bucket_1232_);
lean_inc_ref(v_buckets_1218_);
lean_inc(v_size_1217_);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_m_1215_);
if (v_isSharedCheck_1244_ == 0)
{
lean_object* v_unused_1245_; lean_object* v_unused_1246_; 
v_unused_1245_ = lean_ctor_get(v_m_1215_, 1);
lean_dec(v_unused_1245_);
v_unused_1246_ = lean_ctor_get(v_m_1215_, 0);
lean_dec(v_unused_1246_);
v___x_1235_ = v_m_1215_;
v_isShared_1236_ = v_isSharedCheck_1244_;
goto v_resetjp_1234_;
}
else
{
lean_dec(v_m_1215_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1244_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1237_; lean_object* v_buckets_1238_; lean_object* v_bucket_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1237_ = lean_box(0);
v_buckets_1238_ = lean_array_uset(v_buckets_1218_, v___x_1231_, v___x_1237_);
v_bucket_1239_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1214_, v_a_1216_, v_bucket_1232_);
v___x_1240_ = lean_array_uset(v_buckets_1238_, v___x_1231_, v_bucket_1239_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v___x_1240_);
v___x_1242_ = v___x_1235_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_size_1217_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0___boxed(lean_object* v_commonCnt_1247_, lean_object* v_m_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_commonCnt_1247_, v_m_1248_, v_a_1249_);
lean_dec(v_commonCnt_1247_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(lean_object* v_x_1251_, lean_object* v_x_1252_){
_start:
{
if (lean_obj_tag(v_x_1252_) == 0)
{
return v_x_1251_;
}
else
{
lean_object* v_key_1253_; lean_object* v_value_1254_; lean_object* v_tail_1255_; lean_object* v___x_1256_; 
v_key_1253_ = lean_ctor_get(v_x_1252_, 0);
lean_inc(v_key_1253_);
v_value_1254_ = lean_ctor_get(v_x_1252_, 1);
lean_inc(v_value_1254_);
v_tail_1255_ = lean_ctor_get(v_x_1252_, 2);
lean_inc(v_tail_1255_);
lean_dec_ref_known(v_x_1252_, 3);
v___x_1256_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_value_1254_, v_x_1251_, v_key_1253_);
lean_dec(v_value_1254_);
v_x_1251_ = v___x_1256_;
v_x_1252_ = v_tail_1255_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(lean_object* v_x_1258_, lean_object* v_x_1259_){
_start:
{
if (lean_obj_tag(v_x_1259_) == 0)
{
return v_x_1258_;
}
else
{
lean_object* v_key_1260_; lean_object* v_value_1261_; lean_object* v_tail_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v_key_1260_ = lean_ctor_get(v_x_1259_, 0);
lean_inc(v_key_1260_);
v_value_1261_ = lean_ctor_get(v_x_1259_, 1);
lean_inc(v_value_1261_);
v_tail_1262_ = lean_ctor_get(v_x_1259_, 2);
lean_inc(v_tail_1262_);
lean_dec_ref_known(v_x_1259_, 3);
v___x_1263_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_value_1261_, v_x_1258_, v_key_1260_);
lean_dec(v_value_1261_);
v___x_1264_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(v___x_1263_, v_tail_1262_);
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(lean_object* v_as_1265_, size_t v_i_1266_, size_t v_stop_1267_, lean_object* v_b_1268_){
_start:
{
uint8_t v___x_1269_; 
v___x_1269_ = lean_usize_dec_eq(v_i_1266_, v_stop_1267_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1271_; size_t v___x_1272_; size_t v___x_1273_; 
v___x_1270_ = lean_array_uget_borrowed(v_as_1265_, v_i_1266_);
lean_inc(v___x_1270_);
v___x_1271_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(v_b_1268_, v___x_1270_);
v___x_1272_ = ((size_t)1ULL);
v___x_1273_ = lean_usize_add(v_i_1266_, v___x_1272_);
v_i_1266_ = v___x_1273_;
v_b_1268_ = v___x_1271_;
goto _start;
}
else
{
return v_b_1268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2___boxed(lean_object* v_as_1275_, lean_object* v_i_1276_, lean_object* v_stop_1277_, lean_object* v_b_1278_){
_start:
{
size_t v_i_boxed_1279_; size_t v_stop_boxed_1280_; lean_object* v_res_1281_; 
v_i_boxed_1279_ = lean_unbox_usize(v_i_1276_);
lean_dec(v_i_1276_);
v_stop_boxed_1280_ = lean_unbox_usize(v_stop_1277_);
lean_dec(v_stop_1277_);
v_res_1281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_as_1275_, v_i_boxed_1279_, v_stop_boxed_1280_, v_b_1278_);
lean_dec_ref(v_as_1275_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(lean_object* v_x_1282_, lean_object* v_y_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v___y_1287_; lean_object* v_fst_1288_; lean_object* v_snd_1289_; lean_object* v_size_1293_; lean_object* v_buckets_1294_; lean_object* v_size_1295_; lean_object* v_buckets_1296_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v_buckets_1305_; lean_object* v___y_1306_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v_buckets_1317_; lean_object* v_fst_1325_; lean_object* v_buckets_1326_; lean_object* v_snd_1327_; uint8_t v___x_1337_; 
v_size_1293_ = lean_ctor_get(v_y_1283_, 0);
lean_inc(v_size_1293_);
v_buckets_1294_ = lean_ctor_get(v_y_1283_, 1);
v_size_1295_ = lean_ctor_get(v_x_1282_, 0);
lean_inc(v_size_1295_);
v_buckets_1296_ = lean_ctor_get(v_x_1282_, 1);
v___x_1337_ = lean_nat_dec_lt(v_size_1293_, v_size_1295_);
if (v___x_1337_ == 0)
{
lean_inc_ref(v_buckets_1296_);
v_fst_1325_ = v_x_1282_;
v_buckets_1326_ = v_buckets_1296_;
v_snd_1327_ = v_y_1283_;
goto v___jp_1324_;
}
else
{
lean_inc_ref(v_buckets_1294_);
v_fst_1325_ = v_y_1283_;
v_buckets_1326_ = v_buckets_1294_;
v_snd_1327_ = v_x_1282_;
goto v___jp_1324_;
}
v___jp_1286_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1290_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1290_, 0, v___y_1287_);
lean_ctor_set(v___x_1290_, 1, v_fst_1288_);
lean_ctor_set(v___x_1290_, 2, v_snd_1289_);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v_a_1284_);
v___x_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
return v___x_1292_;
}
v___jp_1297_:
{
uint8_t v___x_1301_; 
v___x_1301_ = lean_nat_dec_lt(v_size_1293_, v_size_1295_);
lean_dec(v_size_1295_);
lean_dec(v_size_1293_);
if (v___x_1301_ == 0)
{
v___y_1287_ = v___y_1299_;
v_fst_1288_ = v___y_1298_;
v_snd_1289_ = v___y_1300_;
goto v___jp_1286_;
}
else
{
v___y_1287_ = v___y_1299_;
v_fst_1288_ = v___y_1300_;
v_snd_1289_ = v___y_1298_;
goto v___jp_1286_;
}
}
v___jp_1302_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1307_ = lean_unsigned_to_nat(0u);
v___x_1308_ = lean_array_get_size(v_buckets_1305_);
v___x_1309_ = lean_nat_dec_lt(v___x_1307_, v___x_1308_);
if (v___x_1309_ == 0)
{
lean_dec_ref(v_buckets_1305_);
v___y_1298_ = v___y_1306_;
v___y_1299_ = v___y_1304_;
v___y_1300_ = v___y_1303_;
goto v___jp_1297_;
}
else
{
size_t v___x_1310_; size_t v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = ((size_t)0ULL);
v___x_1311_ = lean_usize_of_nat(v___x_1308_);
v___x_1312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1305_, v___x_1310_, v___x_1311_, v___y_1303_);
lean_dec_ref(v_buckets_1305_);
v___y_1298_ = v___y_1306_;
v___y_1299_ = v___y_1304_;
v___y_1300_ = v___x_1312_;
goto v___jp_1297_;
}
}
v___jp_1313_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1318_ = lean_unsigned_to_nat(0u);
v___x_1319_ = lean_array_get_size(v_buckets_1317_);
v___x_1320_ = lean_nat_dec_lt(v___x_1318_, v___x_1319_);
if (v___x_1320_ == 0)
{
v___y_1303_ = v___y_1314_;
v___y_1304_ = v___y_1316_;
v_buckets_1305_ = v_buckets_1317_;
v___y_1306_ = v___y_1315_;
goto v___jp_1302_;
}
else
{
size_t v___x_1321_; size_t v___x_1322_; lean_object* v___x_1323_; 
v___x_1321_ = ((size_t)0ULL);
v___x_1322_ = lean_usize_of_nat(v___x_1319_);
v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1317_, v___x_1321_, v___x_1322_, v___y_1315_);
v___y_1303_ = v___y_1314_;
v___y_1304_ = v___y_1316_;
v_buckets_1305_ = v_buckets_1317_;
v___y_1306_ = v___x_1323_;
goto v___jp_1302_;
}
}
v___jp_1324_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1328_ = lean_unsigned_to_nat(0u);
v___x_1329_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1330_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1331_ = lean_array_get_size(v_buckets_1326_);
v___x_1332_ = lean_nat_dec_lt(v___x_1328_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_dec_ref(v_buckets_1326_);
v___y_1314_ = v_snd_1327_;
v___y_1315_ = v_fst_1325_;
v___y_1316_ = v___x_1330_;
v_buckets_1317_ = v___x_1329_;
goto v___jp_1313_;
}
else
{
size_t v___x_1333_; size_t v___x_1334_; lean_object* v___x_1335_; lean_object* v_buckets_1336_; 
v___x_1333_ = ((size_t)0ULL);
v___x_1334_ = lean_usize_of_nat(v___x_1331_);
v___x_1335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1327_, v_buckets_1326_, v___x_1333_, v___x_1334_, v___x_1330_);
lean_dec_ref(v_buckets_1326_);
v_buckets_1336_ = lean_ctor_get(v___x_1335_, 1);
lean_inc_ref(v_buckets_1336_);
v___y_1314_ = v_snd_1327_;
v___y_1315_ = v_fst_1325_;
v___y_1316_ = v___x_1335_;
v_buckets_1317_ = v_buckets_1336_;
goto v___jp_1313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg___boxed(lean_object* v_x_1338_, lean_object* v_y_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1338_, v_y_1339_, v_a_1340_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(lean_object* v_x_1343_, lean_object* v_y_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1343_, v_y_1344_, v_a_1345_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___boxed(lean_object* v_x_1354_, lean_object* v_y_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(v_x_1354_, v_y_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3(lean_object* v_00_u03b2_1365_, lean_object* v_m_1366_, lean_object* v_a_1367_, lean_object* v_b_1368_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(v_m_1366_, v_a_1367_, v_b_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4(lean_object* v_00_u03b2_1370_, lean_object* v_m_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1371_, v_a_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___boxed(lean_object* v_00_u03b2_1374_, lean_object* v_m_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4(v_00_u03b2_1374_, v_m_1375_, v_a_1376_);
lean_dec(v_a_1376_);
lean_dec_ref(v_m_1375_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5(lean_object* v_00_u03b2_1378_, lean_object* v_a_1379_, lean_object* v_b_1380_, lean_object* v_x_1381_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1379_, v_b_1380_, v_x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7(lean_object* v_00_u03b2_1383_, lean_object* v_a_1384_, lean_object* v_x_1385_){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1384_, v_x_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1387_, lean_object* v_a_1388_, lean_object* v_x_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7(v_00_u03b2_1387_, v_a_1388_, v_x_1389_);
lean_dec(v_x_1389_);
lean_dec(v_a_1388_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(lean_object* v_x_1391_, lean_object* v_x_1392_){
_start:
{
if (lean_obj_tag(v_x_1392_) == 0)
{
return v_x_1391_;
}
else
{
lean_object* v_key_1393_; lean_object* v_value_1394_; lean_object* v_tail_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v_key_1393_ = lean_ctor_get(v_x_1392_, 0);
v_value_1394_ = lean_ctor_get(v_x_1392_, 1);
v_tail_1395_ = lean_ctor_get(v_x_1392_, 2);
lean_inc(v_value_1394_);
lean_inc(v_key_1393_);
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v_key_1393_);
lean_ctor_set(v___x_1396_, 1, v_value_1394_);
v___x_1397_ = lean_array_push(v_x_1391_, v___x_1396_);
v_x_1391_ = v___x_1397_;
v_x_1392_ = v_tail_1395_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___boxed(lean_object* v_x_1399_, lean_object* v_x_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(v_x_1399_, v_x_1400_);
lean_dec(v_x_1400_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(lean_object* v_as_1402_, size_t v_i_1403_, size_t v_stop_1404_, lean_object* v_b_1405_){
_start:
{
uint8_t v___x_1406_; 
v___x_1406_ = lean_usize_dec_eq(v_i_1403_, v_stop_1404_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; size_t v___x_1409_; size_t v___x_1410_; 
v___x_1407_ = lean_array_uget_borrowed(v_as_1402_, v_i_1403_);
v___x_1408_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(v_b_1405_, v___x_1407_);
v___x_1409_ = ((size_t)1ULL);
v___x_1410_ = lean_usize_add(v_i_1403_, v___x_1409_);
v_i_1403_ = v___x_1410_;
v_b_1405_ = v___x_1408_;
goto _start;
}
else
{
return v_b_1405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4___boxed(lean_object* v_as_1412_, lean_object* v_i_1413_, lean_object* v_stop_1414_, lean_object* v_b_1415_){
_start:
{
size_t v_i_boxed_1416_; size_t v_stop_boxed_1417_; lean_object* v_res_1418_; 
v_i_boxed_1416_ = lean_unbox_usize(v_i_1413_);
lean_dec(v_i_1413_);
v_stop_boxed_1417_ = lean_unbox_usize(v_stop_1414_);
lean_dec(v_stop_1414_);
v_res_1418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_as_1412_, v_i_boxed_1416_, v_stop_boxed_1417_, v_b_1415_);
lean_dec_ref(v_as_1412_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(lean_object* v_upperBound_1419_, lean_object* v___x_1420_, lean_object* v_op_1421_, lean_object* v_a_1422_, lean_object* v_b_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v___y_1427_; uint8_t v___x_1431_; 
v___x_1431_ = lean_nat_dec_lt(v_a_1422_, v_upperBound_1419_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec(v_a_1422_);
lean_dec_ref(v_op_1421_);
lean_dec_ref(v___x_1420_);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v_b_1423_);
lean_ctor_set(v___x_1432_, 1, v___y_1424_);
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
return v___x_1433_;
}
else
{
if (lean_obj_tag(v_b_1423_) == 0)
{
lean_object* v___x_1434_; 
lean_inc_ref(v___x_1420_);
v___x_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1420_);
v___y_1427_ = v___x_1434_;
goto v___jp_1426_;
}
else
{
lean_object* v_val_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1444_; 
v_val_1435_ = lean_ctor_get(v_b_1423_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_b_1423_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1437_ = v_b_1423_;
v_isShared_1438_ = v_isSharedCheck_1444_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_val_1435_);
lean_dec(v_b_1423_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1444_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1442_; 
lean_inc_ref(v_op_1421_);
v___x_1439_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_1421_);
lean_inc_ref(v___x_1420_);
v___x_1440_ = l_Lean_mkAppB(v___x_1439_, v_val_1435_, v___x_1420_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v___x_1440_);
v___x_1442_ = v___x_1437_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
v___y_1427_ = v___x_1442_;
goto v___jp_1426_;
}
}
}
}
v___jp_1426_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_unsigned_to_nat(1u);
v___x_1429_ = lean_nat_add(v_a_1422_, v___x_1428_);
lean_dec(v_a_1422_);
v_a_1422_ = v___x_1429_;
v_b_1423_ = v___y_1427_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg___boxed(lean_object* v_upperBound_1445_, lean_object* v___x_1446_, lean_object* v_op_1447_, lean_object* v_a_1448_, lean_object* v_b_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1445_, v___x_1446_, v_op_1447_, v_a_1448_, v_b_1449_, v___y_1450_);
lean_dec(v_upperBound_1445_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(lean_object* v_op_1453_, lean_object* v_as_1454_, size_t v_sz_1455_, size_t v_i_1456_, lean_object* v_b_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
uint8_t v___x_1466_; 
v___x_1466_ = lean_usize_dec_lt(v_i_1456_, v_sz_1455_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_dec_ref(v_op_1453_);
v___x_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1467_, 0, v_b_1457_);
lean_ctor_set(v___x_1467_, 1, v___y_1458_);
v___x_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
return v___x_1468_;
}
else
{
lean_object* v_a_1469_; lean_object* v_fst_1470_; lean_object* v_snd_1471_; lean_object* v_varToExpr_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v_a_1469_ = lean_array_uget_borrowed(v_as_1454_, v_i_1456_);
v_fst_1470_ = lean_ctor_get(v_a_1469_, 0);
v_snd_1471_ = lean_ctor_get(v_a_1469_, 1);
v_varToExpr_1472_ = lean_ctor_get(v___y_1458_, 2);
v___x_1473_ = l_Lean_instInhabitedExpr;
v___x_1474_ = lean_unsigned_to_nat(0u);
v___x_1475_ = lean_array_get(v___x_1473_, v_varToExpr_1472_, v_fst_1470_);
lean_inc_ref(v_op_1453_);
v___x_1476_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_snd_1471_, v___x_1475_, v_op_1453_, v___x_1474_, v_b_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v_fst_1478_; lean_object* v_snd_1479_; size_t v___x_1480_; size_t v___x_1481_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1476_, 1);
v_fst_1478_ = lean_ctor_get(v_a_1477_, 0);
lean_inc(v_fst_1478_);
v_snd_1479_ = lean_ctor_get(v_a_1477_, 1);
lean_inc(v_snd_1479_);
lean_dec(v_a_1477_);
v___x_1480_ = ((size_t)1ULL);
v___x_1481_ = lean_usize_add(v_i_1456_, v___x_1480_);
v_i_1456_ = v___x_1481_;
v_b_1457_ = v_fst_1478_;
v___y_1458_ = v_snd_1479_;
goto _start;
}
else
{
lean_dec_ref(v_op_1453_);
return v___x_1476_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1___boxed(lean_object* v_op_1483_, lean_object* v_as_1484_, lean_object* v_sz_1485_, lean_object* v_i_1486_, lean_object* v_b_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
size_t v_sz_boxed_1496_; size_t v_i_boxed_1497_; lean_object* v_res_1498_; 
v_sz_boxed_1496_ = lean_unbox_usize(v_sz_1485_);
lean_dec(v_sz_1485_);
v_i_boxed_1497_ = lean_unbox_usize(v_i_1486_);
lean_dec(v_i_1486_);
v_res_1498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1483_, v_as_1484_, v_sz_boxed_1496_, v_i_boxed_1497_, v_b_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec_ref(v_as_1484_);
return v_res_1498_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(lean_object* v_x1_1499_, lean_object* v_x2_1500_){
_start:
{
lean_object* v_fst_1501_; lean_object* v_fst_1502_; uint8_t v___x_1503_; 
v_fst_1501_ = lean_ctor_get(v_x1_1499_, 0);
v_fst_1502_ = lean_ctor_get(v_x2_1500_, 0);
v___x_1503_ = lean_nat_dec_lt(v_fst_1501_, v_fst_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed(lean_object* v_x1_1504_, lean_object* v_x2_1505_){
_start:
{
uint8_t v_res_1506_; lean_object* v_r_1507_; 
v_res_1506_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v_x1_1504_, v_x2_1505_);
lean_dec_ref(v_x2_1505_);
lean_dec_ref(v_x1_1504_);
v_r_1507_ = lean_box(v_res_1506_);
return v_r_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(lean_object* v_hi_1508_, lean_object* v_pivot_1509_, lean_object* v_as_1510_, lean_object* v_i_1511_, lean_object* v_k_1512_){
_start:
{
uint8_t v___x_1513_; 
v___x_1513_ = lean_nat_dec_lt(v_k_1512_, v_hi_1508_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_dec(v_k_1512_);
v___x_1514_ = lean_array_fswap(v_as_1510_, v_i_1511_, v_hi_1508_);
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v_i_1511_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
return v___x_1515_;
}
else
{
lean_object* v___x_1516_; lean_object* v_fst_1517_; lean_object* v_fst_1518_; uint8_t v___x_1519_; 
v___x_1516_ = lean_array_fget_borrowed(v_as_1510_, v_k_1512_);
v_fst_1517_ = lean_ctor_get(v___x_1516_, 0);
v_fst_1518_ = lean_ctor_get(v_pivot_1509_, 0);
v___x_1519_ = lean_nat_dec_lt(v_fst_1517_, v_fst_1518_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = lean_unsigned_to_nat(1u);
v___x_1521_ = lean_nat_add(v_k_1512_, v___x_1520_);
lean_dec(v_k_1512_);
v_k_1512_ = v___x_1521_;
goto _start;
}
else
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1523_ = lean_array_fswap(v_as_1510_, v_i_1511_, v_k_1512_);
v___x_1524_ = lean_unsigned_to_nat(1u);
v___x_1525_ = lean_nat_add(v_i_1511_, v___x_1524_);
lean_dec(v_i_1511_);
v___x_1526_ = lean_nat_add(v_k_1512_, v___x_1524_);
lean_dec(v_k_1512_);
v_as_1510_ = v___x_1523_;
v_i_1511_ = v___x_1525_;
v_k_1512_ = v___x_1526_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg___boxed(lean_object* v_hi_1528_, lean_object* v_pivot_1529_, lean_object* v_as_1530_, lean_object* v_i_1531_, lean_object* v_k_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1528_, v_pivot_1529_, v_as_1530_, v_i_1531_, v_k_1532_);
lean_dec_ref(v_pivot_1529_);
lean_dec(v_hi_1528_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(lean_object* v_n_1534_, lean_object* v_as_1535_, lean_object* v_lo_1536_, lean_object* v_hi_1537_){
_start:
{
lean_object* v___y_1539_; uint8_t v___x_1549_; 
v___x_1549_ = lean_nat_dec_lt(v_lo_1536_, v_hi_1537_);
if (v___x_1549_ == 0)
{
lean_dec(v_lo_1536_);
return v_as_1535_;
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v_mid_1552_; lean_object* v___y_1554_; lean_object* v___y_1560_; lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1550_ = lean_nat_add(v_lo_1536_, v_hi_1537_);
v___x_1551_ = lean_unsigned_to_nat(1u);
v_mid_1552_ = lean_nat_shiftr(v___x_1550_, v___x_1551_);
lean_dec(v___x_1550_);
v___x_1565_ = lean_array_fget_borrowed(v_as_1535_, v_mid_1552_);
v___x_1566_ = lean_array_fget_borrowed(v_as_1535_, v_lo_1536_);
v___x_1567_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1565_, v___x_1566_);
if (v___x_1567_ == 0)
{
v___y_1560_ = v_as_1535_;
goto v___jp_1559_;
}
else
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_array_fswap(v_as_1535_, v_lo_1536_, v_mid_1552_);
v___y_1560_ = v___x_1568_;
goto v___jp_1559_;
}
v___jp_1553_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1555_ = lean_array_fget_borrowed(v___y_1554_, v_mid_1552_);
v___x_1556_ = lean_array_fget_borrowed(v___y_1554_, v_hi_1537_);
v___x_1557_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
lean_dec(v_mid_1552_);
v___y_1539_ = v___y_1554_;
goto v___jp_1538_;
}
else
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_array_fswap(v___y_1554_, v_mid_1552_, v_hi_1537_);
lean_dec(v_mid_1552_);
v___y_1539_ = v___x_1558_;
goto v___jp_1538_;
}
}
v___jp_1559_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
v___x_1561_ = lean_array_fget_borrowed(v___y_1560_, v_hi_1537_);
v___x_1562_ = lean_array_fget_borrowed(v___y_1560_, v_lo_1536_);
v___x_1563_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1561_, v___x_1562_);
if (v___x_1563_ == 0)
{
v___y_1554_ = v___y_1560_;
goto v___jp_1553_;
}
else
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_array_fswap(v___y_1560_, v_lo_1536_, v_hi_1537_);
v___y_1554_ = v___x_1564_;
goto v___jp_1553_;
}
}
}
v___jp_1538_:
{
lean_object* v_pivot_1540_; lean_object* v___x_1541_; lean_object* v_fst_1542_; lean_object* v_snd_1543_; uint8_t v___x_1544_; 
v_pivot_1540_ = lean_array_fget(v___y_1539_, v_hi_1537_);
lean_inc_n(v_lo_1536_, 2);
v___x_1541_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1537_, v_pivot_1540_, v___y_1539_, v_lo_1536_, v_lo_1536_);
lean_dec(v_pivot_1540_);
v_fst_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_fst_1542_);
v_snd_1543_ = lean_ctor_get(v___x_1541_, 1);
lean_inc(v_snd_1543_);
lean_dec_ref(v___x_1541_);
v___x_1544_ = lean_nat_dec_le(v_hi_1537_, v_fst_1542_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1545_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1534_, v_snd_1543_, v_lo_1536_, v_fst_1542_);
v___x_1546_ = lean_unsigned_to_nat(1u);
v___x_1547_ = lean_nat_add(v_fst_1542_, v___x_1546_);
lean_dec(v_fst_1542_);
v_as_1535_ = v___x_1545_;
v_lo_1536_ = v___x_1547_;
goto _start;
}
else
{
lean_dec(v_fst_1542_);
lean_dec(v_lo_1536_);
return v_snd_1543_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___boxed(lean_object* v_n_1569_, lean_object* v_as_1570_, lean_object* v_lo_1571_, lean_object* v_hi_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1569_, v_as_1570_, v_lo_1571_, v_hi_1572_);
lean_dec(v_hi_1572_);
lean_dec(v_n_1569_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(lean_object* v_coeff_1574_, lean_object* v_op_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v___y_1585_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1603_; lean_object* v_size_1610_; lean_object* v_buckets_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v_size_1610_ = lean_ctor_get(v_coeff_1574_, 0);
v_buckets_1611_ = lean_ctor_get(v_coeff_1574_, 1);
v___x_1612_ = lean_mk_empty_array_with_capacity(v_size_1610_);
v___x_1613_ = lean_unsigned_to_nat(0u);
v___x_1614_ = lean_array_get_size(v_buckets_1611_);
v___x_1615_ = lean_nat_dec_lt(v___x_1613_, v___x_1614_);
if (v___x_1615_ == 0)
{
v___y_1603_ = v___x_1612_;
goto v___jp_1602_;
}
else
{
size_t v___x_1616_; size_t v___x_1617_; lean_object* v___x_1618_; 
v___x_1616_ = ((size_t)0ULL);
v___x_1617_ = lean_usize_of_nat(v___x_1614_);
v___x_1618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_buckets_1611_, v___x_1616_, v___x_1617_, v___x_1612_);
v___y_1603_ = v___x_1618_;
goto v___jp_1602_;
}
v___jp_1584_:
{
lean_object* v_acc_1586_; size_t v_sz_1587_; size_t v___x_1588_; lean_object* v___x_1589_; 
v_acc_1586_ = lean_box(0);
v_sz_1587_ = lean_array_size(v___y_1585_);
v___x_1588_ = ((size_t)0ULL);
v___x_1589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1575_, v___y_1585_, v_sz_1587_, v___x_1588_, v_acc_1586_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
lean_dec_ref(v___y_1585_);
return v___x_1589_;
}
v___jp_1590_:
{
lean_object* v___x_1595_; 
v___x_1595_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v___y_1592_, v___y_1591_, v___y_1593_, v___y_1594_);
lean_dec(v___y_1594_);
lean_dec(v___y_1592_);
v___y_1585_ = v___x_1595_;
goto v___jp_1584_;
}
v___jp_1596_:
{
uint8_t v___x_1601_; 
v___x_1601_ = lean_nat_dec_le(v___y_1600_, v___y_1598_);
if (v___x_1601_ == 0)
{
lean_dec(v___y_1598_);
lean_inc(v___y_1600_);
v___y_1591_ = v___y_1597_;
v___y_1592_ = v___y_1599_;
v___y_1593_ = v___y_1600_;
v___y_1594_ = v___y_1600_;
goto v___jp_1590_;
}
else
{
v___y_1591_ = v___y_1597_;
v___y_1592_ = v___y_1599_;
v___y_1593_ = v___y_1600_;
v___y_1594_ = v___y_1598_;
goto v___jp_1590_;
}
}
v___jp_1602_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; 
v___x_1604_ = lean_array_get_size(v___y_1603_);
v___x_1605_ = lean_unsigned_to_nat(0u);
v___x_1606_ = lean_nat_dec_eq(v___x_1604_, v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1607_ = lean_unsigned_to_nat(1u);
v___x_1608_ = lean_nat_sub(v___x_1604_, v___x_1607_);
v___x_1609_ = lean_nat_dec_le(v___x_1605_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_inc(v___x_1608_);
v___y_1597_ = v___y_1603_;
v___y_1598_ = v___x_1608_;
v___y_1599_ = v___x_1604_;
v___y_1600_ = v___x_1608_;
goto v___jp_1596_;
}
else
{
v___y_1597_ = v___y_1603_;
v___y_1598_ = v___x_1608_;
v___y_1599_ = v___x_1604_;
v___y_1600_ = v___x_1605_;
goto v___jp_1596_;
}
}
else
{
v___y_1585_ = v___y_1603_;
goto v___jp_1584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr___boxed(lean_object* v_coeff_1619_, lean_object* v_op_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_coeff_1619_, v_op_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec_ref(v_coeff_1619_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(lean_object* v_upperBound_1630_, lean_object* v___x_1631_, lean_object* v_op_1632_, lean_object* v_inst_1633_, lean_object* v_R_1634_, lean_object* v_a_1635_, lean_object* v_b_1636_, lean_object* v_c_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1630_, v___x_1631_, v_op_1632_, v_a_1635_, v_b_1636_, v___y_1638_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___boxed(lean_object* v_upperBound_1647_, lean_object* v___x_1648_, lean_object* v_op_1649_, lean_object* v_inst_1650_, lean_object* v_R_1651_, lean_object* v_a_1652_, lean_object* v_b_1653_, lean_object* v_c_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(v_upperBound_1647_, v___x_1648_, v_op_1649_, v_inst_1650_, v_R_1651_, v_a_1652_, v_b_1653_, v_c_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v_upperBound_1647_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(lean_object* v_n_1664_, lean_object* v_as_1665_, lean_object* v_lo_1666_, lean_object* v_hi_1667_, lean_object* v_w_1668_, lean_object* v_hlo_1669_, lean_object* v_hhi_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1664_, v_as_1665_, v_lo_1666_, v_hi_1667_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___boxed(lean_object* v_n_1672_, lean_object* v_as_1673_, lean_object* v_lo_1674_, lean_object* v_hi_1675_, lean_object* v_w_1676_, lean_object* v_hlo_1677_, lean_object* v_hhi_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(v_n_1672_, v_as_1673_, v_lo_1674_, v_hi_1675_, v_w_1676_, v_hlo_1677_, v_hhi_1678_);
lean_dec(v_hi_1675_);
lean_dec(v_n_1672_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(lean_object* v_n_1680_, lean_object* v_lo_1681_, lean_object* v_hi_1682_, lean_object* v_hhi_1683_, lean_object* v_pivot_1684_, lean_object* v_as_1685_, lean_object* v_i_1686_, lean_object* v_k_1687_, lean_object* v_ilo_1688_, lean_object* v_ik_1689_, lean_object* v_w_1690_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1682_, v_pivot_1684_, v_as_1685_, v_i_1686_, v_k_1687_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___boxed(lean_object* v_n_1692_, lean_object* v_lo_1693_, lean_object* v_hi_1694_, lean_object* v_hhi_1695_, lean_object* v_pivot_1696_, lean_object* v_as_1697_, lean_object* v_i_1698_, lean_object* v_k_1699_, lean_object* v_ilo_1700_, lean_object* v_ik_1701_, lean_object* v_w_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(v_n_1692_, v_lo_1693_, v_hi_1694_, v_hhi_1695_, v_pivot_1696_, v_as_1697_, v_i_1698_, v_k_1699_, v_ilo_1700_, v_ik_1701_, v_w_1702_);
lean_dec_ref(v_pivot_1696_);
lean_dec(v_hi_1694_);
lean_dec(v_lo_1693_);
lean_dec(v_n_1692_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(lean_object* v_e_1704_, lean_object* v___y_1705_){
_start:
{
uint8_t v___x_1707_; 
v___x_1707_ = l_Lean_Expr_hasMVar(v_e_1704_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; 
v___x_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1708_, 0, v_e_1704_);
return v___x_1708_;
}
else
{
lean_object* v___x_1709_; lean_object* v_mctx_1710_; lean_object* v___x_1711_; lean_object* v_fst_1712_; lean_object* v_snd_1713_; lean_object* v___x_1714_; lean_object* v_cache_1715_; lean_object* v_zetaDeltaFVarIds_1716_; lean_object* v_postponed_1717_; lean_object* v_diag_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1727_; 
v___x_1709_ = lean_st_ref_get(v___y_1705_);
v_mctx_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc_ref(v_mctx_1710_);
lean_dec(v___x_1709_);
v___x_1711_ = l_Lean_instantiateMVarsCore(v_mctx_1710_, v_e_1704_);
v_fst_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_fst_1712_);
v_snd_1713_ = lean_ctor_get(v___x_1711_, 1);
lean_inc(v_snd_1713_);
lean_dec_ref(v___x_1711_);
v___x_1714_ = lean_st_ref_take(v___y_1705_);
v_cache_1715_ = lean_ctor_get(v___x_1714_, 1);
v_zetaDeltaFVarIds_1716_ = lean_ctor_get(v___x_1714_, 2);
v_postponed_1717_ = lean_ctor_get(v___x_1714_, 3);
v_diag_1718_ = lean_ctor_get(v___x_1714_, 4);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1727_ == 0)
{
lean_object* v_unused_1728_; 
v_unused_1728_ = lean_ctor_get(v___x_1714_, 0);
lean_dec(v_unused_1728_);
v___x_1720_ = v___x_1714_;
v_isShared_1721_ = v_isSharedCheck_1727_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_diag_1718_);
lean_inc(v_postponed_1717_);
lean_inc(v_zetaDeltaFVarIds_1716_);
lean_inc(v_cache_1715_);
lean_dec(v___x_1714_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1727_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v_snd_1713_);
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_snd_1713_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_cache_1715_);
lean_ctor_set(v_reuseFailAlloc_1726_, 2, v_zetaDeltaFVarIds_1716_);
lean_ctor_set(v_reuseFailAlloc_1726_, 3, v_postponed_1717_);
lean_ctor_set(v_reuseFailAlloc_1726_, 4, v_diag_1718_);
v___x_1723_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = lean_st_ref_put(v___y_1705_, v___x_1723_);
v___x_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1725_, 0, v_fst_1712_);
return v___x_1725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg___boxed(lean_object* v_e_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1729_, v___y_1730_);
lean_dec(v___y_1730_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(lean_object* v_e_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1733_, v___y_1735_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___boxed(lean_object* v_e_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(v_e_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(lean_object* v_x_1747_, lean_object* v_y_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_Meta_mkEq(v_x_1747_, v_y_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1777_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1757_ = v___x_1754_;
v_isShared_1758_ = v_isSharedCheck_1777_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1777_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
lean_ctor_set_tag(v___x_1757_, 1);
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
uint8_t v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = 0;
v___x_1762_ = lean_box(0);
v___x_1763_ = l_Lean_Meta_mkFreshExprMVar(v___x_1760_, v___x_1761_, v___x_1762_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
v___x_1765_ = l_Lean_Expr_mvarId_x21(v_a_1764_);
v___x_1766_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v___x_1765_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v___x_1767_; 
lean_dec_ref_known(v___x_1766_, 1);
v___x_1767_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_a_1764_, v_a_1750_);
return v___x_1767_;
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec(v_a_1764_);
v_a_1768_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1766_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1766_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
else
{
return v___x_1763_;
}
}
}
}
else
{
return v___x_1754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC___boxed(lean_object* v_x_1778_, lean_object* v_y_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v_x_1778_, v_y_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
return v_res_1785_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = lean_unsigned_to_nat(32u);
v___x_1787_ = lean_mk_empty_array_with_capacity(v___x_1786_);
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
return v___x_1788_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1789_ = ((size_t)5ULL);
v___x_1790_ = lean_unsigned_to_nat(0u);
v___x_1791_ = lean_unsigned_to_nat(32u);
v___x_1792_ = lean_mk_empty_array_with_capacity(v___x_1791_);
v___x_1793_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0);
v___x_1794_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
lean_ctor_set(v___x_1794_, 1, v___x_1792_);
lean_ctor_set(v___x_1794_, 2, v___x_1790_);
lean_ctor_set(v___x_1794_, 3, v___x_1790_);
lean_ctor_set_usize(v___x_1794_, 4, v___x_1789_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(lean_object* v___y_1795_){
_start:
{
lean_object* v___x_1797_; lean_object* v_traceState_1798_; lean_object* v_traces_1799_; lean_object* v___x_1800_; lean_object* v_traceState_1801_; lean_object* v_env_1802_; lean_object* v_nextMacroScope_1803_; lean_object* v_ngen_1804_; lean_object* v_auxDeclNGen_1805_; lean_object* v_cache_1806_; lean_object* v_messages_1807_; lean_object* v_infoState_1808_; lean_object* v_snapshotTasks_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1828_; 
v___x_1797_ = lean_st_ref_get(v___y_1795_);
v_traceState_1798_ = lean_ctor_get(v___x_1797_, 4);
lean_inc_ref(v_traceState_1798_);
lean_dec(v___x_1797_);
v_traces_1799_ = lean_ctor_get(v_traceState_1798_, 0);
lean_inc_ref(v_traces_1799_);
lean_dec_ref(v_traceState_1798_);
v___x_1800_ = lean_st_ref_take(v___y_1795_);
v_traceState_1801_ = lean_ctor_get(v___x_1800_, 4);
v_env_1802_ = lean_ctor_get(v___x_1800_, 0);
v_nextMacroScope_1803_ = lean_ctor_get(v___x_1800_, 1);
v_ngen_1804_ = lean_ctor_get(v___x_1800_, 2);
v_auxDeclNGen_1805_ = lean_ctor_get(v___x_1800_, 3);
v_cache_1806_ = lean_ctor_get(v___x_1800_, 5);
v_messages_1807_ = lean_ctor_get(v___x_1800_, 6);
v_infoState_1808_ = lean_ctor_get(v___x_1800_, 7);
v_snapshotTasks_1809_ = lean_ctor_get(v___x_1800_, 8);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1811_ = v___x_1800_;
v_isShared_1812_ = v_isSharedCheck_1828_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_snapshotTasks_1809_);
lean_inc(v_infoState_1808_);
lean_inc(v_messages_1807_);
lean_inc(v_cache_1806_);
lean_inc(v_traceState_1801_);
lean_inc(v_auxDeclNGen_1805_);
lean_inc(v_ngen_1804_);
lean_inc(v_nextMacroScope_1803_);
lean_inc(v_env_1802_);
lean_dec(v___x_1800_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1828_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
uint64_t v_tid_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1826_; 
v_tid_1813_ = lean_ctor_get_uint64(v_traceState_1801_, sizeof(void*)*1);
v_isSharedCheck_1826_ = !lean_is_exclusive(v_traceState_1801_);
if (v_isSharedCheck_1826_ == 0)
{
lean_object* v_unused_1827_; 
v_unused_1827_ = lean_ctor_get(v_traceState_1801_, 0);
lean_dec(v_unused_1827_);
v___x_1815_ = v_traceState_1801_;
v_isShared_1816_ = v_isSharedCheck_1826_;
goto v_resetjp_1814_;
}
else
{
lean_dec(v_traceState_1801_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1826_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1817_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1817_);
v___x_1819_ = v___x_1815_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1817_);
lean_ctor_set_uint64(v_reuseFailAlloc_1825_, sizeof(void*)*1, v_tid_1813_);
v___x_1819_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1821_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 4, v___x_1819_);
v___x_1821_ = v___x_1811_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_env_1802_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_nextMacroScope_1803_);
lean_ctor_set(v_reuseFailAlloc_1824_, 2, v_ngen_1804_);
lean_ctor_set(v_reuseFailAlloc_1824_, 3, v_auxDeclNGen_1805_);
lean_ctor_set(v_reuseFailAlloc_1824_, 4, v___x_1819_);
lean_ctor_set(v_reuseFailAlloc_1824_, 5, v_cache_1806_);
lean_ctor_set(v_reuseFailAlloc_1824_, 6, v_messages_1807_);
lean_ctor_set(v_reuseFailAlloc_1824_, 7, v_infoState_1808_);
lean_ctor_set(v_reuseFailAlloc_1824_, 8, v_snapshotTasks_1809_);
v___x_1821_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = lean_st_ref_put(v___y_1795_, v___x_1821_);
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v_traces_1799_);
return v___x_1823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___boxed(lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1829_);
lean_dec(v___y_1829_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1840_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
return v_res_1853_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(lean_object* v_opts_1854_, lean_object* v_opt_1855_){
_start:
{
lean_object* v_name_1856_; lean_object* v_defValue_1857_; lean_object* v_map_1858_; lean_object* v___x_1859_; 
v_name_1856_ = lean_ctor_get(v_opt_1855_, 0);
v_defValue_1857_ = lean_ctor_get(v_opt_1855_, 1);
v_map_1858_ = lean_ctor_get(v_opts_1854_, 0);
v___x_1859_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1858_, v_name_1856_);
if (lean_obj_tag(v___x_1859_) == 0)
{
uint8_t v___x_1860_; 
v___x_1860_ = lean_unbox(v_defValue_1857_);
return v___x_1860_;
}
else
{
lean_object* v_val_1861_; 
v_val_1861_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_val_1861_);
lean_dec_ref_known(v___x_1859_, 1);
if (lean_obj_tag(v_val_1861_) == 1)
{
uint8_t v_v_1862_; 
v_v_1862_ = lean_ctor_get_uint8(v_val_1861_, 0);
lean_dec_ref_known(v_val_1861_, 0);
return v_v_1862_;
}
else
{
uint8_t v___x_1863_; 
lean_dec(v_val_1861_);
v___x_1863_ = lean_unbox(v_defValue_1857_);
return v___x_1863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object* v_opts_1864_, lean_object* v_opt_1865_){
_start:
{
uint8_t v_res_1866_; lean_object* v_r_1867_; 
v_res_1866_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_1864_, v_opt_1865_);
lean_dec_ref(v_opt_1865_);
lean_dec_ref(v_opts_1864_);
v_r_1867_ = lean_box(v_res_1866_);
return v_r_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(lean_object* v_cls_1868_, lean_object* v_____do__lift_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v_options_1880_; uint8_t v_hasTrace_1881_; 
v_options_1880_ = lean_ctor_get(v___y_1877_, 1);
v_hasTrace_1881_ = lean_ctor_get_uint8(v_options_1880_, sizeof(void*)*1);
if (v_hasTrace_1881_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_dec(v_cls_1868_);
v___x_1882_ = lean_box(v_hasTrace_1881_);
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
return v___x_1883_;
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1884_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_1885_ = l_Lean_Name_append(v___x_1884_, v_cls_1868_);
v___x_1886_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_1869_, v_options_1880_, v___x_1885_);
lean_dec(v___x_1885_);
v___x_1887_ = lean_box(v___x_1886_);
v___x_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
return v___x_1888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0___boxed(lean_object* v_cls_1889_, lean_object* v_____do__lift_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_1889_, v_____do__lift_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v_____do__lift_1890_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1(lean_object* v___x_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Lean_mkAppB(v___x_1902_, v___y_1903_, v___y_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(lean_object* v_val_1906_, lean_object* v_lhs_1907_, lean_object* v_rhs_1908_, lean_object* v_P_1909_, uint8_t v___x_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v___x_1919_; 
lean_inc_ref(v_lhs_1907_);
lean_inc_ref(v_val_1906_);
v___x_1919_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1906_, v_lhs_1907_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v_fst_1921_; lean_object* v_snd_1922_; lean_object* v___x_1923_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v_fst_1921_ = lean_ctor_get(v_a_1920_, 0);
lean_inc(v_fst_1921_);
v_snd_1922_ = lean_ctor_get(v_a_1920_, 1);
lean_inc(v_snd_1922_);
lean_dec(v_a_1920_);
lean_inc_ref(v_rhs_1908_);
lean_inc_ref(v_val_1906_);
v___x_1923_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1906_, v_rhs_1908_, v_snd_1922_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v_fst_1925_; lean_object* v_snd_1926_; lean_object* v___x_1927_; lean_object* v_a_1928_; lean_object* v_fst_1929_; lean_object* v_snd_1930_; lean_object* v_common_1931_; lean_object* v_x_1932_; lean_object* v_y_1933_; lean_object* v___x_1934_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v_fst_1925_ = lean_ctor_get(v_a_1924_, 0);
lean_inc(v_fst_1925_);
v_snd_1926_ = lean_ctor_get(v_a_1924_, 1);
lean_inc(v_snd_1926_);
lean_dec(v_a_1924_);
v___x_1927_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_1921_, v_fst_1925_, v_snd_1926_);
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref(v___x_1927_);
v_fst_1929_ = lean_ctor_get(v_a_1928_, 0);
lean_inc(v_fst_1929_);
v_snd_1930_ = lean_ctor_get(v_a_1928_, 1);
lean_inc(v_snd_1930_);
lean_dec(v_a_1928_);
v_common_1931_ = lean_ctor_get(v_fst_1929_, 0);
lean_inc_ref(v_common_1931_);
v_x_1932_ = lean_ctor_get(v_fst_1929_, 1);
lean_inc_ref(v_x_1932_);
v_y_1933_ = lean_ctor_get(v_fst_1929_, 2);
lean_inc_ref(v_y_1933_);
lean_dec(v_fst_1929_);
lean_inc_ref(v_val_1906_);
v___x_1934_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_1931_, v_val_1906_, v_snd_1930_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
lean_dec_ref(v_common_1931_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v_fst_1936_; lean_object* v_snd_1937_; lean_object* v___x_1938_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v___x_1934_, 1);
v_fst_1936_ = lean_ctor_get(v_a_1935_, 0);
lean_inc(v_fst_1936_);
v_snd_1937_ = lean_ctor_get(v_a_1935_, 1);
lean_inc(v_snd_1937_);
lean_dec(v_a_1935_);
lean_inc_ref(v_val_1906_);
v___x_1938_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_1932_, v_val_1906_, v_snd_1937_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
lean_dec_ref(v_x_1932_);
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
lean_inc_ref(v_val_1906_);
v___x_1942_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_1933_, v_val_1906_, v_snd_1941_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
lean_dec_ref(v_y_1933_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_2007_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_2007_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_2007_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v_fst_1947_; lean_object* v_snd_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_2006_; 
v_fst_1947_ = lean_ctor_get(v_a_1943_, 0);
v_snd_1948_ = lean_ctor_get(v_a_1943_, 1);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_a_1943_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1950_ = v_a_1943_;
v_isShared_1951_ = v_isSharedCheck_2006_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_snd_1948_);
lean_inc(v_fst_1947_);
lean_dec(v_a_1943_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_2006_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___x_1996_; lean_object* v___f_1997_; lean_object* v___y_1999_; lean_object* v___x_2003_; 
lean_inc_ref(v_val_1906_);
v___x_1996_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_1906_);
v___f_1997_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_1997_, 0, v___x_1996_);
lean_inc(v_fst_1936_);
lean_inc_ref(v___f_1997_);
v___x_2003_ = l_Option_merge___redArg(v___f_1997_, v_fst_1936_, v_fst_1940_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v___x_2004_; 
lean_inc_ref(v_val_1906_);
v___x_2004_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1906_);
v___y_1999_ = v___x_2004_;
goto v___jp_1998_;
}
else
{
lean_object* v_val_2005_; 
v_val_2005_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_val_2005_);
lean_dec_ref_known(v___x_2003_, 1);
v___y_1999_ = v_val_2005_;
goto v___jp_1998_;
}
v___jp_1952_:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
lean_inc_ref(v_P_1909_);
v___x_1955_ = l_Lean_mkAppB(v_P_1909_, v_lhs_1907_, v_rhs_1908_);
v___x_1956_ = l_Lean_mkAppB(v_P_1909_, v___y_1953_, v___y_1954_);
v___x_1957_ = lean_expr_eqv(v___x_1955_, v___x_1956_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; 
lean_del_object(v___x_1945_);
lean_inc_ref(v___x_1956_);
v___x_1958_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_1955_, v___x_1956_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1960_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1958_, 1);
v___x_1960_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1956_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1972_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_1972_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1972_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1965_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1965_, 0, v_a_1961_);
lean_ctor_set(v___x_1965_, 1, v_a_1959_);
lean_ctor_set_uint8(v___x_1965_, sizeof(void*)*2, v___x_1957_);
lean_ctor_set_uint8(v___x_1965_, sizeof(void*)*2 + 1, v___x_1957_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1965_);
v___x_1967_ = v___x_1950_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_snd_1948_);
v___x_1967_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1969_; 
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1967_);
v___x_1969_ = v___x_1963_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_dec(v_a_1959_);
lean_del_object(v___x_1950_);
lean_dec(v_snd_1948_);
v_a_1973_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1960_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1960_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_dec_ref(v___x_1956_);
lean_del_object(v___x_1950_);
lean_dec(v_snd_1948_);
v_a_1981_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1958_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1958_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
else
{
lean_object* v___x_1989_; lean_object* v___x_1991_; 
lean_dec_ref(v___x_1956_);
lean_dec_ref(v___x_1955_);
v___x_1989_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1989_, 0, v___x_1910_);
lean_ctor_set_uint8(v___x_1989_, 1, v___x_1910_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1989_);
v___x_1991_ = v___x_1950_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_snd_1948_);
v___x_1991_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1993_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1991_);
v___x_1993_ = v___x_1945_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
v___jp_1998_:
{
lean_object* v___x_2000_; 
v___x_2000_ = l_Option_merge___redArg(v___f_1997_, v_fst_1936_, v_fst_1947_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1906_);
v___y_1953_ = v___y_1999_;
v___y_1954_ = v___x_2001_;
goto v___jp_1952_;
}
else
{
lean_object* v_val_2002_; 
lean_dec_ref(v_val_1906_);
v_val_2002_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_val_2002_);
lean_dec_ref_known(v___x_2000_, 1);
v___y_1953_ = v___y_1999_;
v___y_1954_ = v_val_2002_;
goto v___jp_1952_;
}
}
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec(v_fst_1940_);
lean_dec(v_fst_1936_);
lean_dec_ref(v_P_1909_);
lean_dec_ref(v_rhs_1908_);
lean_dec_ref(v_lhs_1907_);
lean_dec_ref(v_val_1906_);
v_a_2008_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1942_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1942_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec(v_fst_1936_);
lean_dec_ref(v_y_1933_);
lean_dec_ref(v_P_1909_);
lean_dec_ref(v_rhs_1908_);
lean_dec_ref(v_lhs_1907_);
lean_dec_ref(v_val_1906_);
v_a_2016_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_1938_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_1938_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec_ref(v_y_1933_);
lean_dec_ref(v_x_1932_);
lean_dec_ref(v_P_1909_);
lean_dec_ref(v_rhs_1908_);
lean_dec_ref(v_lhs_1907_);
lean_dec_ref(v_val_1906_);
v_a_2024_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_1934_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_1934_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec(v_fst_1921_);
lean_dec_ref(v_P_1909_);
lean_dec_ref(v_rhs_1908_);
lean_dec_ref(v_lhs_1907_);
lean_dec_ref(v_val_1906_);
v_a_2032_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_1923_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_1923_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec_ref(v_P_1909_);
lean_dec_ref(v_rhs_1908_);
lean_dec_ref(v_lhs_1907_);
lean_dec_ref(v_val_1906_);
v_a_2040_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_1919_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_1919_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object* v_val_2048_, lean_object* v_lhs_2049_, lean_object* v_rhs_2050_, lean_object* v_P_2051_, lean_object* v___x_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
uint8_t v___x_187301__boxed_2061_; lean_object* v_res_2062_; 
v___x_187301__boxed_2061_ = lean_unbox(v___x_2052_);
v_res_2062_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(v_val_2048_, v_lhs_2049_, v_rhs_2050_, v_P_2051_, v___x_187301__boxed_2061_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
return v_res_2062_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_2065_ = l_Lean_stringToMessageData(v___x_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(lean_object* v_x_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1);
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object* v_x_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(v_x_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v_x_2079_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object* v_cls_2091_, lean_object* v_msg_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v_ref_2098_; lean_object* v___x_2099_; lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2144_; 
v_ref_2098_ = lean_ctor_get(v___y_2095_, 4);
v___x_2099_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2102_ = v___x_2099_;
v_isShared_2103_ = v_isSharedCheck_2144_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2099_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2144_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2104_; lean_object* v_traceState_2105_; lean_object* v_env_2106_; lean_object* v_nextMacroScope_2107_; lean_object* v_ngen_2108_; lean_object* v_auxDeclNGen_2109_; lean_object* v_cache_2110_; lean_object* v_messages_2111_; lean_object* v_infoState_2112_; lean_object* v_snapshotTasks_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2143_; 
v___x_2104_ = lean_st_ref_take(v___y_2096_);
v_traceState_2105_ = lean_ctor_get(v___x_2104_, 4);
v_env_2106_ = lean_ctor_get(v___x_2104_, 0);
v_nextMacroScope_2107_ = lean_ctor_get(v___x_2104_, 1);
v_ngen_2108_ = lean_ctor_get(v___x_2104_, 2);
v_auxDeclNGen_2109_ = lean_ctor_get(v___x_2104_, 3);
v_cache_2110_ = lean_ctor_get(v___x_2104_, 5);
v_messages_2111_ = lean_ctor_get(v___x_2104_, 6);
v_infoState_2112_ = lean_ctor_get(v___x_2104_, 7);
v_snapshotTasks_2113_ = lean_ctor_get(v___x_2104_, 8);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2115_ = v___x_2104_;
v_isShared_2116_ = v_isSharedCheck_2143_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_snapshotTasks_2113_);
lean_inc(v_infoState_2112_);
lean_inc(v_messages_2111_);
lean_inc(v_cache_2110_);
lean_inc(v_traceState_2105_);
lean_inc(v_auxDeclNGen_2109_);
lean_inc(v_ngen_2108_);
lean_inc(v_nextMacroScope_2107_);
lean_inc(v_env_2106_);
lean_dec(v___x_2104_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2143_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
uint64_t v_tid_2117_; lean_object* v_traces_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2142_; 
v_tid_2117_ = lean_ctor_get_uint64(v_traceState_2105_, sizeof(void*)*1);
v_traces_2118_ = lean_ctor_get(v_traceState_2105_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_traceState_2105_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2120_ = v_traceState_2105_;
v_isShared_2121_ = v_isSharedCheck_2142_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_traces_2118_);
lean_dec(v_traceState_2105_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2142_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; double v___x_2123_; uint8_t v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2122_ = lean_box(0);
v___x_2123_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_2124_ = 0;
v___x_2125_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_2126_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2126_, 0, v_cls_2091_);
lean_ctor_set(v___x_2126_, 1, v___x_2122_);
lean_ctor_set(v___x_2126_, 2, v___x_2125_);
lean_ctor_set_float(v___x_2126_, sizeof(void*)*3, v___x_2123_);
lean_ctor_set_float(v___x_2126_, sizeof(void*)*3 + 8, v___x_2123_);
lean_ctor_set_uint8(v___x_2126_, sizeof(void*)*3 + 16, v___x_2124_);
v___x_2127_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_2128_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2126_);
lean_ctor_set(v___x_2128_, 1, v_a_2100_);
lean_ctor_set(v___x_2128_, 2, v___x_2127_);
lean_inc(v_ref_2098_);
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v_ref_2098_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = l_Lean_PersistentArray_push___redArg(v_traces_2118_, v___x_2129_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2130_);
v___x_2132_ = v___x_2120_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2130_);
lean_ctor_set_uint64(v_reuseFailAlloc_2141_, sizeof(void*)*1, v_tid_2117_);
v___x_2132_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2134_; 
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 4, v___x_2132_);
v___x_2134_ = v___x_2115_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_env_2106_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v_nextMacroScope_2107_);
lean_ctor_set(v_reuseFailAlloc_2140_, 2, v_ngen_2108_);
lean_ctor_set(v_reuseFailAlloc_2140_, 3, v_auxDeclNGen_2109_);
lean_ctor_set(v_reuseFailAlloc_2140_, 4, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2140_, 5, v_cache_2110_);
lean_ctor_set(v_reuseFailAlloc_2140_, 6, v_messages_2111_);
lean_ctor_set(v_reuseFailAlloc_2140_, 7, v_infoState_2112_);
lean_ctor_set(v_reuseFailAlloc_2140_, 8, v_snapshotTasks_2113_);
v___x_2134_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2135_ = lean_st_ref_put(v___y_2096_, v___x_2134_);
v___x_2136_ = lean_box(0);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2136_);
v___x_2138_ = v___x_2102_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2136_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object* v_cls_2145_, lean_object* v_msg_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2145_, v_msg_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
return v_res_2152_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2155_ = l_Lean_stringToMessageData(v___x_2154_);
return v___x_2155_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3(void){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2));
v___x_2158_ = l_Lean_stringToMessageData(v___x_2157_);
return v___x_2158_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4));
v___x_2161_ = l_Lean_stringToMessageData(v___x_2160_);
return v___x_2161_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2162_ = lean_box(0);
v___x_2163_ = lean_unsigned_to_nat(16u);
v___x_2164_ = lean_mk_array(v___x_2163_, v___x_2162_);
return v___x_2164_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6);
v___x_2166_ = lean_unsigned_to_nat(0u);
v___x_2167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
lean_ctor_set(v___x_2167_, 1, v___x_2165_);
return v___x_2167_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9));
v___x_2172_ = l_Lean_stringToMessageData(v___x_2171_);
return v___x_2172_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11));
v___x_2175_ = l_Lean_stringToMessageData(v___x_2174_);
return v___x_2175_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13));
v___x_2178_ = l_Lean_stringToMessageData(v___x_2177_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(lean_object* v_lhs_2179_, lean_object* v_rhs_2180_, uint8_t v___x_2181_, lean_object* v___f_2182_, lean_object* v_cls_2183_, lean_object* v_P_2184_, lean_object* v_____r_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v___x_2205_; 
lean_inc_ref(v_lhs_2179_);
v___x_2205_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2179_);
if (lean_obj_tag(v___x_2205_) == 1)
{
lean_object* v_val_2206_; lean_object* v___x_2207_; 
v_val_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_val_2206_);
lean_dec_ref_known(v___x_2205_, 1);
lean_inc_ref(v_rhs_2180_);
v___x_2207_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2180_);
if (lean_obj_tag(v___x_2207_) == 1)
{
lean_object* v_val_2208_; uint8_t v___x_2248_; 
v_val_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_val_2208_);
lean_dec_ref_known(v___x_2207_, 1);
v___x_2248_ = lean_expr_eqv(v_val_2206_, v_val_2208_);
if (v___x_2248_ == 0)
{
lean_dec_ref(v_P_2184_);
goto v___jp_2209_;
}
else
{
if (v___x_2181_ == 0)
{
lean_object* v_options_2249_; lean_object* v_toCold_2250_; uint8_t v_hasTrace_2251_; lean_object* v___x_2252_; lean_object* v___f_2253_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; 
lean_dec(v_val_2208_);
lean_dec_ref(v___f_2182_);
v_options_2249_ = lean_ctor_get(v___y_2193_, 1);
v_toCold_2250_ = lean_ctor_get(v___y_2193_, 0);
v_hasTrace_2251_ = lean_ctor_get_uint8(v_options_2249_, sizeof(void*)*1);
v___x_2252_ = lean_box(v___x_2181_);
lean_inc(v_val_2206_);
v___f_2253_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 13, 5);
lean_closure_set(v___f_2253_, 0, v_val_2206_);
lean_closure_set(v___f_2253_, 1, v_lhs_2179_);
lean_closure_set(v___f_2253_, 2, v_rhs_2180_);
lean_closure_set(v___f_2253_, 3, v_P_2184_);
lean_closure_set(v___f_2253_, 4, v___x_2252_);
if (v_hasTrace_2251_ == 0)
{
lean_dec(v_cls_2183_);
v___y_2255_ = v___y_2189_;
v___y_2256_ = v___y_2190_;
v___y_2257_ = v___y_2191_;
v___y_2258_ = v___y_2192_;
v___y_2259_ = v___y_2193_;
v___y_2260_ = v___y_2194_;
goto v___jp_2254_;
}
else
{
lean_object* v_inheritedTraceOptions_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; 
v_inheritedTraceOptions_2265_ = lean_ctor_get(v_toCold_2250_, 4);
v___x_2266_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2183_);
v___x_2267_ = l_Lean_Name_append(v___x_2266_, v_cls_2183_);
v___x_2268_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2265_, v_options_2249_, v___x_2267_);
lean_dec(v___x_2267_);
if (v___x_2268_ == 0)
{
lean_dec(v_cls_2183_);
v___y_2255_ = v___y_2189_;
v___y_2256_ = v___y_2190_;
v___y_2257_ = v___y_2191_;
v___y_2258_ = v___y_2192_;
v___y_2259_ = v___y_2193_;
v___y_2260_ = v___y_2194_;
goto v___jp_2254_;
}
else
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2269_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10);
lean_inc(v_val_2206_);
v___x_2270_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2206_);
v___x_2271_ = l_Lean_MessageData_ofExpr(v___x_2270_);
v___x_2272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2269_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
v___x_2273_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12);
v___x_2274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2272_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
v___x_2275_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2183_, v___x_2274_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_dec_ref_known(v___x_2275_, 1);
v___y_2255_ = v___y_2189_;
v___y_2256_ = v___y_2190_;
v___y_2257_ = v___y_2191_;
v___y_2258_ = v___y_2192_;
v___y_2259_ = v___y_2193_;
v___y_2260_ = v___y_2194_;
goto v___jp_2254_;
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec_ref(v___f_2253_);
lean_dec(v_val_2206_);
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2275_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2275_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
v___jp_2254_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2261_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7);
v___x_2262_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8));
v___x_2263_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2263_, 0, v_val_2206_);
lean_ctor_set(v___x_2263_, 1, v___x_2261_);
lean_ctor_set(v___x_2263_, 2, v___x_2262_);
v___x_2264_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___f_2253_, v___x_2263_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
return v___x_2264_;
}
}
else
{
lean_dec_ref(v_P_2184_);
goto v___jp_2209_;
}
}
v___jp_2209_:
{
lean_object* v_toCold_2210_; lean_object* v_inheritedTraceOptions_2211_; lean_object* v___x_2212_; 
v_toCold_2210_ = lean_ctor_get(v___y_2193_, 0);
v_inheritedTraceOptions_2211_ = lean_ctor_get(v_toCold_2210_, 4);
lean_inc(v___y_2194_);
lean_inc_ref(v___y_2193_);
lean_inc(v___y_2192_);
lean_inc_ref(v___y_2191_);
lean_inc(v___y_2190_);
lean_inc_ref(v___y_2189_);
lean_inc(v___y_2188_);
lean_inc_ref(v___y_2187_);
lean_inc(v___y_2186_);
lean_inc_ref(v_inheritedTraceOptions_2211_);
v___x_2212_ = lean_apply_11(v___f_2182_, v_inheritedTraceOptions_2211_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, lean_box(0));
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; uint8_t v___x_2214_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2213_);
lean_dec_ref_known(v___x_2212_, 1);
v___x_2214_ = lean_unbox(v_a_2213_);
lean_dec(v_a_2213_);
if (v___x_2214_ == 0)
{
lean_dec(v_val_2208_);
lean_dec(v_val_2206_);
lean_dec(v_cls_2183_);
lean_dec_ref(v_rhs_2180_);
lean_dec_ref(v_lhs_2179_);
goto v___jp_2196_;
}
else
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2215_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1);
v___x_2216_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2206_);
v___x_2217_ = l_Lean_MessageData_ofExpr(v___x_2216_);
v___x_2218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2215_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
v___x_2219_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3);
v___x_2220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2218_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
v___x_2221_ = l_Lean_indentExpr(v_lhs_2179_);
v___x_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2220_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5);
v___x_2224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2222_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
v___x_2225_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2208_);
v___x_2226_ = l_Lean_MessageData_ofExpr(v___x_2225_);
v___x_2227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2224_);
lean_ctor_set(v___x_2227_, 1, v___x_2226_);
v___x_2228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
lean_ctor_set(v___x_2228_, 1, v___x_2219_);
v___x_2229_ = l_Lean_indentExpr(v_rhs_2180_);
v___x_2230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2228_);
lean_ctor_set(v___x_2230_, 1, v___x_2229_);
v___x_2231_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2183_, v___x_2230_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_dec_ref_known(v___x_2231_, 1);
goto v___jp_2196_;
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v_val_2208_);
lean_dec(v_val_2206_);
lean_dec(v_cls_2183_);
lean_dec_ref(v_rhs_2180_);
lean_dec_ref(v_lhs_2179_);
v_a_2240_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2212_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2212_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
}
else
{
lean_object* v_toCold_2284_; lean_object* v_inheritedTraceOptions_2285_; lean_object* v___x_2286_; 
lean_dec(v___x_2207_);
lean_dec(v_val_2206_);
lean_dec_ref(v_P_2184_);
lean_dec_ref(v_lhs_2179_);
v_toCold_2284_ = lean_ctor_get(v___y_2193_, 0);
v_inheritedTraceOptions_2285_ = lean_ctor_get(v_toCold_2284_, 4);
lean_inc(v___y_2194_);
lean_inc_ref(v___y_2193_);
lean_inc(v___y_2192_);
lean_inc_ref(v___y_2191_);
lean_inc(v___y_2190_);
lean_inc_ref(v___y_2189_);
lean_inc(v___y_2188_);
lean_inc_ref(v___y_2187_);
lean_inc(v___y_2186_);
lean_inc_ref(v_inheritedTraceOptions_2285_);
v___x_2286_ = lean_apply_11(v___f_2182_, v_inheritedTraceOptions_2285_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, lean_box(0));
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; uint8_t v___x_2288_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref_known(v___x_2286_, 1);
v___x_2288_ = lean_unbox(v_a_2287_);
lean_dec(v_a_2287_);
if (v___x_2288_ == 0)
{
lean_dec(v_cls_2183_);
lean_dec_ref(v_rhs_2180_);
goto v___jp_2199_;
}
else
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2289_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_2290_ = l_Lean_indentExpr(v_rhs_2180_);
v___x_2291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2289_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2183_, v___x_2291_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_dec_ref_known(v___x_2292_, 1);
goto v___jp_2199_;
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2292_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2292_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
lean_dec(v_cls_2183_);
lean_dec_ref(v_rhs_2180_);
v_a_2301_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2286_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2286_);
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
lean_object* v_toCold_2309_; lean_object* v_inheritedTraceOptions_2310_; lean_object* v___x_2311_; 
lean_dec(v___x_2205_);
lean_dec_ref(v_P_2184_);
lean_dec_ref(v_rhs_2180_);
v_toCold_2309_ = lean_ctor_get(v___y_2193_, 0);
v_inheritedTraceOptions_2310_ = lean_ctor_get(v_toCold_2309_, 4);
lean_inc(v___y_2194_);
lean_inc_ref(v___y_2193_);
lean_inc(v___y_2192_);
lean_inc_ref(v___y_2191_);
lean_inc(v___y_2190_);
lean_inc_ref(v___y_2189_);
lean_inc(v___y_2188_);
lean_inc_ref(v___y_2187_);
lean_inc(v___y_2186_);
lean_inc_ref(v_inheritedTraceOptions_2310_);
v___x_2311_ = lean_apply_11(v___f_2182_, v_inheritedTraceOptions_2310_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, lean_box(0));
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; uint8_t v___x_2313_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2311_, 1);
v___x_2313_ = lean_unbox(v_a_2312_);
lean_dec(v_a_2312_);
if (v___x_2313_ == 0)
{
lean_dec(v_cls_2183_);
lean_dec_ref(v_lhs_2179_);
goto v___jp_2202_;
}
else
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2314_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_2315_ = l_Lean_indentExpr(v_lhs_2179_);
v___x_2316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2314_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
v___x_2317_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2183_, v___x_2316_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_dec_ref_known(v___x_2317_, 1);
goto v___jp_2202_;
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2317_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
lean_dec(v_cls_2183_);
lean_dec_ref(v_lhs_2179_);
v_a_2326_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2311_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2311_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
v___jp_2196_:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2197_, 0, v___x_2181_);
lean_ctor_set_uint8(v___x_2197_, 1, v___x_2181_);
v___x_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
return v___x_2198_;
}
v___jp_2199_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2200_, 0, v___x_2181_);
lean_ctor_set_uint8(v___x_2200_, 1, v___x_2181_);
v___x_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
return v___x_2201_;
}
v___jp_2202_:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2203_, 0, v___x_2181_);
lean_ctor_set_uint8(v___x_2203_, 1, v___x_2181_);
v___x_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
return v___x_2204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___boxed(lean_object** _args){
lean_object* v_lhs_2334_ = _args[0];
lean_object* v_rhs_2335_ = _args[1];
lean_object* v___x_2336_ = _args[2];
lean_object* v___f_2337_ = _args[3];
lean_object* v_cls_2338_ = _args[4];
lean_object* v_P_2339_ = _args[5];
lean_object* v_____r_2340_ = _args[6];
lean_object* v___y_2341_ = _args[7];
lean_object* v___y_2342_ = _args[8];
lean_object* v___y_2343_ = _args[9];
lean_object* v___y_2344_ = _args[10];
lean_object* v___y_2345_ = _args[11];
lean_object* v___y_2346_ = _args[12];
lean_object* v___y_2347_ = _args[13];
lean_object* v___y_2348_ = _args[14];
lean_object* v___y_2349_ = _args[15];
lean_object* v___y_2350_ = _args[16];
_start:
{
uint8_t v___x_187785__boxed_2351_; lean_object* v_res_2352_; 
v___x_187785__boxed_2351_ = lean_unbox(v___x_2336_);
v_res_2352_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2334_, v_rhs_2335_, v___x_187785__boxed_2351_, v___f_2337_, v_cls_2338_, v_P_2339_, v_____r_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(lean_object* v_val_2353_, lean_object* v_lhs_2354_, lean_object* v_rhs_2355_, lean_object* v_P_2356_, uint8_t v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v___x_2366_; 
lean_inc_ref(v_lhs_2354_);
lean_inc_ref(v_val_2353_);
v___x_2366_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_2353_, v_lhs_2354_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v_fst_2368_; lean_object* v_snd_2369_; lean_object* v___x_2370_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v_fst_2368_ = lean_ctor_get(v_a_2367_, 0);
lean_inc(v_fst_2368_);
v_snd_2369_ = lean_ctor_get(v_a_2367_, 1);
lean_inc(v_snd_2369_);
lean_dec(v_a_2367_);
lean_inc_ref(v_rhs_2355_);
lean_inc_ref(v_val_2353_);
v___x_2370_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_2353_, v_rhs_2355_, v_snd_2369_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v_fst_2372_; lean_object* v_snd_2373_; lean_object* v___x_2374_; lean_object* v_a_2375_; lean_object* v_fst_2376_; lean_object* v_snd_2377_; lean_object* v_common_2378_; lean_object* v_x_2379_; lean_object* v_y_2380_; lean_object* v___x_2381_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_a_2371_);
lean_dec_ref_known(v___x_2370_, 1);
v_fst_2372_ = lean_ctor_get(v_a_2371_, 0);
lean_inc(v_fst_2372_);
v_snd_2373_ = lean_ctor_get(v_a_2371_, 1);
lean_inc(v_snd_2373_);
lean_dec(v_a_2371_);
v___x_2374_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_2368_, v_fst_2372_, v_snd_2373_);
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref(v___x_2374_);
v_fst_2376_ = lean_ctor_get(v_a_2375_, 0);
lean_inc(v_fst_2376_);
v_snd_2377_ = lean_ctor_get(v_a_2375_, 1);
lean_inc(v_snd_2377_);
lean_dec(v_a_2375_);
v_common_2378_ = lean_ctor_get(v_fst_2376_, 0);
lean_inc_ref(v_common_2378_);
v_x_2379_ = lean_ctor_get(v_fst_2376_, 1);
lean_inc_ref(v_x_2379_);
v_y_2380_ = lean_ctor_get(v_fst_2376_, 2);
lean_inc_ref(v_y_2380_);
lean_dec(v_fst_2376_);
lean_inc_ref(v_val_2353_);
v___x_2381_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_2378_, v_val_2353_, v_snd_2377_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec_ref(v_common_2378_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v_fst_2383_; lean_object* v_snd_2384_; lean_object* v___x_2385_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2382_);
lean_dec_ref_known(v___x_2381_, 1);
v_fst_2383_ = lean_ctor_get(v_a_2382_, 0);
lean_inc(v_fst_2383_);
v_snd_2384_ = lean_ctor_get(v_a_2382_, 1);
lean_inc(v_snd_2384_);
lean_dec(v_a_2382_);
lean_inc_ref(v_val_2353_);
v___x_2385_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_2379_, v_val_2353_, v_snd_2384_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec_ref(v_x_2379_);
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
lean_inc_ref(v_val_2353_);
v___x_2389_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_2380_, v_val_2353_, v_snd_2388_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec_ref(v_y_2380_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2454_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2392_ = v___x_2389_;
v_isShared_2393_ = v_isSharedCheck_2454_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2389_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2454_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v_fst_2394_; lean_object* v_snd_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2453_; 
v_fst_2394_ = lean_ctor_get(v_a_2390_, 0);
v_snd_2395_ = lean_ctor_get(v_a_2390_, 1);
v_isSharedCheck_2453_ = !lean_is_exclusive(v_a_2390_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2397_ = v_a_2390_;
v_isShared_2398_ = v_isSharedCheck_2453_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_snd_2395_);
lean_inc(v_fst_2394_);
lean_dec(v_a_2390_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2453_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___x_2443_; lean_object* v___f_2444_; lean_object* v___y_2446_; lean_object* v___x_2450_; 
lean_inc_ref(v_val_2353_);
v___x_2443_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2353_);
v___f_2444_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_2444_, 0, v___x_2443_);
lean_inc(v_fst_2383_);
lean_inc_ref(v___f_2444_);
v___x_2450_ = l_Option_merge___redArg(v___f_2444_, v_fst_2383_, v_fst_2387_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v___x_2451_; 
lean_inc_ref(v_val_2353_);
v___x_2451_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_2353_);
v___y_2446_ = v___x_2451_;
goto v___jp_2445_;
}
else
{
lean_object* v_val_2452_; 
v_val_2452_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_val_2452_);
lean_dec_ref_known(v___x_2450_, 1);
v___y_2446_ = v_val_2452_;
goto v___jp_2445_;
}
v___jp_2399_:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; uint8_t v___x_2404_; 
lean_inc_ref(v_P_2356_);
v___x_2402_ = l_Lean_mkAppB(v_P_2356_, v_lhs_2354_, v_rhs_2355_);
v___x_2403_ = l_Lean_mkAppB(v_P_2356_, v___y_2400_, v___y_2401_);
v___x_2404_ = lean_expr_eqv(v___x_2402_, v___x_2403_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2405_; 
lean_del_object(v___x_2392_);
lean_inc_ref(v___x_2403_);
v___x_2405_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_2402_, v___x_2403_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2407_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
lean_dec_ref_known(v___x_2405_, 1);
v___x_2407_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2403_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2419_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2410_ = v___x_2407_;
v_isShared_2411_ = v_isSharedCheck_2419_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2407_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2419_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2412_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2412_, 0, v_a_2408_);
lean_ctor_set(v___x_2412_, 1, v_a_2406_);
lean_ctor_set_uint8(v___x_2412_, sizeof(void*)*2, v___x_2404_);
lean_ctor_set_uint8(v___x_2412_, sizeof(void*)*2 + 1, v___x_2404_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2412_);
v___x_2414_ = v___x_2397_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_snd_2395_);
v___x_2414_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2416_; 
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v___x_2414_);
v___x_2416_ = v___x_2410_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
lean_dec(v_a_2406_);
lean_del_object(v___x_2397_);
lean_dec(v_snd_2395_);
v_a_2420_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2407_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2407_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2420_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec_ref(v___x_2403_);
lean_del_object(v___x_2397_);
lean_dec(v_snd_2395_);
v_a_2428_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2405_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2405_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
else
{
lean_object* v___x_2436_; lean_object* v___x_2438_; 
lean_dec_ref(v___x_2403_);
lean_dec_ref(v___x_2402_);
v___x_2436_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2436_, 0, v___y_2357_);
lean_ctor_set_uint8(v___x_2436_, 1, v___y_2357_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2436_);
v___x_2438_ = v___x_2397_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2436_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v_snd_2395_);
v___x_2438_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
lean_object* v___x_2440_; 
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v___x_2438_);
v___x_2440_ = v___x_2392_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2438_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
v___jp_2445_:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Option_merge___redArg(v___f_2444_, v_fst_2383_, v_fst_2394_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v___x_2448_; 
v___x_2448_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_2353_);
v___y_2400_ = v___y_2446_;
v___y_2401_ = v___x_2448_;
goto v___jp_2399_;
}
else
{
lean_object* v_val_2449_; 
lean_dec_ref(v_val_2353_);
v_val_2449_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_val_2449_);
lean_dec_ref_known(v___x_2447_, 1);
v___y_2400_ = v___y_2446_;
v___y_2401_ = v_val_2449_;
goto v___jp_2399_;
}
}
}
}
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
lean_dec(v_fst_2387_);
lean_dec(v_fst_2383_);
lean_dec_ref(v_P_2356_);
lean_dec_ref(v_rhs_2355_);
lean_dec_ref(v_lhs_2354_);
lean_dec_ref(v_val_2353_);
v_a_2455_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2389_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2389_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec(v_fst_2383_);
lean_dec_ref(v_y_2380_);
lean_dec_ref(v_P_2356_);
lean_dec_ref(v_rhs_2355_);
lean_dec_ref(v_lhs_2354_);
lean_dec_ref(v_val_2353_);
v_a_2463_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2385_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2385_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
lean_dec_ref(v_y_2380_);
lean_dec_ref(v_x_2379_);
lean_dec_ref(v_P_2356_);
lean_dec_ref(v_rhs_2355_);
lean_dec_ref(v_lhs_2354_);
lean_dec_ref(v_val_2353_);
v_a_2471_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2381_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2381_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec(v_fst_2368_);
lean_dec_ref(v_P_2356_);
lean_dec_ref(v_rhs_2355_);
lean_dec_ref(v_lhs_2354_);
lean_dec_ref(v_val_2353_);
v_a_2479_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2370_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2370_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_dec_ref(v_P_2356_);
lean_dec_ref(v_rhs_2355_);
lean_dec_ref(v_lhs_2354_);
lean_dec_ref(v_val_2353_);
v_a_2487_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2366_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2366_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed(lean_object* v_val_2495_, lean_object* v_lhs_2496_, lean_object* v_rhs_2497_, lean_object* v_P_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
uint8_t v___y_188114__boxed_2508_; lean_object* v_res_2509_; 
v___y_188114__boxed_2508_ = lean_unbox(v___y_2499_);
v_res_2509_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(v_val_2495_, v_lhs_2496_, v_rhs_2497_, v_P_2498_, v___y_188114__boxed_2508_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(lean_object* v_lhs_2510_, lean_object* v_rhs_2511_, lean_object* v_P_2512_, lean_object* v_cls_2513_, uint8_t v___x_2514_, lean_object* v___f_2515_, uint8_t v___x_2516_, lean_object* v_____r_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v___x_2534_; 
lean_inc_ref(v_lhs_2510_);
v___x_2534_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2510_);
if (lean_obj_tag(v___x_2534_) == 1)
{
lean_object* v_val_2535_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; uint8_t v___y_2549_; lean_object* v___x_2574_; 
v_val_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_val_2535_);
lean_dec_ref_known(v___x_2534_, 1);
lean_inc_ref(v_rhs_2511_);
v___x_2574_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2511_);
if (lean_obj_tag(v___x_2574_) == 1)
{
lean_object* v_val_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2623_; 
v_val_2575_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2577_ = v___x_2574_;
v_isShared_2578_ = v_isSharedCheck_2623_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_val_2575_);
lean_dec(v___x_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2623_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
uint8_t v___x_2579_; 
v___x_2579_ = lean_expr_eqv(v_val_2535_, v_val_2575_);
if (v___x_2579_ == 0)
{
if (v___x_2514_ == 0)
{
lean_del_object(v___x_2577_);
lean_dec(v_val_2575_);
lean_dec_ref(v___f_2515_);
v___y_2549_ = v___x_2514_;
goto v___jp_2548_;
}
else
{
lean_object* v_toCold_2585_; lean_object* v_inheritedTraceOptions_2586_; lean_object* v___x_2587_; 
lean_dec_ref(v_P_2512_);
v_toCold_2585_ = lean_ctor_get(v___y_2525_, 0);
v_inheritedTraceOptions_2586_ = lean_ctor_get(v_toCold_2585_, 4);
lean_inc(v___y_2526_);
lean_inc_ref(v___y_2525_);
lean_inc(v___y_2524_);
lean_inc_ref(v___y_2523_);
lean_inc(v___y_2522_);
lean_inc_ref(v___y_2521_);
lean_inc(v___y_2520_);
lean_inc_ref(v___y_2519_);
lean_inc(v___y_2518_);
lean_inc_ref(v_inheritedTraceOptions_2586_);
v___x_2587_ = lean_apply_11(v___f_2515_, v_inheritedTraceOptions_2586_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, lean_box(0));
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; uint8_t v___x_2589_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_a_2588_);
lean_dec_ref_known(v___x_2587_, 1);
v___x_2589_ = lean_unbox(v_a_2588_);
lean_dec(v_a_2588_);
if (v___x_2589_ == 0)
{
lean_dec(v_val_2575_);
lean_dec(v_val_2535_);
lean_dec(v_cls_2513_);
lean_dec_ref(v_rhs_2511_);
lean_dec_ref(v_lhs_2510_);
goto v___jp_2580_;
}
else
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2590_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1);
v___x_2591_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2535_);
v___x_2592_ = l_Lean_MessageData_ofExpr(v___x_2591_);
v___x_2593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2590_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
v___x_2594_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3);
v___x_2595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2593_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
v___x_2596_ = l_Lean_indentExpr(v_lhs_2510_);
v___x_2597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2595_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v___x_2598_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5);
v___x_2599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2597_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2575_);
v___x_2601_ = l_Lean_MessageData_ofExpr(v___x_2600_);
v___x_2602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2599_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
lean_ctor_set(v___x_2603_, 1, v___x_2594_);
v___x_2604_ = l_Lean_indentExpr(v_rhs_2511_);
v___x_2605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2603_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
v___x_2606_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2513_, v___x_2605_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_dec_ref_known(v___x_2606_, 1);
goto v___jp_2580_;
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_del_object(v___x_2577_);
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2606_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2606_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_del_object(v___x_2577_);
lean_dec(v_val_2575_);
lean_dec(v_val_2535_);
lean_dec(v_cls_2513_);
lean_dec_ref(v_rhs_2511_);
lean_dec_ref(v_lhs_2510_);
v_a_2615_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2587_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2587_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
else
{
lean_del_object(v___x_2577_);
lean_dec(v_val_2575_);
lean_dec_ref(v___f_2515_);
v___y_2549_ = v___x_2516_;
goto v___jp_2548_;
}
v___jp_2580_:
{
lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2581_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2581_, 0, v___x_2579_);
lean_ctor_set_uint8(v___x_2581_, 1, v___x_2579_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set_tag(v___x_2577_, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2581_);
v___x_2583_ = v___x_2577_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
else
{
lean_object* v_toCold_2624_; lean_object* v_inheritedTraceOptions_2625_; lean_object* v___x_2626_; 
lean_dec(v___x_2574_);
lean_dec(v_val_2535_);
lean_dec_ref(v_P_2512_);
lean_dec_ref(v_lhs_2510_);
v_toCold_2624_ = lean_ctor_get(v___y_2525_, 0);
v_inheritedTraceOptions_2625_ = lean_ctor_get(v_toCold_2624_, 4);
lean_inc(v___y_2526_);
lean_inc_ref(v___y_2525_);
lean_inc(v___y_2524_);
lean_inc_ref(v___y_2523_);
lean_inc(v___y_2522_);
lean_inc_ref(v___y_2521_);
lean_inc(v___y_2520_);
lean_inc_ref(v___y_2519_);
lean_inc(v___y_2518_);
lean_inc_ref(v_inheritedTraceOptions_2625_);
v___x_2626_ = lean_apply_11(v___f_2515_, v_inheritedTraceOptions_2625_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, lean_box(0));
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; uint8_t v___x_2628_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
lean_dec_ref_known(v___x_2626_, 1);
v___x_2628_ = lean_unbox(v_a_2627_);
lean_dec(v_a_2627_);
if (v___x_2628_ == 0)
{
lean_dec(v_cls_2513_);
lean_dec_ref(v_rhs_2511_);
goto v___jp_2528_;
}
else
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2629_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_2630_ = l_Lean_indentExpr(v_rhs_2511_);
v___x_2631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2629_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v___x_2632_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2513_, v___x_2631_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_dec_ref_known(v___x_2632_, 1);
goto v___jp_2528_;
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2632_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2632_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
lean_dec(v_cls_2513_);
lean_dec_ref(v_rhs_2511_);
v_a_2641_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2626_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2626_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
v___jp_2536_:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2544_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7);
v___x_2545_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8));
v___x_2546_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2546_, 0, v_val_2535_);
lean_ctor_set(v___x_2546_, 1, v___x_2544_);
lean_ctor_set(v___x_2546_, 2, v___x_2545_);
v___x_2547_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___y_2537_, v___x_2546_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
return v___x_2547_;
}
v___jp_2548_:
{
lean_object* v_options_2550_; lean_object* v_toCold_2551_; uint8_t v_hasTrace_2552_; lean_object* v___x_2553_; lean_object* v___f_2554_; 
v_options_2550_ = lean_ctor_get(v___y_2525_, 1);
v_toCold_2551_ = lean_ctor_get(v___y_2525_, 0);
v_hasTrace_2552_ = lean_ctor_get_uint8(v_options_2550_, sizeof(void*)*1);
v___x_2553_ = lean_box(v___y_2549_);
lean_inc(v_val_2535_);
v___f_2554_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed), 13, 5);
lean_closure_set(v___f_2554_, 0, v_val_2535_);
lean_closure_set(v___f_2554_, 1, v_lhs_2510_);
lean_closure_set(v___f_2554_, 2, v_rhs_2511_);
lean_closure_set(v___f_2554_, 3, v_P_2512_);
lean_closure_set(v___f_2554_, 4, v___x_2553_);
if (v_hasTrace_2552_ == 0)
{
lean_dec(v_cls_2513_);
v___y_2537_ = v___f_2554_;
v___y_2538_ = v___y_2521_;
v___y_2539_ = v___y_2522_;
v___y_2540_ = v___y_2523_;
v___y_2541_ = v___y_2524_;
v___y_2542_ = v___y_2525_;
v___y_2543_ = v___y_2526_;
goto v___jp_2536_;
}
else
{
lean_object* v_inheritedTraceOptions_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; 
v_inheritedTraceOptions_2555_ = lean_ctor_get(v_toCold_2551_, 4);
v___x_2556_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2513_);
v___x_2557_ = l_Lean_Name_append(v___x_2556_, v_cls_2513_);
v___x_2558_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2555_, v_options_2550_, v___x_2557_);
lean_dec(v___x_2557_);
if (v___x_2558_ == 0)
{
lean_dec(v_cls_2513_);
v___y_2537_ = v___f_2554_;
v___y_2538_ = v___y_2521_;
v___y_2539_ = v___y_2522_;
v___y_2540_ = v___y_2523_;
v___y_2541_ = v___y_2524_;
v___y_2542_ = v___y_2525_;
v___y_2543_ = v___y_2526_;
goto v___jp_2536_;
}
else
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2559_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10);
lean_inc(v_val_2535_);
v___x_2560_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2535_);
v___x_2561_ = l_Lean_MessageData_ofExpr(v___x_2560_);
v___x_2562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2559_);
lean_ctor_set(v___x_2562_, 1, v___x_2561_);
v___x_2563_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12);
v___x_2564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2562_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
v___x_2565_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2513_, v___x_2564_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_dec_ref_known(v___x_2565_, 1);
v___y_2537_ = v___f_2554_;
v___y_2538_ = v___y_2521_;
v___y_2539_ = v___y_2522_;
v___y_2540_ = v___y_2523_;
v___y_2541_ = v___y_2524_;
v___y_2542_ = v___y_2525_;
v___y_2543_ = v___y_2526_;
goto v___jp_2536_;
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec_ref(v___f_2554_);
lean_dec(v_val_2535_);
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_2649_; lean_object* v_inheritedTraceOptions_2650_; lean_object* v___x_2651_; 
lean_dec(v___x_2534_);
lean_dec_ref(v_P_2512_);
lean_dec_ref(v_rhs_2511_);
v_toCold_2649_ = lean_ctor_get(v___y_2525_, 0);
v_inheritedTraceOptions_2650_ = lean_ctor_get(v_toCold_2649_, 4);
lean_inc(v___y_2526_);
lean_inc_ref(v___y_2525_);
lean_inc(v___y_2524_);
lean_inc_ref(v___y_2523_);
lean_inc(v___y_2522_);
lean_inc_ref(v___y_2521_);
lean_inc(v___y_2520_);
lean_inc_ref(v___y_2519_);
lean_inc(v___y_2518_);
lean_inc_ref(v_inheritedTraceOptions_2650_);
v___x_2651_ = lean_apply_11(v___f_2515_, v_inheritedTraceOptions_2650_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, lean_box(0));
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; uint8_t v___x_2653_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref_known(v___x_2651_, 1);
v___x_2653_ = lean_unbox(v_a_2652_);
lean_dec(v_a_2652_);
if (v___x_2653_ == 0)
{
lean_dec(v_cls_2513_);
lean_dec_ref(v_lhs_2510_);
goto v___jp_2531_;
}
else
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2654_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_2655_ = l_Lean_indentExpr(v_lhs_2510_);
v___x_2656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2654_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
v___x_2657_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2513_, v___x_2656_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_dec_ref_known(v___x_2657_, 1);
goto v___jp_2531_;
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2657_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2657_);
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
}
else
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
lean_dec(v_cls_2513_);
lean_dec_ref(v_lhs_2510_);
v_a_2666_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2668_ = v___x_2651_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2651_);
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
v___jp_2528_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2529_, 0, v___x_2516_);
lean_ctor_set_uint8(v___x_2529_, 1, v___x_2516_);
v___x_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
return v___x_2530_;
}
v___jp_2531_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2532_, 0, v___x_2516_);
lean_ctor_set_uint8(v___x_2532_, 1, v___x_2516_);
v___x_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
return v___x_2533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___boxed(lean_object** _args){
lean_object* v_lhs_2674_ = _args[0];
lean_object* v_rhs_2675_ = _args[1];
lean_object* v_P_2676_ = _args[2];
lean_object* v_cls_2677_ = _args[3];
lean_object* v___x_2678_ = _args[4];
lean_object* v___f_2679_ = _args[5];
lean_object* v___x_2680_ = _args[6];
lean_object* v_____r_2681_ = _args[7];
lean_object* v___y_2682_ = _args[8];
lean_object* v___y_2683_ = _args[9];
lean_object* v___y_2684_ = _args[10];
lean_object* v___y_2685_ = _args[11];
lean_object* v___y_2686_ = _args[12];
lean_object* v___y_2687_ = _args[13];
lean_object* v___y_2688_ = _args[14];
lean_object* v___y_2689_ = _args[15];
lean_object* v___y_2690_ = _args[16];
lean_object* v___y_2691_ = _args[17];
_start:
{
uint8_t v___x_188436__boxed_2692_; uint8_t v___x_188438__boxed_2693_; lean_object* v_res_2694_; 
v___x_188436__boxed_2692_ = lean_unbox(v___x_2678_);
v___x_188438__boxed_2693_ = lean_unbox(v___x_2680_);
v_res_2694_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2674_, v_rhs_2675_, v_P_2676_, v_cls_2677_, v___x_188436__boxed_2692_, v___f_2679_, v___x_188438__boxed_2693_, v_____r_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
return v_res_2694_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(lean_object* v_e_2695_){
_start:
{
if (lean_obj_tag(v_e_2695_) == 0)
{
uint8_t v___x_2696_; 
v___x_2696_ = 2;
return v___x_2696_;
}
else
{
uint8_t v___x_2697_; 
v___x_2697_ = 0;
return v___x_2697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5___boxed(lean_object* v_e_2698_){
_start:
{
uint8_t v_res_2699_; lean_object* v_r_2700_; 
v_res_2699_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_e_2698_);
lean_dec_ref(v_e_2698_);
v_r_2700_ = lean_box(v_res_2699_);
return v_r_2700_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(lean_object* v_x_2701_){
_start:
{
if (lean_obj_tag(v_x_2701_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
v_a_2703_ = lean_ctor_get(v_x_2701_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_x_2701_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v_x_2701_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v_x_2701_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
lean_ctor_set_tag(v___x_2705_, 1);
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
v_a_2711_ = lean_ctor_get(v_x_2701_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v_x_2701_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v_x_2701_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v_x_2701_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
lean_ctor_set_tag(v___x_2713_, 0);
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg___boxed(lean_object* v_x_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_2719_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(lean_object* v_opts_2722_, lean_object* v_opt_2723_){
_start:
{
lean_object* v_name_2724_; lean_object* v_defValue_2725_; lean_object* v_map_2726_; lean_object* v___x_2727_; 
v_name_2724_ = lean_ctor_get(v_opt_2723_, 0);
v_defValue_2725_ = lean_ctor_get(v_opt_2723_, 1);
v_map_2726_ = lean_ctor_get(v_opts_2722_, 0);
v___x_2727_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2726_, v_name_2724_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_inc(v_defValue_2725_);
return v_defValue_2725_;
}
else
{
lean_object* v_val_2728_; 
v_val_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_val_2728_);
lean_dec_ref_known(v___x_2727_, 1);
if (lean_obj_tag(v_val_2728_) == 3)
{
lean_object* v_v_2729_; 
v_v_2729_ = lean_ctor_get(v_val_2728_, 0);
lean_inc(v_v_2729_);
lean_dec_ref_known(v_val_2728_, 1);
return v_v_2729_;
}
else
{
lean_dec(v_val_2728_);
lean_inc(v_defValue_2725_);
return v_defValue_2725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6___boxed(lean_object* v_opts_2730_, lean_object* v_opt_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2730_, v_opt_2731_);
lean_dec_ref(v_opt_2731_);
lean_dec_ref(v_opts_2730_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(size_t v_sz_2733_, size_t v_i_2734_, lean_object* v_bs_2735_){
_start:
{
uint8_t v___x_2736_; 
v___x_2736_ = lean_usize_dec_lt(v_i_2734_, v_sz_2733_);
if (v___x_2736_ == 0)
{
return v_bs_2735_;
}
else
{
lean_object* v_v_2737_; lean_object* v_msg_2738_; lean_object* v___x_2739_; lean_object* v_bs_x27_2740_; size_t v___x_2741_; size_t v___x_2742_; lean_object* v___x_2743_; 
v_v_2737_ = lean_array_uget_borrowed(v_bs_2735_, v_i_2734_);
v_msg_2738_ = lean_ctor_get(v_v_2737_, 1);
lean_inc_ref(v_msg_2738_);
v___x_2739_ = lean_unsigned_to_nat(0u);
v_bs_x27_2740_ = lean_array_uset(v_bs_2735_, v_i_2734_, v___x_2739_);
v___x_2741_ = ((size_t)1ULL);
v___x_2742_ = lean_usize_add(v_i_2734_, v___x_2741_);
v___x_2743_ = lean_array_uset(v_bs_x27_2740_, v_i_2734_, v_msg_2738_);
v_i_2734_ = v___x_2742_;
v_bs_2735_ = v___x_2743_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2745_, lean_object* v_i_2746_, lean_object* v_bs_2747_){
_start:
{
size_t v_sz_boxed_2748_; size_t v_i_boxed_2749_; lean_object* v_res_2750_; 
v_sz_boxed_2748_ = lean_unbox_usize(v_sz_2745_);
lean_dec(v_sz_2745_);
v_i_boxed_2749_ = lean_unbox_usize(v_i_2746_);
lean_dec(v_i_2746_);
v_res_2750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_boxed_2748_, v_i_boxed_2749_, v_bs_2747_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(lean_object* v_oldTraces_2751_, lean_object* v_data_2752_, lean_object* v_ref_2753_, lean_object* v_msg_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v_toCold_2760_; lean_object* v_options_2761_; lean_object* v_currRecDepth_2762_; lean_object* v_maxRecDepth_2763_; lean_object* v_ref_2764_; lean_object* v_currNamespace_2765_; lean_object* v_openDecls_2766_; lean_object* v_initHeartbeats_2767_; lean_object* v_maxHeartbeats_2768_; lean_object* v_currMacroScope_2769_; uint8_t v_diag_2770_; uint8_t v_suppressElabErrors_2771_; lean_object* v___x_2772_; lean_object* v_traceState_2773_; lean_object* v_traces_2774_; lean_object* v_ref_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; size_t v_sz_2778_; size_t v___x_2779_; lean_object* v___x_2780_; lean_object* v_msg_2781_; lean_object* v___x_2782_; lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2820_; 
v_toCold_2760_ = lean_ctor_get(v___y_2757_, 0);
v_options_2761_ = lean_ctor_get(v___y_2757_, 1);
v_currRecDepth_2762_ = lean_ctor_get(v___y_2757_, 2);
v_maxRecDepth_2763_ = lean_ctor_get(v___y_2757_, 3);
v_ref_2764_ = lean_ctor_get(v___y_2757_, 4);
v_currNamespace_2765_ = lean_ctor_get(v___y_2757_, 5);
v_openDecls_2766_ = lean_ctor_get(v___y_2757_, 6);
v_initHeartbeats_2767_ = lean_ctor_get(v___y_2757_, 7);
v_maxHeartbeats_2768_ = lean_ctor_get(v___y_2757_, 8);
v_currMacroScope_2769_ = lean_ctor_get(v___y_2757_, 9);
v_diag_2770_ = lean_ctor_get_uint8(v___y_2757_, sizeof(void*)*10);
v_suppressElabErrors_2771_ = lean_ctor_get_uint8(v___y_2757_, sizeof(void*)*10 + 1);
v___x_2772_ = lean_st_ref_get(v___y_2758_);
v_traceState_2773_ = lean_ctor_get(v___x_2772_, 4);
lean_inc_ref(v_traceState_2773_);
lean_dec(v___x_2772_);
v_traces_2774_ = lean_ctor_get(v_traceState_2773_, 0);
lean_inc_ref(v_traces_2774_);
lean_dec_ref(v_traceState_2773_);
v_ref_2775_ = l_Lean_replaceRef(v_ref_2753_, v_ref_2764_);
lean_inc(v_currMacroScope_2769_);
lean_inc(v_maxHeartbeats_2768_);
lean_inc(v_initHeartbeats_2767_);
lean_inc(v_openDecls_2766_);
lean_inc(v_currNamespace_2765_);
lean_inc(v_maxRecDepth_2763_);
lean_inc(v_currRecDepth_2762_);
lean_inc_ref(v_options_2761_);
lean_inc_ref(v_toCold_2760_);
v___x_2776_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2776_, 0, v_toCold_2760_);
lean_ctor_set(v___x_2776_, 1, v_options_2761_);
lean_ctor_set(v___x_2776_, 2, v_currRecDepth_2762_);
lean_ctor_set(v___x_2776_, 3, v_maxRecDepth_2763_);
lean_ctor_set(v___x_2776_, 4, v_ref_2775_);
lean_ctor_set(v___x_2776_, 5, v_currNamespace_2765_);
lean_ctor_set(v___x_2776_, 6, v_openDecls_2766_);
lean_ctor_set(v___x_2776_, 7, v_initHeartbeats_2767_);
lean_ctor_set(v___x_2776_, 8, v_maxHeartbeats_2768_);
lean_ctor_set(v___x_2776_, 9, v_currMacroScope_2769_);
lean_ctor_set_uint8(v___x_2776_, sizeof(void*)*10, v_diag_2770_);
lean_ctor_set_uint8(v___x_2776_, sizeof(void*)*10 + 1, v_suppressElabErrors_2771_);
v___x_2777_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2774_);
lean_dec_ref(v_traces_2774_);
v_sz_2778_ = lean_array_size(v___x_2777_);
v___x_2779_ = ((size_t)0ULL);
v___x_2780_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_2778_, v___x_2779_, v___x_2777_);
v_msg_2781_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2781_, 0, v_data_2752_);
lean_ctor_set(v_msg_2781_, 1, v_msg_2754_);
lean_ctor_set(v_msg_2781_, 2, v___x_2780_);
v___x_2782_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2781_, v___y_2755_, v___y_2756_, v___x_2776_, v___y_2758_);
lean_dec_ref_known(v___x_2776_, 10);
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2785_ = v___x_2782_;
v_isShared_2786_ = v_isSharedCheck_2820_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2782_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2820_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2787_; lean_object* v_traceState_2788_; lean_object* v_env_2789_; lean_object* v_nextMacroScope_2790_; lean_object* v_ngen_2791_; lean_object* v_auxDeclNGen_2792_; lean_object* v_cache_2793_; lean_object* v_messages_2794_; lean_object* v_infoState_2795_; lean_object* v_snapshotTasks_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2819_; 
v___x_2787_ = lean_st_ref_take(v___y_2758_);
v_traceState_2788_ = lean_ctor_get(v___x_2787_, 4);
v_env_2789_ = lean_ctor_get(v___x_2787_, 0);
v_nextMacroScope_2790_ = lean_ctor_get(v___x_2787_, 1);
v_ngen_2791_ = lean_ctor_get(v___x_2787_, 2);
v_auxDeclNGen_2792_ = lean_ctor_get(v___x_2787_, 3);
v_cache_2793_ = lean_ctor_get(v___x_2787_, 5);
v_messages_2794_ = lean_ctor_get(v___x_2787_, 6);
v_infoState_2795_ = lean_ctor_get(v___x_2787_, 7);
v_snapshotTasks_2796_ = lean_ctor_get(v___x_2787_, 8);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2798_ = v___x_2787_;
v_isShared_2799_ = v_isSharedCheck_2819_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_snapshotTasks_2796_);
lean_inc(v_infoState_2795_);
lean_inc(v_messages_2794_);
lean_inc(v_cache_2793_);
lean_inc(v_traceState_2788_);
lean_inc(v_auxDeclNGen_2792_);
lean_inc(v_ngen_2791_);
lean_inc(v_nextMacroScope_2790_);
lean_inc(v_env_2789_);
lean_dec(v___x_2787_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2819_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
uint64_t v_tid_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2817_; 
v_tid_2800_ = lean_ctor_get_uint64(v_traceState_2788_, sizeof(void*)*1);
v_isSharedCheck_2817_ = !lean_is_exclusive(v_traceState_2788_);
if (v_isSharedCheck_2817_ == 0)
{
lean_object* v_unused_2818_; 
v_unused_2818_ = lean_ctor_get(v_traceState_2788_, 0);
lean_dec(v_unused_2818_);
v___x_2802_ = v_traceState_2788_;
v_isShared_2803_ = v_isSharedCheck_2817_;
goto v_resetjp_2801_;
}
else
{
lean_dec(v_traceState_2788_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2817_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2807_; 
v___x_2804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2804_, 0, v_ref_2753_);
lean_ctor_set(v___x_2804_, 1, v_a_2783_);
v___x_2805_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2751_, v___x_2804_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v___x_2805_);
v___x_2807_ = v___x_2802_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2805_);
lean_ctor_set_uint64(v_reuseFailAlloc_2816_, sizeof(void*)*1, v_tid_2800_);
v___x_2807_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
lean_object* v___x_2809_; 
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 4, v___x_2807_);
v___x_2809_ = v___x_2798_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_env_2789_);
lean_ctor_set(v_reuseFailAlloc_2815_, 1, v_nextMacroScope_2790_);
lean_ctor_set(v_reuseFailAlloc_2815_, 2, v_ngen_2791_);
lean_ctor_set(v_reuseFailAlloc_2815_, 3, v_auxDeclNGen_2792_);
lean_ctor_set(v_reuseFailAlloc_2815_, 4, v___x_2807_);
lean_ctor_set(v_reuseFailAlloc_2815_, 5, v_cache_2793_);
lean_ctor_set(v_reuseFailAlloc_2815_, 6, v_messages_2794_);
lean_ctor_set(v_reuseFailAlloc_2815_, 7, v_infoState_2795_);
lean_ctor_set(v_reuseFailAlloc_2815_, 8, v_snapshotTasks_2796_);
v___x_2809_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2813_; 
v___x_2810_ = lean_st_ref_put(v___y_2758_, v___x_2809_);
v___x_2811_ = lean_box(0);
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 0, v___x_2811_);
v___x_2813_ = v___x_2785_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2811_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_2821_, lean_object* v_data_2822_, lean_object* v_ref_2823_, lean_object* v_msg_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_2821_, v_data_2822_, v_ref_2823_, v_msg_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
return v_res_2830_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__0));
v___x_2833_ = l_Lean_stringToMessageData(v___x_2832_);
return v___x_2833_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2834_; double v___x_2835_; 
v___x_2834_ = lean_unsigned_to_nat(1000u);
v___x_2835_ = lean_float_of_nat(v___x_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(lean_object* v_cls_2836_, uint8_t v_collapsed_2837_, lean_object* v_tag_2838_, lean_object* v_opts_2839_, uint8_t v_clsEnabled_2840_, lean_object* v_oldTraces_2841_, lean_object* v_msg_2842_, lean_object* v_resStartStop_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_fst_2854_; lean_object* v_snd_2855_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v_data_2859_; lean_object* v_fst_2870_; lean_object* v_snd_2871_; lean_object* v___x_2872_; uint8_t v___x_2873_; lean_object* v___y_2875_; lean_object* v_a_2876_; uint8_t v___y_2891_; double v___y_2922_; 
v_fst_2854_ = lean_ctor_get(v_resStartStop_2843_, 0);
lean_inc(v_fst_2854_);
v_snd_2855_ = lean_ctor_get(v_resStartStop_2843_, 1);
lean_inc(v_snd_2855_);
lean_dec_ref(v_resStartStop_2843_);
v_fst_2870_ = lean_ctor_get(v_snd_2855_, 0);
lean_inc(v_fst_2870_);
v_snd_2871_ = lean_ctor_get(v_snd_2855_, 1);
lean_inc(v_snd_2871_);
lean_dec(v_snd_2855_);
v___x_2872_ = l_Lean_trace_profiler;
v___x_2873_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_2839_, v___x_2872_);
if (v___x_2873_ == 0)
{
v___y_2891_ = v___x_2873_;
goto v___jp_2890_;
}
else
{
lean_object* v___x_2927_; uint8_t v___x_2928_; 
v___x_2927_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2928_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_2839_, v___x_2927_);
if (v___x_2928_ == 0)
{
lean_object* v___x_2929_; lean_object* v___x_2930_; double v___x_2931_; double v___x_2932_; double v___x_2933_; 
v___x_2929_ = l_Lean_trace_profiler_threshold;
v___x_2930_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2839_, v___x_2929_);
v___x_2931_ = lean_float_of_nat(v___x_2930_);
v___x_2932_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2);
v___x_2933_ = lean_float_div(v___x_2931_, v___x_2932_);
v___y_2922_ = v___x_2933_;
goto v___jp_2921_;
}
else
{
lean_object* v___x_2934_; lean_object* v___x_2935_; double v___x_2936_; 
v___x_2934_ = l_Lean_trace_profiler_threshold;
v___x_2935_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2839_, v___x_2934_);
v___x_2936_ = lean_float_of_nat(v___x_2935_);
v___y_2922_ = v___x_2936_;
goto v___jp_2921_;
}
}
v___jp_2856_:
{
lean_object* v___x_2860_; 
lean_inc(v___y_2857_);
v___x_2860_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_2841_, v_data_2859_, v___y_2857_, v___y_2858_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v___x_2861_; 
lean_dec_ref_known(v___x_2860_, 1);
v___x_2861_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_fst_2854_);
return v___x_2861_;
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
lean_dec(v_fst_2854_);
v_a_2862_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2860_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2860_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
v___jp_2874_:
{
uint8_t v_result_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; double v___x_2880_; lean_object* v_data_2881_; 
v_result_2877_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_fst_2854_);
v___x_2878_ = lean_box(v_result_2877_);
v___x_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
v___x_2880_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2838_);
lean_inc_ref(v___x_2879_);
lean_inc(v_cls_2836_);
v_data_2881_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2881_, 0, v_cls_2836_);
lean_ctor_set(v_data_2881_, 1, v___x_2879_);
lean_ctor_set(v_data_2881_, 2, v_tag_2838_);
lean_ctor_set_float(v_data_2881_, sizeof(void*)*3, v___x_2880_);
lean_ctor_set_float(v_data_2881_, sizeof(void*)*3 + 8, v___x_2880_);
lean_ctor_set_uint8(v_data_2881_, sizeof(void*)*3 + 16, v_collapsed_2837_);
if (v___x_2873_ == 0)
{
lean_dec_ref_known(v___x_2879_, 1);
lean_dec(v_snd_2871_);
lean_dec(v_fst_2870_);
lean_dec_ref(v_tag_2838_);
lean_dec(v_cls_2836_);
v___y_2857_ = v___y_2875_;
v___y_2858_ = v_a_2876_;
v_data_2859_ = v_data_2881_;
goto v___jp_2856_;
}
else
{
lean_object* v_data_2882_; double v___x_2883_; double v___x_2884_; 
lean_dec_ref_known(v_data_2881_, 3);
v_data_2882_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2882_, 0, v_cls_2836_);
lean_ctor_set(v_data_2882_, 1, v___x_2879_);
lean_ctor_set(v_data_2882_, 2, v_tag_2838_);
v___x_2883_ = lean_unbox_float(v_fst_2870_);
lean_dec(v_fst_2870_);
lean_ctor_set_float(v_data_2882_, sizeof(void*)*3, v___x_2883_);
v___x_2884_ = lean_unbox_float(v_snd_2871_);
lean_dec(v_snd_2871_);
lean_ctor_set_float(v_data_2882_, sizeof(void*)*3 + 8, v___x_2884_);
lean_ctor_set_uint8(v_data_2882_, sizeof(void*)*3 + 16, v_collapsed_2837_);
v___y_2857_ = v___y_2875_;
v___y_2858_ = v_a_2876_;
v_data_2859_ = v_data_2882_;
goto v___jp_2856_;
}
}
v___jp_2885_:
{
lean_object* v_ref_2886_; lean_object* v___x_2887_; 
v_ref_2886_ = lean_ctor_get(v___y_2851_, 4);
lean_inc(v___y_2852_);
lean_inc_ref(v___y_2851_);
lean_inc(v___y_2850_);
lean_inc_ref(v___y_2849_);
lean_inc(v___y_2848_);
lean_inc_ref(v___y_2847_);
lean_inc(v___y_2846_);
lean_inc_ref(v___y_2845_);
lean_inc(v___y_2844_);
lean_inc(v_fst_2854_);
v___x_2887_ = lean_apply_11(v_msg_2842_, v_fst_2854_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, lean_box(0));
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2887_, 1);
v___y_2875_ = v_ref_2886_;
v_a_2876_ = v_a_2888_;
goto v___jp_2874_;
}
else
{
lean_object* v___x_2889_; 
lean_dec_ref_known(v___x_2887_, 1);
v___x_2889_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1);
v___y_2875_ = v_ref_2886_;
v_a_2876_ = v___x_2889_;
goto v___jp_2874_;
}
}
v___jp_2890_:
{
if (v_clsEnabled_2840_ == 0)
{
if (v___y_2891_ == 0)
{
lean_object* v___x_2892_; lean_object* v_traceState_2893_; lean_object* v_env_2894_; lean_object* v_nextMacroScope_2895_; lean_object* v_ngen_2896_; lean_object* v_auxDeclNGen_2897_; lean_object* v_cache_2898_; lean_object* v_messages_2899_; lean_object* v_infoState_2900_; lean_object* v_snapshotTasks_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2920_; 
lean_dec(v_snd_2871_);
lean_dec(v_fst_2870_);
lean_dec_ref(v_msg_2842_);
lean_dec_ref(v_tag_2838_);
lean_dec(v_cls_2836_);
v___x_2892_ = lean_st_ref_take(v___y_2852_);
v_traceState_2893_ = lean_ctor_get(v___x_2892_, 4);
v_env_2894_ = lean_ctor_get(v___x_2892_, 0);
v_nextMacroScope_2895_ = lean_ctor_get(v___x_2892_, 1);
v_ngen_2896_ = lean_ctor_get(v___x_2892_, 2);
v_auxDeclNGen_2897_ = lean_ctor_get(v___x_2892_, 3);
v_cache_2898_ = lean_ctor_get(v___x_2892_, 5);
v_messages_2899_ = lean_ctor_get(v___x_2892_, 6);
v_infoState_2900_ = lean_ctor_get(v___x_2892_, 7);
v_snapshotTasks_2901_ = lean_ctor_get(v___x_2892_, 8);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2903_ = v___x_2892_;
v_isShared_2904_ = v_isSharedCheck_2920_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_snapshotTasks_2901_);
lean_inc(v_infoState_2900_);
lean_inc(v_messages_2899_);
lean_inc(v_cache_2898_);
lean_inc(v_traceState_2893_);
lean_inc(v_auxDeclNGen_2897_);
lean_inc(v_ngen_2896_);
lean_inc(v_nextMacroScope_2895_);
lean_inc(v_env_2894_);
lean_dec(v___x_2892_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2920_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
uint64_t v_tid_2905_; lean_object* v_traces_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2919_; 
v_tid_2905_ = lean_ctor_get_uint64(v_traceState_2893_, sizeof(void*)*1);
v_traces_2906_ = lean_ctor_get(v_traceState_2893_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_traceState_2893_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2908_ = v_traceState_2893_;
v_isShared_2909_ = v_isSharedCheck_2919_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_traces_2906_);
lean_dec(v_traceState_2893_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2919_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2910_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2841_, v_traces_2906_);
lean_dec_ref(v_traces_2906_);
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 0, v___x_2910_);
v___x_2912_ = v___x_2908_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2910_);
lean_ctor_set_uint64(v_reuseFailAlloc_2918_, sizeof(void*)*1, v_tid_2905_);
v___x_2912_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2914_; 
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 4, v___x_2912_);
v___x_2914_ = v___x_2903_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_env_2894_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_nextMacroScope_2895_);
lean_ctor_set(v_reuseFailAlloc_2917_, 2, v_ngen_2896_);
lean_ctor_set(v_reuseFailAlloc_2917_, 3, v_auxDeclNGen_2897_);
lean_ctor_set(v_reuseFailAlloc_2917_, 4, v___x_2912_);
lean_ctor_set(v_reuseFailAlloc_2917_, 5, v_cache_2898_);
lean_ctor_set(v_reuseFailAlloc_2917_, 6, v_messages_2899_);
lean_ctor_set(v_reuseFailAlloc_2917_, 7, v_infoState_2900_);
lean_ctor_set(v_reuseFailAlloc_2917_, 8, v_snapshotTasks_2901_);
v___x_2914_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2915_ = lean_st_ref_put(v___y_2852_, v___x_2914_);
v___x_2916_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_fst_2854_);
return v___x_2916_;
}
}
}
}
}
else
{
goto v___jp_2885_;
}
}
else
{
goto v___jp_2885_;
}
}
v___jp_2921_:
{
double v___x_2923_; double v___x_2924_; double v___x_2925_; uint8_t v___x_2926_; 
v___x_2923_ = lean_unbox_float(v_snd_2871_);
v___x_2924_ = lean_unbox_float(v_fst_2870_);
v___x_2925_ = lean_float_sub(v___x_2923_, v___x_2924_);
v___x_2926_ = lean_float_decLt(v___y_2922_, v___x_2925_);
v___y_2891_ = v___x_2926_;
goto v___jp_2890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___boxed(lean_object** _args){
lean_object* v_cls_2937_ = _args[0];
lean_object* v_collapsed_2938_ = _args[1];
lean_object* v_tag_2939_ = _args[2];
lean_object* v_opts_2940_ = _args[3];
lean_object* v_clsEnabled_2941_ = _args[4];
lean_object* v_oldTraces_2942_ = _args[5];
lean_object* v_msg_2943_ = _args[6];
lean_object* v_resStartStop_2944_ = _args[7];
lean_object* v___y_2945_ = _args[8];
lean_object* v___y_2946_ = _args[9];
lean_object* v___y_2947_ = _args[10];
lean_object* v___y_2948_ = _args[11];
lean_object* v___y_2949_ = _args[12];
lean_object* v___y_2950_ = _args[13];
lean_object* v___y_2951_ = _args[14];
lean_object* v___y_2952_ = _args[15];
lean_object* v___y_2953_ = _args[16];
lean_object* v___y_2954_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2955_; uint8_t v_clsEnabled_boxed_2956_; lean_object* v_res_2957_; 
v_collapsed_boxed_2955_ = lean_unbox(v_collapsed_2938_);
v_clsEnabled_boxed_2956_ = lean_unbox(v_clsEnabled_2941_);
v_res_2957_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_2937_, v_collapsed_boxed_2955_, v_tag_2939_, v_opts_2940_, v_clsEnabled_boxed_2956_, v_oldTraces_2942_, v_msg_2943_, v_resStartStop_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v_opts_2940_);
return v_res_2957_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3(void){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2));
v___x_2964_ = l_Lean_stringToMessageData(v___x_2963_);
return v___x_2964_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5(void){
_start:
{
lean_object* v___x_2966_; double v___x_2967_; 
v___x_2966_ = lean_unsigned_to_nat(1000000000u);
v___x_2967_ = lean_float_of_nat(v___x_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(lean_object* v_P_2968_, lean_object* v_lhs_2969_, lean_object* v_rhs_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_){
_start:
{
uint8_t v___y_2982_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v_options_3004_; lean_object* v_toCold_3005_; uint8_t v_hasTrace_3006_; lean_object* v_cls_3007_; lean_object* v___f_3008_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; uint8_t v_____do__lift_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; 
v_options_3004_ = lean_ctor_get(v_a_2978_, 1);
v_toCold_3005_ = lean_ctor_get(v_a_2978_, 0);
v_hasTrace_3006_ = lean_ctor_get_uint8(v_options_3004_, sizeof(void*)*1);
v_cls_3007_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___f_3008_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1));
if (v_hasTrace_3006_ == 0)
{
lean_object* v_inheritedTraceOptions_3136_; lean_object* v___x_3137_; lean_object* v_a_3138_; uint8_t v___x_3139_; 
v_inheritedTraceOptions_3136_ = lean_ctor_get(v_toCold_3005_, 4);
v___x_3137_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3007_, v_inheritedTraceOptions_3136_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3138_);
lean_dec_ref(v___x_3137_);
v___x_3139_ = lean_unbox(v_a_3138_);
lean_dec(v_a_3138_);
v_____do__lift_3113_ = v___x_3139_;
v___y_3114_ = v_a_2971_;
v___y_3115_ = v_a_2972_;
v___y_3116_ = v_a_2973_;
v___y_3117_ = v_a_2974_;
v___y_3118_ = v_a_2975_;
v___y_3119_ = v_a_2976_;
v___y_3120_ = v_a_2977_;
v___y_3121_ = v_a_2978_;
v___y_3122_ = v_a_2979_;
goto v___jp_3112_;
}
else
{
lean_object* v_inheritedTraceOptions_3140_; lean_object* v___f_3141_; uint8_t v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; uint8_t v___x_3145_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v_a_3149_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v_a_3161_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v_a_3179_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v_a_3194_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; 
v_inheritedTraceOptions_3140_ = lean_ctor_get(v_toCold_3005_, 4);
v___f_3141_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4));
v___x_3142_ = 0;
v___x_3143_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_3144_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3145_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3140_, v_options_3004_, v___x_3144_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3242_; uint8_t v___x_3243_; 
v___x_3242_ = l_Lean_trace_profiler;
v___x_3243_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_3004_, v___x_3242_);
if (v___x_3243_ == 0)
{
lean_object* v___x_3244_; lean_object* v_a_3245_; uint8_t v___x_3246_; 
v___x_3244_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3007_, v_inheritedTraceOptions_3140_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_a_3245_);
lean_dec_ref(v___x_3244_);
v___x_3246_ = lean_unbox(v_a_3245_);
lean_dec(v_a_3245_);
v_____do__lift_3113_ = v___x_3246_;
v___y_3114_ = v_a_2971_;
v___y_3115_ = v_a_2972_;
v___y_3116_ = v_a_2973_;
v___y_3117_ = v_a_2974_;
v___y_3118_ = v_a_2975_;
v___y_3119_ = v_a_2976_;
v___y_3120_ = v_a_2977_;
v___y_3121_ = v_a_2978_;
v___y_3122_ = v_a_2979_;
goto v___jp_3112_;
}
else
{
goto v___jp_3209_;
}
}
else
{
goto v___jp_3209_;
}
v___jp_3146_:
{
lean_object* v___x_3150_; double v___x_3151_; double v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3150_ = lean_io_get_num_heartbeats();
v___x_3151_ = lean_float_of_nat(v___y_3148_);
v___x_3152_ = lean_float_of_nat(v___x_3150_);
v___x_3153_ = lean_box_float(v___x_3151_);
v___x_3154_ = lean_box_float(v___x_3152_);
v___x_3155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3153_);
lean_ctor_set(v___x_3155_, 1, v___x_3154_);
v___x_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3156_, 0, v_a_3149_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_3007_, v___x_3142_, v___x_3143_, v_options_3004_, v___x_3145_, v___y_3147_, v___f_3141_, v___x_3156_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
return v___x_3157_;
}
v___jp_3158_:
{
lean_object* v___x_3162_; 
v___x_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3162_, 0, v_a_3161_);
v___y_3147_ = v___y_3160_;
v___y_3148_ = v___y_3159_;
v_a_3149_ = v___x_3162_;
goto v___jp_3146_;
}
v___jp_3163_:
{
if (lean_obj_tag(v___y_3166_) == 0)
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
v_a_3167_ = lean_ctor_get(v___y_3166_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___y_3166_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___y_3166_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___y_3166_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
lean_ctor_set_tag(v___x_3169_, 1);
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
v___y_3147_ = v___y_3165_;
v___y_3148_ = v___y_3164_;
v_a_3149_ = v___x_3172_;
goto v___jp_3146_;
}
}
}
else
{
lean_object* v_a_3175_; 
v_a_3175_ = lean_ctor_get(v___y_3166_, 0);
lean_inc(v_a_3175_);
lean_dec_ref_known(v___y_3166_, 1);
v___y_3159_ = v___y_3164_;
v___y_3160_ = v___y_3165_;
v_a_3161_ = v_a_3175_;
goto v___jp_3158_;
}
}
v___jp_3176_:
{
lean_object* v___x_3180_; double v___x_3181_; double v___x_3182_; double v___x_3183_; double v___x_3184_; double v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3180_ = lean_io_mono_nanos_now();
v___x_3181_ = lean_float_of_nat(v___y_3177_);
v___x_3182_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5);
v___x_3183_ = lean_float_div(v___x_3181_, v___x_3182_);
v___x_3184_ = lean_float_of_nat(v___x_3180_);
v___x_3185_ = lean_float_div(v___x_3184_, v___x_3182_);
v___x_3186_ = lean_box_float(v___x_3183_);
v___x_3187_ = lean_box_float(v___x_3185_);
v___x_3188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3186_);
lean_ctor_set(v___x_3188_, 1, v___x_3187_);
v___x_3189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3189_, 0, v_a_3179_);
lean_ctor_set(v___x_3189_, 1, v___x_3188_);
v___x_3190_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_3007_, v___x_3142_, v___x_3143_, v_options_3004_, v___x_3145_, v___y_3178_, v___f_3141_, v___x_3189_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
return v___x_3190_;
}
v___jp_3191_:
{
lean_object* v___x_3195_; 
v___x_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3195_, 0, v_a_3194_);
v___y_3177_ = v___y_3192_;
v___y_3178_ = v___y_3193_;
v_a_3179_ = v___x_3195_;
goto v___jp_3176_;
}
v___jp_3196_:
{
if (lean_obj_tag(v___y_3199_) == 0)
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
v_a_3200_ = lean_ctor_get(v___y_3199_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___y_3199_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___y_3199_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___y_3199_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
lean_ctor_set_tag(v___x_3202_, 1);
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
v___y_3177_ = v___y_3197_;
v___y_3178_ = v___y_3198_;
v_a_3179_ = v___x_3205_;
goto v___jp_3176_;
}
}
}
else
{
lean_object* v_a_3208_; 
v_a_3208_ = lean_ctor_get(v___y_3199_, 0);
lean_inc(v_a_3208_);
lean_dec_ref_known(v___y_3199_, 1);
v___y_3192_ = v___y_3197_;
v___y_3193_ = v___y_3198_;
v_a_3194_ = v_a_3208_;
goto v___jp_3191_;
}
}
v___jp_3209_:
{
lean_object* v___x_3210_; lean_object* v_a_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; 
v___x_3210_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v_a_2979_);
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
lean_dec_ref(v___x_3210_);
v___x_3212_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3213_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_3004_, v___x_3212_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v_a_3216_; uint8_t v___x_3217_; 
v___x_3214_ = lean_io_mono_nanos_now();
v___x_3215_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3007_, v_inheritedTraceOptions_3140_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
lean_inc(v_a_3216_);
lean_dec_ref(v___x_3215_);
v___x_3217_ = lean_unbox(v_a_3216_);
lean_dec(v_a_3216_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = lean_box(0);
v___x_3219_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2969_, v_rhs_2970_, v___x_3213_, v___f_3008_, v_cls_3007_, v_P_2968_, v___x_3218_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
v___y_3197_ = v___x_3214_;
v___y_3198_ = v_a_3211_;
v___y_3199_ = v___x_3219_;
goto v___jp_3196_;
}
else
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3220_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_2970_);
lean_inc_ref(v_lhs_2969_);
lean_inc_ref(v_P_2968_);
v___x_3221_ = l_Lean_mkAppB(v_P_2968_, v_lhs_2969_, v_rhs_2970_);
v___x_3222_ = l_Lean_indentExpr(v___x_3221_);
v___x_3223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3220_);
lean_ctor_set(v___x_3223_, 1, v___x_3222_);
v___x_3224_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3007_, v___x_3223_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; lean_object* v___x_3226_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3225_);
lean_dec_ref_known(v___x_3224_, 1);
v___x_3226_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2969_, v_rhs_2970_, v___x_3213_, v___f_3008_, v_cls_3007_, v_P_2968_, v_a_3225_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
v___y_3197_ = v___x_3214_;
v___y_3198_ = v_a_3211_;
v___y_3199_ = v___x_3226_;
goto v___jp_3196_;
}
else
{
lean_object* v_a_3227_; 
lean_dec_ref(v_rhs_2970_);
lean_dec_ref(v_lhs_2969_);
lean_dec_ref(v_P_2968_);
v_a_3227_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3227_);
lean_dec_ref_known(v___x_3224_, 1);
v___y_3192_ = v___x_3214_;
v___y_3193_ = v_a_3211_;
v_a_3194_ = v_a_3227_;
goto v___jp_3191_;
}
}
}
else
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v_a_3230_; uint8_t v___x_3231_; 
v___x_3228_ = lean_io_get_num_heartbeats();
v___x_3229_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3007_, v_inheritedTraceOptions_3140_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_a_3230_);
lean_dec_ref(v___x_3229_);
v___x_3231_ = lean_unbox(v_a_3230_);
lean_dec(v_a_3230_);
if (v___x_3231_ == 0)
{
lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3232_ = lean_box(0);
v___x_3233_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2969_, v_rhs_2970_, v_P_2968_, v_cls_3007_, v___x_3213_, v___f_3008_, v___x_3142_, v___x_3232_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
v___y_3164_ = v___x_3228_;
v___y_3165_ = v_a_3211_;
v___y_3166_ = v___x_3233_;
goto v___jp_3163_;
}
else
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3234_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_2970_);
lean_inc_ref(v_lhs_2969_);
lean_inc_ref(v_P_2968_);
v___x_3235_ = l_Lean_mkAppB(v_P_2968_, v_lhs_2969_, v_rhs_2970_);
v___x_3236_ = l_Lean_indentExpr(v___x_3235_);
v___x_3237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3234_);
lean_ctor_set(v___x_3237_, 1, v___x_3236_);
v___x_3238_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3007_, v___x_3237_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; lean_object* v___x_3240_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
lean_inc(v_a_3239_);
lean_dec_ref_known(v___x_3238_, 1);
v___x_3240_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2969_, v_rhs_2970_, v_P_2968_, v_cls_3007_, v___x_3213_, v___f_3008_, v___x_3142_, v_a_3239_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
v___y_3164_ = v___x_3228_;
v___y_3165_ = v_a_3211_;
v___y_3166_ = v___x_3240_;
goto v___jp_3163_;
}
else
{
lean_object* v_a_3241_; 
lean_dec_ref(v_rhs_2970_);
lean_dec_ref(v_lhs_2969_);
lean_dec_ref(v_P_2968_);
v_a_3241_ = lean_ctor_get(v___x_3238_, 0);
lean_inc(v_a_3241_);
lean_dec_ref_known(v___x_3238_, 1);
v___y_3159_ = v___x_3228_;
v___y_3160_ = v_a_3211_;
v_a_3161_ = v_a_3241_;
goto v___jp_3158_;
}
}
}
}
}
v___jp_2981_:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2983_, 0, v___y_2982_);
lean_ctor_set_uint8(v___x_2983_, 1, v___y_2982_);
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
lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2989_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
return v___x_2990_;
}
v___jp_2991_:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3000_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7);
v___x_3001_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8));
v___x_3002_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3002_, 0, v___y_2993_);
lean_ctor_set(v___x_3002_, 1, v___x_3000_);
lean_ctor_set(v___x_3002_, 2, v___x_3001_);
v___x_3003_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___y_2992_, v___x_3002_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
return v___x_3003_;
}
v___jp_3009_:
{
lean_object* v___x_3019_; 
lean_inc_ref(v_lhs_2969_);
v___x_3019_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2969_);
if (lean_obj_tag(v___x_3019_) == 1)
{
lean_object* v_val_3020_; lean_object* v___x_3021_; 
v_val_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_val_3020_);
lean_dec_ref_known(v___x_3019_, 1);
lean_inc_ref(v_rhs_2970_);
v___x_3021_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2970_);
if (lean_obj_tag(v___x_3021_) == 1)
{
lean_object* v_val_3022_; uint8_t v___x_3023_; 
v_val_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_val_3022_);
lean_dec_ref_known(v___x_3021_, 1);
v___x_3023_ = lean_expr_eqv(v_val_3020_, v_val_3022_);
if (v___x_3023_ == 0)
{
lean_object* v_toCold_3024_; lean_object* v_inheritedTraceOptions_3025_; lean_object* v___x_3026_; lean_object* v_a_3027_; uint8_t v___x_3028_; 
lean_dec_ref(v_P_2968_);
v_toCold_3024_ = lean_ctor_get(v___y_3017_, 0);
v_inheritedTraceOptions_3025_ = lean_ctor_get(v_toCold_3024_, 4);
v___x_3026_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3007_, v_inheritedTraceOptions_3025_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_a_3027_);
lean_dec_ref(v___x_3026_);
v___x_3028_ = lean_unbox(v_a_3027_);
lean_dec(v_a_3027_);
if (v___x_3028_ == 0)
{
lean_dec(v_val_3022_);
lean_dec(v_val_3020_);
lean_dec_ref(v_rhs_2970_);
lean_dec_ref(v_lhs_2969_);
v___y_2982_ = v___x_3023_;
goto v___jp_2981_;
}
else
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3029_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1);
v___x_3030_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3020_);
v___x_3031_ = l_Lean_MessageData_ofExpr(v___x_3030_);
v___x_3032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3029_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3);
v___x_3034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3032_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
v___x_3035_ = l_Lean_indentExpr(v_lhs_2969_);
v___x_3036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3034_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
v___x_3037_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5);
v___x_3038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3036_);
lean_ctor_set(v___x_3038_, 1, v___x_3037_);
v___x_3039_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3022_);
v___x_3040_ = l_Lean_MessageData_ofExpr(v___x_3039_);
v___x_3041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3038_);
lean_ctor_set(v___x_3041_, 1, v___x_3040_);
v___x_3042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3041_);
lean_ctor_set(v___x_3042_, 1, v___x_3033_);
v___x_3043_ = l_Lean_indentExpr(v_rhs_2970_);
v___x_3044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3042_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
v___x_3045_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3007_, v___x_3044_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_dec_ref_known(v___x_3045_, 1);
v___y_2982_ = v___x_3023_;
goto v___jp_2981_;
}
else
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___x_3045_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_3045_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
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
else
{
lean_object* v_options_3054_; lean_object* v_toCold_3055_; uint8_t v_hasTrace_3056_; uint8_t v___x_3057_; lean_object* v___x_3058_; lean_object* v___f_3059_; 
lean_dec(v_val_3022_);
v_options_3054_ = lean_ctor_get(v___y_3017_, 1);
v_toCold_3055_ = lean_ctor_get(v___y_3017_, 0);
v_hasTrace_3056_ = lean_ctor_get_uint8(v_options_3054_, sizeof(void*)*1);
v___x_3057_ = 0;
v___x_3058_ = lean_box(v___x_3057_);
lean_inc(v_val_3020_);
v___f_3059_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 13, 5);
lean_closure_set(v___f_3059_, 0, v_val_3020_);
lean_closure_set(v___f_3059_, 1, v_lhs_2969_);
lean_closure_set(v___f_3059_, 2, v_rhs_2970_);
lean_closure_set(v___f_3059_, 3, v_P_2968_);
lean_closure_set(v___f_3059_, 4, v___x_3058_);
if (v_hasTrace_3056_ == 0)
{
v___y_2992_ = v___f_3059_;
v___y_2993_ = v_val_3020_;
v___y_2994_ = v___y_3013_;
v___y_2995_ = v___y_3014_;
v___y_2996_ = v___y_3015_;
v___y_2997_ = v___y_3016_;
v___y_2998_ = v___y_3017_;
v___y_2999_ = v___y_3018_;
goto v___jp_2991_;
}
else
{
lean_object* v_inheritedTraceOptions_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
v_inheritedTraceOptions_3060_ = lean_ctor_get(v_toCold_3055_, 4);
v___x_3061_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3062_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3060_, v_options_3054_, v___x_3061_);
if (v___x_3062_ == 0)
{
v___y_2992_ = v___f_3059_;
v___y_2993_ = v_val_3020_;
v___y_2994_ = v___y_3013_;
v___y_2995_ = v___y_3014_;
v___y_2996_ = v___y_3015_;
v___y_2997_ = v___y_3016_;
v___y_2998_ = v___y_3017_;
v___y_2999_ = v___y_3018_;
goto v___jp_2991_;
}
else
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3063_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10);
lean_inc(v_val_3020_);
v___x_3064_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3020_);
v___x_3065_ = l_Lean_MessageData_ofExpr(v___x_3064_);
v___x_3066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3063_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v___x_3067_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12);
v___x_3068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3066_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
v___x_3069_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3007_, v___x_3068_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_dec_ref_known(v___x_3069_, 1);
v___y_2992_ = v___f_3059_;
v___y_2993_ = v_val_3020_;
v___y_2994_ = v___y_3013_;
v___y_2995_ = v___y_3014_;
v___y_2996_ = v___y_3015_;
v___y_2997_ = v___y_3016_;
v___y_2998_ = v___y_3017_;
v___y_2999_ = v___y_3018_;
goto v___jp_2991_;
}
else
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
lean_dec_ref(v___f_3059_);
lean_dec(v_val_3020_);
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_3069_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3070_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_3078_; lean_object* v_inheritedTraceOptions_3079_; lean_object* v___x_3080_; lean_object* v_a_3081_; uint8_t v___x_3082_; 
lean_dec(v___x_3021_);
lean_dec(v_val_3020_);
lean_dec_ref(v_lhs_2969_);
lean_dec_ref(v_P_2968_);
v_toCold_3078_ = lean_ctor_get(v___y_3017_, 0);
v_inheritedTraceOptions_3079_ = lean_ctor_get(v_toCold_3078_, 4);
v___x_3080_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3007_, v_inheritedTraceOptions_3079_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref(v___x_3080_);
v___x_3082_ = lean_unbox(v_a_3081_);
lean_dec(v_a_3081_);
if (v___x_3082_ == 0)
{
lean_dec_ref(v_rhs_2970_);
goto v___jp_2988_;
}
else
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3083_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_3084_ = l_Lean_indentExpr(v_rhs_2970_);
v___x_3085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3083_);
lean_ctor_set(v___x_3085_, 1, v___x_3084_);
v___x_3086_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3007_, v___x_3085_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_dec_ref_known(v___x_3086_, 1);
goto v___jp_2988_;
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3086_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3086_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3095_; lean_object* v_inheritedTraceOptions_3096_; lean_object* v___x_3097_; lean_object* v_a_3098_; uint8_t v___x_3099_; 
lean_dec(v___x_3019_);
lean_dec_ref(v_rhs_2970_);
lean_dec_ref(v_P_2968_);
v_toCold_3095_ = lean_ctor_get(v___y_3017_, 0);
v_inheritedTraceOptions_3096_ = lean_ctor_get(v_toCold_3095_, 4);
v___x_3097_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3007_, v_inheritedTraceOptions_3096_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
lean_dec_ref(v___x_3097_);
v___x_3099_ = lean_unbox(v_a_3098_);
lean_dec(v_a_3098_);
if (v___x_3099_ == 0)
{
lean_dec_ref(v_lhs_2969_);
goto v___jp_2985_;
}
else
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3100_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_3101_ = l_Lean_indentExpr(v_lhs_2969_);
v___x_3102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3100_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
v___x_3103_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3007_, v___x_3102_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_dec_ref_known(v___x_3103_, 1);
goto v___jp_2985_;
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3103_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3103_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
}
}
v___jp_3112_:
{
if (v_____do__lift_3113_ == 0)
{
v___y_3010_ = v___y_3114_;
v___y_3011_ = v___y_3115_;
v___y_3012_ = v___y_3116_;
v___y_3013_ = v___y_3117_;
v___y_3014_ = v___y_3118_;
v___y_3015_ = v___y_3119_;
v___y_3016_ = v___y_3120_;
v___y_3017_ = v___y_3121_;
v___y_3018_ = v___y_3122_;
goto v___jp_3009_;
}
else
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3123_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_2970_);
lean_inc_ref(v_lhs_2969_);
lean_inc_ref(v_P_2968_);
v___x_3124_ = l_Lean_mkAppB(v_P_2968_, v_lhs_2969_, v_rhs_2970_);
v___x_3125_ = l_Lean_indentExpr(v___x_3124_);
v___x_3126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3123_);
lean_ctor_set(v___x_3126_, 1, v___x_3125_);
v___x_3127_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3007_, v___x_3126_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_dec_ref_known(v___x_3127_, 1);
v___y_3010_ = v___y_3114_;
v___y_3011_ = v___y_3115_;
v___y_3012_ = v___y_3116_;
v___y_3013_ = v___y_3117_;
v___y_3014_ = v___y_3118_;
v___y_3015_ = v___y_3119_;
v___y_3016_ = v___y_3120_;
v___y_3017_ = v___y_3121_;
v___y_3018_ = v___y_3122_;
goto v___jp_3009_;
}
else
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
lean_dec_ref(v_rhs_2970_);
lean_dec_ref(v_lhs_2969_);
lean_dec_ref(v_P_2968_);
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___boxed(lean_object* v_P_3247_, lean_object* v_lhs_3248_, lean_object* v_rhs_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v_P_3247_, v_lhs_3248_, v_rhs_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_);
lean_dec(v_a_3258_);
lean_dec_ref(v_a_3257_);
lean_dec(v_a_3256_);
lean_dec_ref(v_a_3255_);
lean_dec(v_a_3254_);
lean_dec_ref(v_a_3253_);
lean_dec(v_a_3252_);
lean_dec_ref(v_a_3251_);
lean_dec(v_a_3250_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(lean_object* v_cls_3261_, lean_object* v_msg_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3261_, v_msg_3262_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object* v_cls_3274_, lean_object* v_msg_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(v_cls_3274_, v_msg_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(lean_object* v_00_u03b1_3287_, lean_object* v_x_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_3288_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___boxed(lean_object* v_00_u03b1_3300_, lean_object* v_x_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(v_00_u03b1_3300_, v_x_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(lean_object* v_oldTraces_3313_, lean_object* v_data_3314_, lean_object* v_ref_3315_, lean_object* v_msg_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_3313_, v_data_3314_, v_ref_3315_, v_msg_3316_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___boxed(lean_object* v_oldTraces_3328_, lean_object* v_data_3329_, lean_object* v_ref_3330_, lean_object* v_msg_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(v_oldTraces_3328_, v_data_3329_, v_ref_3330_, v_msg_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(lean_object* v_x_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3354_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3354_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0___boxed(lean_object* v_x_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v_x_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___y_3357_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(lean_object* v_arg_3373_, lean_object* v_arg_3374_, lean_object* v_arg_3375_, lean_object* v_arg_3376_, lean_object* v_____r_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v___x_3388_; 
lean_inc_ref(v_arg_3373_);
v___x_3388_ = l_Lean_Meta_getDecLevel(v_arg_3373_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref_known(v___x_3388_, 1);
v___x_3390_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2));
v___x_3391_ = lean_box(0);
v___x_3392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3392_, 0, v_a_3389_);
lean_ctor_set(v___x_3392_, 1, v___x_3391_);
v___x_3393_ = l_Lean_Expr_const___override(v___x_3390_, v___x_3392_);
v___x_3394_ = l_Lean_mkAppB(v___x_3393_, v_arg_3373_, v_arg_3374_);
v___x_3395_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3394_, v_arg_3375_, v_arg_3376_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
return v___x_3395_;
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_dec_ref(v_arg_3376_);
lean_dec_ref(v_arg_3375_);
lean_dec_ref(v_arg_3374_);
lean_dec_ref(v_arg_3373_);
v_a_3396_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3388_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3388_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___boxed(lean_object* v_arg_3404_, lean_object* v_arg_3405_, lean_object* v_arg_3406_, lean_object* v_arg_3407_, lean_object* v_____r_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3404_, v_arg_3405_, v_arg_3406_, v_arg_3407_, v_____r_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(lean_object* v_arg_3423_, lean_object* v_arg_3424_, lean_object* v_arg_3425_, lean_object* v_____r_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v___x_3437_; 
lean_inc_ref(v_arg_3423_);
v___x_3437_ = l_Lean_Meta_getLevel(v_arg_3423_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref_known(v___x_3437_, 1);
v___x_3439_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1));
v___x_3440_ = lean_box(0);
v___x_3441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3441_, 0, v_a_3438_);
lean_ctor_set(v___x_3441_, 1, v___x_3440_);
v___x_3442_ = l_Lean_Expr_const___override(v___x_3439_, v___x_3441_);
v___x_3443_ = l_Lean_Expr_app___override(v___x_3442_, v_arg_3423_);
v___x_3444_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3443_, v_arg_3424_, v_arg_3425_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
return v___x_3444_;
}
else
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
lean_dec_ref(v_arg_3425_);
lean_dec_ref(v_arg_3424_);
lean_dec_ref(v_arg_3423_);
v_a_3445_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3437_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3437_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___boxed(lean_object* v_arg_3453_, lean_object* v_arg_3454_, lean_object* v_arg_3455_, lean_object* v_____r_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3453_, v_arg_3454_, v_arg_3455_, v_____r_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
return v_res_3467_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1(void){
_start:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3469_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0));
v___x_3470_ = l_Lean_stringToMessageData(v___x_3469_);
return v___x_3470_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2(void){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3471_ = l_Lean_checkEmoji;
v___x_3472_ = l_Lean_stringToMessageData(v___x_3471_);
return v___x_3472_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3(void){
_start:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3473_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2);
v___x_3474_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1);
v___x_3475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
lean_ctor_set(v___x_3475_, 1, v___x_3473_);
return v___x_3475_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5(void){
_start:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3477_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4));
v___x_3478_ = l_Lean_stringToMessageData(v___x_3477_);
return v___x_3478_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6(void){
_start:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3479_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5);
v___x_3480_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3);
v___x_3481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
lean_ctor_set(v___x_3481_, 1, v___x_3479_);
return v___x_3481_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8(void){
_start:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7));
v___x_3484_ = l_Lean_stringToMessageData(v___x_3483_);
return v___x_3484_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9(void){
_start:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3485_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8);
v___x_3486_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3);
v___x_3487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3486_);
lean_ctor_set(v___x_3487_, 1, v___x_3485_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(lean_object* v_e_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_){
_start:
{
lean_object* v___y_3500_; lean_object* v___x_3532_; 
v___x_3532_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3488_, v_a_3495_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v___x_3534_; uint8_t v___x_3535_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_a_3533_);
lean_dec_ref_known(v___x_3532_, 1);
v___x_3534_ = l_Lean_Expr_cleanupAnnotations(v_a_3533_);
v___x_3535_ = l_Lean_Expr_isApp(v___x_3534_);
if (v___x_3535_ == 0)
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
lean_dec_ref(v___x_3534_);
v___x_3536_ = lean_box(0);
v___x_3537_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3536_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_);
v___y_3500_ = v___x_3537_;
goto v___jp_3499_;
}
else
{
lean_object* v_arg_3538_; lean_object* v___x_3539_; uint8_t v___x_3540_; 
v_arg_3538_ = lean_ctor_get(v___x_3534_, 1);
lean_inc_ref(v_arg_3538_);
v___x_3539_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3534_);
v___x_3540_ = l_Lean_Expr_isApp(v___x_3539_);
if (v___x_3540_ == 0)
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
lean_dec_ref(v___x_3539_);
lean_dec_ref(v_arg_3538_);
v___x_3541_ = lean_box(0);
v___x_3542_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3541_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_);
v___y_3500_ = v___x_3542_;
goto v___jp_3499_;
}
else
{
lean_object* v_arg_3543_; lean_object* v___x_3544_; uint8_t v___x_3545_; 
v_arg_3543_ = lean_ctor_get(v___x_3539_, 1);
lean_inc_ref(v_arg_3543_);
v___x_3544_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3539_);
v___x_3545_ = l_Lean_Expr_isApp(v___x_3544_);
if (v___x_3545_ == 0)
{
lean_object* v___x_3546_; lean_object* v___x_3547_; 
lean_dec_ref(v___x_3544_);
lean_dec_ref(v_arg_3543_);
lean_dec_ref(v_arg_3538_);
v___x_3546_ = lean_box(0);
v___x_3547_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3546_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_);
v___y_3500_ = v___x_3547_;
goto v___jp_3499_;
}
else
{
lean_object* v_arg_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; uint8_t v___x_3551_; 
v_arg_3548_ = lean_ctor_get(v___x_3544_, 1);
lean_inc_ref(v_arg_3548_);
v___x_3549_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3544_);
v___x_3550_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1));
v___x_3551_ = l_Lean_Expr_isConstOf(v___x_3549_, v___x_3550_);
if (v___x_3551_ == 0)
{
uint8_t v___x_3552_; 
v___x_3552_ = l_Lean_Expr_isApp(v___x_3549_);
if (v___x_3552_ == 0)
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
lean_dec_ref(v___x_3549_);
lean_dec_ref(v_arg_3548_);
lean_dec_ref(v_arg_3543_);
lean_dec_ref(v_arg_3538_);
v___x_3553_ = lean_box(0);
v___x_3554_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3553_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_);
v___y_3500_ = v___x_3554_;
goto v___jp_3499_;
}
else
{
lean_object* v_arg_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; uint8_t v___x_3558_; 
v_arg_3555_ = lean_ctor_get(v___x_3549_, 1);
lean_inc_ref(v_arg_3555_);
v___x_3556_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3549_);
v___x_3557_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2));
v___x_3558_ = l_Lean_Expr_isConstOf(v___x_3556_, v___x_3557_);
lean_dec_ref(v___x_3556_);
if (v___x_3558_ == 0)
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
lean_dec_ref(v_arg_3555_);
lean_dec_ref(v_arg_3548_);
lean_dec_ref(v_arg_3543_);
lean_dec_ref(v_arg_3538_);
v___x_3559_ = lean_box(0);
v___x_3560_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3559_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_);
v___y_3500_ = v___x_3560_;
goto v___jp_3499_;
}
else
{
lean_object* v_options_3561_; lean_object* v_toCold_3562_; uint8_t v_hasTrace_3563_; 
v_options_3561_ = lean_ctor_get(v_a_3496_, 1);
v_toCold_3562_ = lean_ctor_get(v_a_3496_, 0);
v_hasTrace_3563_ = lean_ctor_get_uint8(v_options_3561_, sizeof(void*)*1);
if (v_hasTrace_3563_ == 0)
{
goto v___jp_3564_;
}
else
{
lean_object* v_inheritedTraceOptions_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; uint8_t v___x_3570_; 
v_inheritedTraceOptions_3567_ = lean_ctor_get(v_toCold_3562_, 4);
v___x_3568_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3569_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3570_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3567_, v_options_3561_, v___x_3569_);
if (v___x_3570_ == 0)
{
goto v___jp_3564_;
}
else
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6);
v___x_3572_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3568_, v___x_3571_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; lean_object* v___x_3574_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_a_3573_);
lean_dec_ref_known(v___x_3572_, 1);
v___x_3574_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3555_, v_arg_3548_, v_arg_3543_, v_arg_3538_, v_a_3573_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_);
v___y_3500_ = v___x_3574_;
goto v___jp_3499_;
}
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_dec_ref(v_arg_3555_);
lean_dec_ref(v_arg_3548_);
lean_dec_ref(v_arg_3543_);
lean_dec_ref(v_arg_3538_);
v_a_3575_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3572_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3572_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
}
v___jp_3564_:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = lean_box(0);
v___x_3566_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3555_, v_arg_3548_, v_arg_3543_, v_arg_3538_, v___x_3565_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_);
v___y_3500_ = v___x_3566_;
goto v___jp_3499_;
}
}
}
}
else
{
lean_object* v_options_3583_; lean_object* v_toCold_3584_; uint8_t v_hasTrace_3585_; 
lean_dec_ref(v___x_3549_);
v_options_3583_ = lean_ctor_get(v_a_3496_, 1);
v_toCold_3584_ = lean_ctor_get(v_a_3496_, 0);
v_hasTrace_3585_ = lean_ctor_get_uint8(v_options_3583_, sizeof(void*)*1);
if (v_hasTrace_3585_ == 0)
{
goto v___jp_3586_;
}
else
{
lean_object* v_inheritedTraceOptions_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; uint8_t v___x_3592_; 
v_inheritedTraceOptions_3589_ = lean_ctor_get(v_toCold_3584_, 4);
v___x_3590_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3591_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3592_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3589_, v_options_3583_, v___x_3591_);
if (v___x_3592_ == 0)
{
goto v___jp_3586_;
}
else
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9);
v___x_3594_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3590_, v___x_3593_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; lean_object* v___x_3596_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3595_);
lean_dec_ref_known(v___x_3594_, 1);
v___x_3596_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3548_, v_arg_3543_, v_arg_3538_, v_a_3595_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_);
v___y_3500_ = v___x_3596_;
goto v___jp_3499_;
}
else
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3604_; 
lean_dec_ref(v_arg_3548_);
lean_dec_ref(v_arg_3543_);
lean_dec_ref(v_arg_3538_);
v_a_3597_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3599_ = v___x_3594_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3594_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3602_; 
if (v_isShared_3600_ == 0)
{
v___x_3602_ = v___x_3599_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_a_3597_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
}
}
v___jp_3586_:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3587_ = lean_box(0);
v___x_3588_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3548_, v_arg_3543_, v_arg_3538_, v___x_3587_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_);
v___y_3500_ = v___x_3588_;
goto v___jp_3499_;
}
}
}
}
}
}
else
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3612_; 
v_a_3605_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3607_ = v___x_3532_;
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3532_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3605_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
v___jp_3499_:
{
if (lean_obj_tag(v___y_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3531_; 
v_a_3501_ = lean_ctor_get(v___y_3500_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___y_3500_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3503_ = v___y_3500_;
v_isShared_3504_ = v_isSharedCheck_3531_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___y_3500_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3531_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
if (lean_obj_tag(v_a_3501_) == 0)
{
uint8_t v_contextDependent_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3516_; 
v_contextDependent_3505_ = lean_ctor_get_uint8(v_a_3501_, 1);
v_isSharedCheck_3516_ = !lean_is_exclusive(v_a_3501_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3507_ = v_a_3501_;
v_isShared_3508_ = v_isSharedCheck_3516_;
goto v_resetjp_3506_;
}
else
{
lean_dec(v_a_3501_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3516_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
uint8_t v___x_3509_; lean_object* v___x_3511_; 
v___x_3509_ = 1;
if (v_isShared_3508_ == 0)
{
v___x_3511_ = v___x_3507_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_3515_, 1, v_contextDependent_3505_);
v___x_3511_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
lean_object* v___x_3513_; 
lean_ctor_set_uint8(v___x_3511_, 0, v___x_3509_);
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 0, v___x_3511_);
v___x_3513_ = v___x_3503_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
else
{
lean_object* v_e_x27_3517_; lean_object* v_proof_3518_; uint8_t v_contextDependent_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3530_; 
v_e_x27_3517_ = lean_ctor_get(v_a_3501_, 0);
v_proof_3518_ = lean_ctor_get(v_a_3501_, 1);
v_contextDependent_3519_ = lean_ctor_get_uint8(v_a_3501_, sizeof(void*)*2 + 1);
v_isSharedCheck_3530_ = !lean_is_exclusive(v_a_3501_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3521_ = v_a_3501_;
v_isShared_3522_ = v_isSharedCheck_3530_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_proof_3518_);
lean_inc(v_e_x27_3517_);
lean_dec(v_a_3501_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3530_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
uint8_t v___x_3523_; lean_object* v___x_3525_; 
v___x_3523_ = 1;
if (v_isShared_3522_ == 0)
{
v___x_3525_ = v___x_3521_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_e_x27_3517_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v_proof_3518_);
lean_ctor_set_uint8(v_reuseFailAlloc_3529_, sizeof(void*)*2 + 1, v_contextDependent_3519_);
v___x_3525_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
lean_object* v___x_3527_; 
lean_ctor_set_uint8(v___x_3525_, sizeof(void*)*2, v___x_3523_);
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 0, v___x_3525_);
v___x_3527_ = v___x_3503_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
}
}
else
{
return v___y_3500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed(lean_object* v_e_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(v_e_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_);
lean_dec(v_a_3622_);
lean_dec_ref(v_a_3621_);
lean_dec(v_a_3620_);
lean_dec_ref(v_a_3619_);
lean_dec(v_a_3618_);
lean_dec_ref(v_a_3617_);
lean_dec(v_a_3616_);
lean_dec_ref(v_a_3615_);
lean_dec(v_a_3614_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(lean_object* v_x_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v___x_3638_; 
lean_inc(v___y_3632_);
lean_inc_ref(v___y_3631_);
lean_inc(v___y_3630_);
lean_inc_ref(v___y_3629_);
lean_inc(v___y_3628_);
lean_inc(v___y_3627_);
lean_inc_ref(v___y_3626_);
v___x_3638_ = lean_apply_12(v_x_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, lean_box(0));
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed(lean_object* v_x_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(v_x_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3643_);
lean_dec(v___y_3642_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object* v_mvarId_3653_, lean_object* v_x_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v___f_3667_; lean_object* v___x_3668_; 
lean_inc(v___y_3661_);
lean_inc_ref(v___y_3660_);
lean_inc(v___y_3659_);
lean_inc_ref(v___y_3658_);
lean_inc(v___y_3657_);
lean_inc(v___y_3656_);
lean_inc_ref(v___y_3655_);
v___f_3667_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_3667_, 0, v_x_3654_);
lean_closure_set(v___f_3667_, 1, v___y_3655_);
lean_closure_set(v___f_3667_, 2, v___y_3656_);
lean_closure_set(v___f_3667_, 3, v___y_3657_);
lean_closure_set(v___f_3667_, 4, v___y_3658_);
lean_closure_set(v___f_3667_, 5, v___y_3659_);
lean_closure_set(v___f_3667_, 6, v___y_3660_);
lean_closure_set(v___f_3667_, 7, v___y_3661_);
v___x_3668_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3653_, v___f_3667_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
if (lean_obj_tag(v___x_3668_) == 0)
{
return v___x_3668_;
}
else
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3676_; 
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3671_ = v___x_3668_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3668_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3674_; 
if (v_isShared_3672_ == 0)
{
v___x_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3669_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object* v_mvarId_3677_, lean_object* v_x_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_mvarId_3677_, v_x_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec(v___y_3681_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(lean_object* v_00_u03b1_3692_, lean_object* v_mvarId_3693_, lean_object* v_x_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v___x_3707_; 
v___x_3707_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_mvarId_3693_, v_x_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object* v_00_u03b1_3708_, lean_object* v_mvarId_3709_, lean_object* v_x_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(v_00_u03b1_3708_, v_mvarId_3709_, v_x_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v___y_3713_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0(lean_object* v_x_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3735_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_3736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3735_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0___boxed(lean_object* v_x_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v_res_3748_; 
v_res_3748_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0(v_x_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
lean_dec(v___y_3746_);
lean_dec_ref(v___y_3745_);
lean_dec(v___y_3744_);
lean_dec_ref(v___y_3743_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v_x_3737_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(lean_object* v_snd_3749_, lean_object* v_a_3750_, lean_object* v___x_3751_, lean_object* v_____r_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3765_ = lean_array_push(v_snd_3749_, v_a_3750_);
v___x_3766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3751_);
lean_ctor_set(v___x_3766_, 1, v___x_3765_);
v___x_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3766_);
v___x_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3767_);
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1___boxed(lean_object* v_snd_3769_, lean_object* v_a_3770_, lean_object* v___x_3771_, lean_object* v_____r_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(v_snd_3769_, v_a_3770_, v___x_3771_, v_____r_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec(v___y_3777_);
lean_dec_ref(v___y_3776_);
lean_dec(v___y_3775_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object* v_cls_3786_, lean_object* v_msg_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v_ref_3793_; lean_object* v___x_3794_; lean_object* v_a_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3839_; 
v_ref_3793_ = lean_ctor_get(v___y_3790_, 4);
v___x_3794_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3797_ = v___x_3794_;
v_isShared_3798_ = v_isSharedCheck_3839_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_a_3795_);
lean_dec(v___x_3794_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3839_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3799_; lean_object* v_traceState_3800_; lean_object* v_env_3801_; lean_object* v_nextMacroScope_3802_; lean_object* v_ngen_3803_; lean_object* v_auxDeclNGen_3804_; lean_object* v_cache_3805_; lean_object* v_messages_3806_; lean_object* v_infoState_3807_; lean_object* v_snapshotTasks_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3838_; 
v___x_3799_ = lean_st_ref_take(v___y_3791_);
v_traceState_3800_ = lean_ctor_get(v___x_3799_, 4);
v_env_3801_ = lean_ctor_get(v___x_3799_, 0);
v_nextMacroScope_3802_ = lean_ctor_get(v___x_3799_, 1);
v_ngen_3803_ = lean_ctor_get(v___x_3799_, 2);
v_auxDeclNGen_3804_ = lean_ctor_get(v___x_3799_, 3);
v_cache_3805_ = lean_ctor_get(v___x_3799_, 5);
v_messages_3806_ = lean_ctor_get(v___x_3799_, 6);
v_infoState_3807_ = lean_ctor_get(v___x_3799_, 7);
v_snapshotTasks_3808_ = lean_ctor_get(v___x_3799_, 8);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3810_ = v___x_3799_;
v_isShared_3811_ = v_isSharedCheck_3838_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_snapshotTasks_3808_);
lean_inc(v_infoState_3807_);
lean_inc(v_messages_3806_);
lean_inc(v_cache_3805_);
lean_inc(v_traceState_3800_);
lean_inc(v_auxDeclNGen_3804_);
lean_inc(v_ngen_3803_);
lean_inc(v_nextMacroScope_3802_);
lean_inc(v_env_3801_);
lean_dec(v___x_3799_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3838_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
uint64_t v_tid_3812_; lean_object* v_traces_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3837_; 
v_tid_3812_ = lean_ctor_get_uint64(v_traceState_3800_, sizeof(void*)*1);
v_traces_3813_ = lean_ctor_get(v_traceState_3800_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v_traceState_3800_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3815_ = v_traceState_3800_;
v_isShared_3816_ = v_isSharedCheck_3837_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_traces_3813_);
lean_dec(v_traceState_3800_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3837_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3817_; double v___x_3818_; uint8_t v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3827_; 
v___x_3817_ = lean_box(0);
v___x_3818_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_3819_ = 0;
v___x_3820_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_3821_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3821_, 0, v_cls_3786_);
lean_ctor_set(v___x_3821_, 1, v___x_3817_);
lean_ctor_set(v___x_3821_, 2, v___x_3820_);
lean_ctor_set_float(v___x_3821_, sizeof(void*)*3, v___x_3818_);
lean_ctor_set_float(v___x_3821_, sizeof(void*)*3 + 8, v___x_3818_);
lean_ctor_set_uint8(v___x_3821_, sizeof(void*)*3 + 16, v___x_3819_);
v___x_3822_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_3823_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3821_);
lean_ctor_set(v___x_3823_, 1, v_a_3795_);
lean_ctor_set(v___x_3823_, 2, v___x_3822_);
lean_inc(v_ref_3793_);
v___x_3824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3824_, 0, v_ref_3793_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
v___x_3825_ = l_Lean_PersistentArray_push___redArg(v_traces_3813_, v___x_3824_);
if (v_isShared_3816_ == 0)
{
lean_ctor_set(v___x_3815_, 0, v___x_3825_);
v___x_3827_ = v___x_3815_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3825_);
lean_ctor_set_uint64(v_reuseFailAlloc_3836_, sizeof(void*)*1, v_tid_3812_);
v___x_3827_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
lean_object* v___x_3829_; 
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 4, v___x_3827_);
v___x_3829_ = v___x_3810_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_env_3801_);
lean_ctor_set(v_reuseFailAlloc_3835_, 1, v_nextMacroScope_3802_);
lean_ctor_set(v_reuseFailAlloc_3835_, 2, v_ngen_3803_);
lean_ctor_set(v_reuseFailAlloc_3835_, 3, v_auxDeclNGen_3804_);
lean_ctor_set(v_reuseFailAlloc_3835_, 4, v___x_3827_);
lean_ctor_set(v_reuseFailAlloc_3835_, 5, v_cache_3805_);
lean_ctor_set(v_reuseFailAlloc_3835_, 6, v_messages_3806_);
lean_ctor_set(v_reuseFailAlloc_3835_, 7, v_infoState_3807_);
lean_ctor_set(v_reuseFailAlloc_3835_, 8, v_snapshotTasks_3808_);
v___x_3829_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3833_; 
v___x_3830_ = lean_st_ref_put(v___y_3791_, v___x_3829_);
v___x_3831_ = lean_box(0);
if (v_isShared_3798_ == 0)
{
lean_ctor_set(v___x_3797_, 0, v___x_3831_);
v___x_3833_ = v___x_3797_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3831_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object* v_cls_3840_, lean_object* v_msg_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v_res_3847_; 
v_res_3847_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_cls_3840_, v_msg_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(uint8_t v___x_3848_, lean_object* v___f_3849_, lean_object* v_____r_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v___x_3863_; lean_object* v_caches_3864_; lean_object* v_typeAnalysis_3865_; lean_object* v_target_3866_; lean_object* v_hypotheses_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3877_; 
v___x_3863_ = lean_st_ref_take(v___y_3852_);
v_caches_3864_ = lean_ctor_get(v___x_3863_, 0);
v_typeAnalysis_3865_ = lean_ctor_get(v___x_3863_, 1);
v_target_3866_ = lean_ctor_get(v___x_3863_, 2);
v_hypotheses_3867_ = lean_ctor_get(v___x_3863_, 3);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3869_ = v___x_3863_;
v_isShared_3870_ = v_isSharedCheck_3877_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_hypotheses_3867_);
lean_inc(v_target_3866_);
lean_inc(v_typeAnalysis_3865_);
lean_inc(v_caches_3864_);
lean_dec(v___x_3863_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3877_;
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
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_caches_3864_);
lean_ctor_set(v_reuseFailAlloc_3876_, 1, v_typeAnalysis_3865_);
lean_ctor_set(v_reuseFailAlloc_3876_, 2, v_target_3866_);
lean_ctor_set(v_reuseFailAlloc_3876_, 3, v_hypotheses_3867_);
v___x_3872_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
lean_ctor_set_uint8(v___x_3872_, sizeof(void*)*4, v___x_3848_);
v___x_3873_ = lean_st_ref_put(v___y_3852_, v___x_3872_);
v___x_3874_ = lean_box(0);
lean_inc(v___y_3861_);
lean_inc_ref(v___y_3860_);
lean_inc(v___y_3859_);
lean_inc_ref(v___y_3858_);
lean_inc(v___y_3857_);
lean_inc_ref(v___y_3856_);
lean_inc(v___y_3855_);
lean_inc_ref(v___y_3854_);
lean_inc(v___y_3853_);
lean_inc(v___y_3852_);
lean_inc_ref(v___y_3851_);
v___x_3875_ = lean_apply_13(v___f_3849_, v___x_3874_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, lean_box(0));
return v___x_3875_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2___boxed(lean_object* v___x_3878_, lean_object* v___f_3879_, lean_object* v_____r_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
uint8_t v___x_10032__boxed_3893_; lean_object* v_res_3894_; 
v___x_10032__boxed_3893_ = lean_unbox(v___x_3878_);
v_res_3894_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_10032__boxed_3893_, v___f_3879_, v_____r_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v___y_3888_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3881_);
return v_res_3894_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3896_; lean_object* v___f_3897_; lean_object* v_methods_3898_; 
v___x_3896_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed), 11, 0);
v___f_3897_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__0));
v_methods_3898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_methods_3898_, 0, v___f_3897_);
lean_ctor_set(v_methods_3898_, 1, v___x_3896_);
return v_methods_3898_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3900_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__2));
v___x_3901_ = l_Lean_stringToMessageData(v___x_3900_);
return v___x_3901_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object* v_upperBound_3902_, lean_object* v___x_3903_, lean_object* v_config_3904_, lean_object* v_a_3905_, lean_object* v_b_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
lean_object* v___y_3920_; uint8_t v___x_3942_; 
v___x_3942_ = lean_nat_dec_lt(v_a_3905_, v_upperBound_3902_);
if (v___x_3942_ == 0)
{
lean_object* v___x_3943_; 
lean_dec(v_a_3905_);
lean_dec_ref(v_config_3904_);
v___x_3943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3943_, 0, v_b_3906_);
return v___x_3943_;
}
else
{
uint8_t v___x_3944_; lean_object* v_methods_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3944_ = 1;
v_methods_3945_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1);
v___x_3946_ = lean_array_fget_borrowed(v___x_3903_, v_a_3905_);
lean_inc(v___x_3946_);
lean_inc_ref(v_config_3904_);
v___x_3947_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v___x_3944_, v_methods_3945_, v_config_3904_, v___x_3946_, v___y_3908_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v_a_3948_; lean_object* v_snd_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_4012_; 
v_a_3948_ = lean_ctor_get(v___x_3947_, 0);
lean_inc(v_a_3948_);
lean_dec_ref_known(v___x_3947_, 1);
v_snd_3949_ = lean_ctor_get(v_b_3906_, 1);
v_isSharedCheck_4012_ = !lean_is_exclusive(v_b_3906_);
if (v_isSharedCheck_4012_ == 0)
{
lean_object* v_unused_4013_; 
v_unused_4013_ = lean_ctor_get(v_b_3906_, 0);
lean_dec(v_unused_4013_);
v___x_3951_ = v_b_3906_;
v_isShared_3952_ = v_isSharedCheck_4012_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_snd_3949_);
lean_dec(v_b_3906_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_4012_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v_type_3953_; lean_object* v_value_3954_; uint8_t v___x_3955_; 
v_type_3953_ = lean_ctor_get(v_a_3948_, 1);
v_value_3954_ = lean_ctor_get(v_a_3948_, 2);
lean_inc_ref(v_type_3953_);
v___x_3955_ = l_Lean_Expr_isFalse(v_type_3953_);
if (v___x_3955_ == 0)
{
lean_object* v_type_3956_; lean_object* v___x_3957_; lean_object* v___f_3958_; uint8_t v___x_3987_; 
lean_del_object(v___x_3951_);
v_type_3956_ = lean_ctor_get(v___x_3946_, 1);
v___x_3957_ = lean_box(0);
lean_inc(v_a_3948_);
lean_inc(v_snd_3949_);
v___f_3958_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1___boxed), 16, 3);
lean_closure_set(v___f_3958_, 0, v_snd_3949_);
lean_closure_set(v___f_3958_, 1, v_a_3948_);
lean_closure_set(v___f_3958_, 2, v___x_3957_);
v___x_3987_ = lean_expr_eqv(v_type_3956_, v_type_3953_);
if (v___x_3987_ == 0)
{
lean_inc_ref(v_type_3953_);
lean_dec(v_snd_3949_);
lean_dec(v_a_3948_);
goto v___jp_3962_;
}
else
{
if (v___x_3955_ == 0)
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
lean_dec_ref(v___f_3958_);
v___x_3988_ = lean_box(0);
v___x_3989_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(v_snd_3949_, v_a_3948_, v___x_3957_, v___x_3988_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
v___y_3920_ = v___x_3989_;
goto v___jp_3919_;
}
else
{
lean_inc_ref(v_type_3953_);
lean_dec(v_snd_3949_);
lean_dec(v_a_3948_);
goto v___jp_3962_;
}
}
v___jp_3959_:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3960_ = lean_box(0);
v___x_3961_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_3942_, v___f_3958_, v___x_3960_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
v___y_3920_ = v___x_3961_;
goto v___jp_3919_;
}
v___jp_3962_:
{
lean_object* v_options_3963_; uint8_t v_hasTrace_3964_; 
v_options_3963_ = lean_ctor_get(v___y_3916_, 1);
v_hasTrace_3964_ = lean_ctor_get_uint8(v_options_3963_, sizeof(void*)*1);
if (v_hasTrace_3964_ == 0)
{
lean_dec_ref(v_type_3953_);
goto v___jp_3959_;
}
else
{
lean_object* v_toCold_3965_; lean_object* v_inheritedTraceOptions_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; uint8_t v___x_3969_; 
v_toCold_3965_ = lean_ctor_get(v___y_3916_, 0);
v_inheritedTraceOptions_3966_ = lean_ctor_get(v_toCold_3965_, 4);
v___x_3967_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3968_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3969_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3966_, v_options_3963_, v___x_3968_);
if (v___x_3969_ == 0)
{
lean_dec_ref(v_type_3953_);
goto v___jp_3959_;
}
else
{
lean_object* v_type_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v_type_3970_ = lean_ctor_get(v___x_3946_, 1);
lean_inc_ref(v_type_3970_);
v___x_3971_ = l_Lean_MessageData_ofExpr(v_type_3970_);
v___x_3972_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3);
v___x_3973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3971_);
lean_ctor_set(v___x_3973_, 1, v___x_3972_);
v___x_3974_ = l_Lean_MessageData_ofExpr(v_type_3953_);
v___x_3975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3975_, 0, v___x_3973_);
lean_ctor_set(v___x_3975_, 1, v___x_3974_);
v___x_3976_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v___x_3967_, v___x_3975_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v___x_3978_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref_known(v___x_3976_, 1);
v___x_3978_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_3942_, v___f_3958_, v_a_3977_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
v___y_3920_ = v___x_3978_;
goto v___jp_3919_;
}
else
{
lean_object* v_a_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_3986_; 
lean_dec_ref(v___f_3958_);
lean_dec(v_a_3905_);
lean_dec_ref(v_config_3904_);
v_a_3979_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3981_ = v___x_3976_;
v_isShared_3982_ = v_isSharedCheck_3986_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_a_3979_);
lean_dec(v___x_3976_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_3986_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v___x_3984_; 
if (v_isShared_3982_ == 0)
{
v___x_3984_ = v___x_3981_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_a_3979_);
v___x_3984_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
return v___x_3984_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3990_; 
lean_inc_ref(v_value_3954_);
lean_dec(v_a_3948_);
lean_dec(v_a_3905_);
lean_dec_ref(v_config_3904_);
v___x_3990_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_3954_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_4002_; 
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4002_ == 0)
{
lean_object* v_unused_4003_; 
v_unused_4003_ = lean_ctor_get(v___x_3990_, 0);
lean_dec(v_unused_4003_);
v___x_3992_ = v___x_3990_;
v_isShared_3993_ = v_isSharedCheck_4002_;
goto v_resetjp_3991_;
}
else
{
lean_dec(v___x_3990_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_4002_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3997_; 
v___x_3994_ = lean_box(v___x_3942_);
v___x_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3994_);
if (v_isShared_3952_ == 0)
{
lean_ctor_set(v___x_3951_, 0, v___x_3995_);
v___x_3997_ = v___x_3951_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v___x_3995_);
lean_ctor_set(v_reuseFailAlloc_4001_, 1, v_snd_3949_);
v___x_3997_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
lean_object* v___x_3999_; 
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 0, v___x_3997_);
v___x_3999_ = v___x_3992_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___x_3997_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4011_; 
lean_del_object(v___x_3951_);
lean_dec(v_snd_3949_);
v_a_4004_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4006_ = v___x_3990_;
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_3990_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4009_; 
if (v_isShared_4007_ == 0)
{
v___x_4009_ = v___x_4006_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
}
}
else
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4021_; 
lean_dec_ref(v_b_3906_);
lean_dec(v_a_3905_);
lean_dec_ref(v_config_3904_);
v_a_4014_ = lean_ctor_get(v___x_3947_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_3947_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4016_ = v___x_3947_;
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_3947_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_4014_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
}
}
v___jp_3919_:
{
if (lean_obj_tag(v___y_3920_) == 0)
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3933_; 
v_a_3921_ = lean_ctor_get(v___y_3920_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___y_3920_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3923_ = v___y_3920_;
v_isShared_3924_ = v_isSharedCheck_3933_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___y_3920_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3933_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
if (lean_obj_tag(v_a_3921_) == 0)
{
lean_object* v_a_3925_; lean_object* v___x_3927_; 
lean_dec(v_a_3905_);
lean_dec_ref(v_config_3904_);
v_a_3925_ = lean_ctor_get(v_a_3921_, 0);
lean_inc(v_a_3925_);
lean_dec_ref_known(v_a_3921_, 1);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 0, v_a_3925_);
v___x_3927_ = v___x_3923_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3925_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
else
{
lean_object* v_a_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
lean_del_object(v___x_3923_);
v_a_3929_ = lean_ctor_get(v_a_3921_, 0);
lean_inc(v_a_3929_);
lean_dec_ref_known(v_a_3921_, 1);
v___x_3930_ = lean_unsigned_to_nat(1u);
v___x_3931_ = lean_nat_add(v_a_3905_, v___x_3930_);
lean_dec(v_a_3905_);
v_a_3905_ = v___x_3931_;
v_b_3906_ = v_a_3929_;
goto _start;
}
}
}
else
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3941_; 
lean_dec(v_a_3905_);
lean_dec_ref(v_config_3904_);
v_a_3934_ = lean_ctor_get(v___y_3920_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___y_3920_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3936_ = v___y_3920_;
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___y_3920_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_a_3934_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_4022_ = _args[0];
lean_object* v___x_4023_ = _args[1];
lean_object* v_config_4024_ = _args[2];
lean_object* v_a_4025_ = _args[3];
lean_object* v_b_4026_ = _args[4];
lean_object* v___y_4027_ = _args[5];
lean_object* v___y_4028_ = _args[6];
lean_object* v___y_4029_ = _args[7];
lean_object* v___y_4030_ = _args[8];
lean_object* v___y_4031_ = _args[9];
lean_object* v___y_4032_ = _args[10];
lean_object* v___y_4033_ = _args[11];
lean_object* v___y_4034_ = _args[12];
lean_object* v___y_4035_ = _args[13];
lean_object* v___y_4036_ = _args[14];
lean_object* v___y_4037_ = _args[15];
lean_object* v___y_4038_ = _args[16];
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_upperBound_4022_, v___x_4023_, v_config_4024_, v_a_4025_, v_b_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
lean_dec(v___y_4037_);
lean_dec_ref(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec(v___y_4029_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
lean_dec_ref(v___x_4023_);
lean_dec(v_upperBound_4022_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(lean_object* v_config_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
lean_object* v___x_4053_; lean_object* v_hypotheses_4054_; lean_object* v___x_4055_; lean_object* v_newHyps_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4053_ = lean_st_ref_get(v___y_4042_);
v_hypotheses_4054_ = lean_ctor_get(v___x_4053_, 3);
lean_inc_ref(v_hypotheses_4054_);
lean_dec(v___x_4053_);
v___x_4055_ = lean_array_get_size(v_hypotheses_4054_);
v_newHyps_4056_ = lean_mk_empty_array_with_capacity(v___x_4055_);
v___x_4057_ = lean_unsigned_to_nat(0u);
v___x_4058_ = lean_box(0);
v___x_4059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4058_);
lean_ctor_set(v___x_4059_, 1, v_newHyps_4056_);
v___x_4060_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v___x_4055_, v_hypotheses_4054_, v_config_4040_, v___x_4057_, v___x_4059_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
lean_dec_ref(v_hypotheses_4054_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4090_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4063_ = v___x_4060_;
v_isShared_4064_ = v_isSharedCheck_4090_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4060_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4090_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v_fst_4065_; 
v_fst_4065_ = lean_ctor_get(v_a_4061_, 0);
if (lean_obj_tag(v_fst_4065_) == 0)
{
lean_object* v_snd_4066_; lean_object* v___x_4067_; lean_object* v_caches_4068_; lean_object* v_typeAnalysis_4069_; lean_object* v_target_4070_; uint8_t v_didChange_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4084_; 
v_snd_4066_ = lean_ctor_get(v_a_4061_, 1);
lean_inc(v_snd_4066_);
lean_dec(v_a_4061_);
v___x_4067_ = lean_st_ref_take(v___y_4042_);
v_caches_4068_ = lean_ctor_get(v___x_4067_, 0);
v_typeAnalysis_4069_ = lean_ctor_get(v___x_4067_, 1);
v_target_4070_ = lean_ctor_get(v___x_4067_, 2);
v_didChange_4071_ = lean_ctor_get_uint8(v___x_4067_, sizeof(void*)*4);
v_isSharedCheck_4084_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4084_ == 0)
{
lean_object* v_unused_4085_; 
v_unused_4085_ = lean_ctor_get(v___x_4067_, 3);
lean_dec(v_unused_4085_);
v___x_4073_ = v___x_4067_;
v_isShared_4074_ = v_isSharedCheck_4084_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_target_4070_);
lean_inc(v_typeAnalysis_4069_);
lean_inc(v_caches_4068_);
lean_dec(v___x_4067_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4084_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
lean_ctor_set(v___x_4073_, 3, v_snd_4066_);
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_caches_4068_);
lean_ctor_set(v_reuseFailAlloc_4083_, 1, v_typeAnalysis_4069_);
lean_ctor_set(v_reuseFailAlloc_4083_, 2, v_target_4070_);
lean_ctor_set(v_reuseFailAlloc_4083_, 3, v_snd_4066_);
lean_ctor_set_uint8(v_reuseFailAlloc_4083_, sizeof(void*)*4, v_didChange_4071_);
v___x_4076_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
lean_object* v___x_4077_; uint8_t v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4081_; 
v___x_4077_ = lean_st_ref_put(v___y_4042_, v___x_4076_);
v___x_4078_ = 0;
v___x_4079_ = lean_box(v___x_4078_);
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 0, v___x_4079_);
v___x_4081_ = v___x_4063_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v___x_4079_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
}
else
{
lean_object* v_val_4086_; lean_object* v___x_4088_; 
lean_inc_ref(v_fst_4065_);
lean_dec(v_a_4061_);
v_val_4086_ = lean_ctor_get(v_fst_4065_, 0);
lean_inc(v_val_4086_);
lean_dec_ref_known(v_fst_4065_, 1);
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 0, v_val_4086_);
v___x_4088_ = v___x_4063_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_val_4086_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
}
else
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4098_; 
v_a_4091_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4093_ = v___x_4060_;
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v___x_4060_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4096_; 
if (v_isShared_4094_ == 0)
{
v___x_4096_ = v___x_4093_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4091_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed(lean_object* v_config_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(v_config_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v_config_4125_; lean_object* v___x_4126_; lean_object* v_maxSteps_4127_; lean_object* v_target_4128_; lean_object* v___x_4129_; lean_object* v_config_4130_; lean_object* v___f_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; 
v_config_4125_ = lean_ctor_get(v___y_4113_, 0);
v___x_4126_ = lean_st_ref_get(v___y_4114_);
v_maxSteps_4127_ = lean_ctor_get(v_config_4125_, 1);
v_target_4128_ = lean_ctor_get(v___x_4126_, 2);
lean_inc_ref(v_target_4128_);
lean_dec(v___x_4126_);
v___x_4129_ = lean_unsigned_to_nat(2u);
lean_inc(v_maxSteps_4127_);
v_config_4130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_config_4130_, 0, v_maxSteps_4127_);
lean_ctor_set(v_config_4130_, 1, v___x_4129_);
v___f_4131_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed), 13, 1);
lean_closure_set(v___f_4131_, 0, v_config_4130_);
v___x_4132_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_4128_);
lean_dec_ref(v_target_4128_);
v___x_4133_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v___x_4132_, v___f_4131_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___boxed(lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(lean_object* v_cls_4155_, lean_object* v_msg_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
lean_object* v___x_4169_; 
v___x_4169_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_cls_4155_, v_msg_4156_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___boxed(lean_object* v_cls_4170_, lean_object* v_msg_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_){
_start:
{
lean_object* v_res_4184_; 
v_res_4184_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(v_cls_4170_, v_msg_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_);
lean_dec(v___y_4182_);
lean_dec_ref(v___y_4181_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4179_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
return v_res_4184_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(lean_object* v_upperBound_4185_, lean_object* v___x_4186_, lean_object* v_config_4187_, lean_object* v_inst_4188_, lean_object* v_R_4189_, lean_object* v_a_4190_, lean_object* v_b_4191_, lean_object* v_c_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v___x_4205_; 
v___x_4205_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_upperBound_4185_, v___x_4186_, v_config_4187_, v_a_4190_, v_b_4191_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_4206_ = _args[0];
lean_object* v___x_4207_ = _args[1];
lean_object* v_config_4208_ = _args[2];
lean_object* v_inst_4209_ = _args[3];
lean_object* v_R_4210_ = _args[4];
lean_object* v_a_4211_ = _args[5];
lean_object* v_b_4212_ = _args[6];
lean_object* v_c_4213_ = _args[7];
lean_object* v___y_4214_ = _args[8];
lean_object* v___y_4215_ = _args[9];
lean_object* v___y_4216_ = _args[10];
lean_object* v___y_4217_ = _args[11];
lean_object* v___y_4218_ = _args[12];
lean_object* v___y_4219_ = _args[13];
lean_object* v___y_4220_ = _args[14];
lean_object* v___y_4221_ = _args[15];
lean_object* v___y_4222_ = _args[16];
lean_object* v___y_4223_ = _args[17];
lean_object* v___y_4224_ = _args[18];
lean_object* v___y_4225_ = _args[19];
_start:
{
lean_object* v_res_4226_; 
v_res_4226_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(v_upperBound_4206_, v___x_4207_, v_config_4208_, v_inst_4209_, v_R_4210_, v_a_4211_, v_b_4212_, v_c_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec_ref(v___x_4207_);
lean_dec(v_upperBound_4206_);
return v_res_4226_;
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
