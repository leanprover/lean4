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
v_options_495_ = lean_ctor_get(v___y_487_, 2);
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
v_ref_512_ = lean_ctor_get(v___y_509_, 5);
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
v_ref_849_ = lean_ctor_get(v___y_846_, 5);
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
v_options_947_ = lean_ctor_get(v_a_939_, 2);
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
lean_object* v_inheritedTraceOptions_950_; lean_object* v_cls_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
v_inheritedTraceOptions_950_ = lean_ctor_get(v_a_939_, 13);
v_cls_951_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_952_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_953_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_950_, v_options_947_, v___x_952_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; 
lean_dec_ref(v_op_931_);
v___x_954_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_932_, v_a_933_, v_a_934_);
return v___x_954_;
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_955_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8);
lean_inc_ref(v_fn_944_);
v___x_956_ = l_Lean_MessageData_ofExpr(v_fn_944_);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10);
v___x_959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
lean_inc_ref(v_arg_945_);
v___x_960_ = l_Lean_MessageData_ofExpr(v_arg_945_);
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
lean_ctor_set(v___x_962_, 1, v___x_958_);
lean_inc_ref(v_arg_943_);
v___x_963_ = l_Lean_MessageData_ofExpr(v_arg_943_);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_931_);
v___x_968_ = l_Lean_MessageData_ofExpr(v___x_967_);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_966_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_951_, v___x_971_, v_a_934_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v_snd_974_; lean_object* v___x_975_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
lean_dec_ref_known(v___x_972_, 1);
v_snd_974_ = lean_ctor_get(v_a_973_, 1);
lean_inc(v_snd_974_);
lean_dec(v_a_973_);
v___x_975_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_932_, v_a_933_, v_snd_974_);
return v___x_975_;
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec_ref_known(v_a_933_, 2);
lean_dec_ref(v_coeff_932_);
v_a_976_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_972_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_972_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
}
}
else
{
lean_object* v___x_984_; 
lean_inc_ref(v_arg_945_);
lean_inc_ref(v_arg_943_);
lean_dec_ref_known(v_a_933_, 2);
lean_inc_ref(v_op_931_);
v___x_984_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_931_, v_coeff_932_, v_arg_945_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v_fst_986_; lean_object* v_snd_987_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
v_fst_986_ = lean_ctor_get(v_a_985_, 0);
lean_inc(v_fst_986_);
v_snd_987_ = lean_ctor_get(v_a_985_, 1);
lean_inc(v_snd_987_);
lean_dec(v_a_985_);
v_coeff_932_ = v_fst_986_;
v_a_933_ = v_arg_943_;
v_a_934_ = v_snd_987_;
goto _start;
}
else
{
lean_dec_ref(v_arg_943_);
lean_dec_ref(v_op_931_);
return v___x_984_;
}
}
}
else
{
lean_object* v___x_989_; 
lean_dec_ref(v_op_931_);
v___x_989_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_932_, v_a_933_, v_a_934_);
return v___x_989_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___boxed(lean_object* v_op_991_, lean_object* v_coeff_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_991_, v_coeff_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(lean_object* v_cls_1003_, lean_object* v_msg_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_1003_, v_msg_1004_, v___y_1005_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___boxed(lean_object* v_cls_1014_, lean_object* v_msg_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(v_cls_1014_, v_msg_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
return v_res_1024_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = lean_box(0);
v___x_1026_ = lean_unsigned_to_nat(16u);
v___x_1027_ = lean_mk_array(v___x_1026_, v___x_1025_);
return v___x_1027_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1029_ = lean_unsigned_to_nat(0u);
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v___x_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(lean_object* v_op_1031_, lean_object* v_e_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1042_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_1031_, v___x_1041_, v_e_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___boxed(lean_object* v_op_1043_, lean_object* v_e_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_op_1043_, v_e_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(lean_object* v_a_1054_, lean_object* v_x_1055_){
_start:
{
if (lean_obj_tag(v_x_1055_) == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_box(0);
return v___x_1056_;
}
else
{
lean_object* v_key_1057_; lean_object* v_value_1058_; lean_object* v_tail_1059_; uint8_t v___x_1060_; 
v_key_1057_ = lean_ctor_get(v_x_1055_, 0);
v_value_1058_ = lean_ctor_get(v_x_1055_, 1);
v_tail_1059_ = lean_ctor_get(v_x_1055_, 2);
v___x_1060_ = lean_nat_dec_eq(v_key_1057_, v_a_1054_);
if (v___x_1060_ == 0)
{
v_x_1055_ = v_tail_1059_;
goto _start;
}
else
{
lean_object* v___x_1062_; 
lean_inc(v_value_1058_);
v___x_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1062_, 0, v_value_1058_);
return v___x_1062_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg___boxed(lean_object* v_a_1063_, lean_object* v_x_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1063_, v_x_1064_);
lean_dec(v_x_1064_);
lean_dec(v_a_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(lean_object* v_m_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_buckets_1068_; lean_object* v___x_1069_; uint64_t v___x_1070_; uint64_t v___x_1071_; uint64_t v___x_1072_; uint64_t v_fold_1073_; uint64_t v___x_1074_; uint64_t v___x_1075_; uint64_t v___x_1076_; size_t v___x_1077_; size_t v___x_1078_; size_t v___x_1079_; size_t v___x_1080_; size_t v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v_buckets_1068_ = lean_ctor_get(v_m_1066_, 1);
v___x_1069_ = lean_array_get_size(v_buckets_1068_);
v___x_1070_ = lean_uint64_of_nat(v_a_1067_);
v___x_1071_ = 32ULL;
v___x_1072_ = lean_uint64_shift_right(v___x_1070_, v___x_1071_);
v_fold_1073_ = lean_uint64_xor(v___x_1070_, v___x_1072_);
v___x_1074_ = 16ULL;
v___x_1075_ = lean_uint64_shift_right(v_fold_1073_, v___x_1074_);
v___x_1076_ = lean_uint64_xor(v_fold_1073_, v___x_1075_);
v___x_1077_ = lean_uint64_to_usize(v___x_1076_);
v___x_1078_ = lean_usize_of_nat(v___x_1069_);
v___x_1079_ = ((size_t)1ULL);
v___x_1080_ = lean_usize_sub(v___x_1078_, v___x_1079_);
v___x_1081_ = lean_usize_land(v___x_1077_, v___x_1080_);
v___x_1082_ = lean_array_uget_borrowed(v_buckets_1068_, v___x_1081_);
v___x_1083_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1067_, v___x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg___boxed(lean_object* v_m_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1084_, v_a_1085_);
lean_dec(v_a_1085_);
lean_dec_ref(v_m_1084_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(lean_object* v_a_1087_, lean_object* v_b_1088_, lean_object* v_x_1089_){
_start:
{
if (lean_obj_tag(v_x_1089_) == 0)
{
lean_dec(v_b_1088_);
lean_dec(v_a_1087_);
return v_x_1089_;
}
else
{
lean_object* v_key_1090_; lean_object* v_value_1091_; lean_object* v_tail_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1104_; 
v_key_1090_ = lean_ctor_get(v_x_1089_, 0);
v_value_1091_ = lean_ctor_get(v_x_1089_, 1);
v_tail_1092_ = lean_ctor_get(v_x_1089_, 2);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_x_1089_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1094_ = v_x_1089_;
v_isShared_1095_ = v_isSharedCheck_1104_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_tail_1092_);
lean_inc(v_value_1091_);
lean_inc(v_key_1090_);
lean_dec(v_x_1089_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1104_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
uint8_t v___x_1096_; 
v___x_1096_ = lean_nat_dec_eq(v_key_1090_, v_a_1087_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1097_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1087_, v_b_1088_, v_tail_1092_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 2, v___x_1097_);
v___x_1099_ = v___x_1094_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_key_1090_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_value_1091_);
lean_ctor_set(v_reuseFailAlloc_1100_, 2, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
else
{
lean_object* v___x_1102_; 
lean_dec(v_value_1091_);
lean_dec(v_key_1090_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 1, v_b_1088_);
lean_ctor_set(v___x_1094_, 0, v_a_1087_);
v___x_1102_ = v___x_1094_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1087_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_b_1088_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v_tail_1092_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(lean_object* v_m_1105_, lean_object* v_a_1106_, lean_object* v_b_1107_){
_start:
{
lean_object* v_size_1108_; lean_object* v_buckets_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1152_; 
v_size_1108_ = lean_ctor_get(v_m_1105_, 0);
v_buckets_1109_ = lean_ctor_get(v_m_1105_, 1);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_m_1105_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1111_ = v_m_1105_;
v_isShared_1112_ = v_isSharedCheck_1152_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_buckets_1109_);
lean_inc(v_size_1108_);
lean_dec(v_m_1105_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1152_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; uint64_t v___x_1114_; uint64_t v___x_1115_; uint64_t v___x_1116_; uint64_t v_fold_1117_; uint64_t v___x_1118_; uint64_t v___x_1119_; uint64_t v___x_1120_; size_t v___x_1121_; size_t v___x_1122_; size_t v___x_1123_; size_t v___x_1124_; size_t v___x_1125_; lean_object* v_bkt_1126_; uint8_t v___x_1127_; 
v___x_1113_ = lean_array_get_size(v_buckets_1109_);
v___x_1114_ = lean_uint64_of_nat(v_a_1106_);
v___x_1115_ = 32ULL;
v___x_1116_ = lean_uint64_shift_right(v___x_1114_, v___x_1115_);
v_fold_1117_ = lean_uint64_xor(v___x_1114_, v___x_1116_);
v___x_1118_ = 16ULL;
v___x_1119_ = lean_uint64_shift_right(v_fold_1117_, v___x_1118_);
v___x_1120_ = lean_uint64_xor(v_fold_1117_, v___x_1119_);
v___x_1121_ = lean_uint64_to_usize(v___x_1120_);
v___x_1122_ = lean_usize_of_nat(v___x_1113_);
v___x_1123_ = ((size_t)1ULL);
v___x_1124_ = lean_usize_sub(v___x_1122_, v___x_1123_);
v___x_1125_ = lean_usize_land(v___x_1121_, v___x_1124_);
v_bkt_1126_ = lean_array_uget_borrowed(v_buckets_1109_, v___x_1125_);
v___x_1127_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1106_, v_bkt_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v_size_x27_1129_; lean_object* v___x_1130_; lean_object* v_buckets_x27_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1128_ = lean_unsigned_to_nat(1u);
v_size_x27_1129_ = lean_nat_add(v_size_1108_, v___x_1128_);
lean_dec(v_size_1108_);
lean_inc(v_bkt_1126_);
v___x_1130_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1130_, 0, v_a_1106_);
lean_ctor_set(v___x_1130_, 1, v_b_1107_);
lean_ctor_set(v___x_1130_, 2, v_bkt_1126_);
v_buckets_x27_1131_ = lean_array_uset(v_buckets_1109_, v___x_1125_, v___x_1130_);
v___x_1132_ = lean_unsigned_to_nat(4u);
v___x_1133_ = lean_nat_mul(v_size_x27_1129_, v___x_1132_);
v___x_1134_ = lean_unsigned_to_nat(3u);
v___x_1135_ = lean_nat_div(v___x_1133_, v___x_1134_);
lean_dec(v___x_1133_);
v___x_1136_ = lean_array_get_size(v_buckets_x27_1131_);
v___x_1137_ = lean_nat_dec_le(v___x_1135_, v___x_1136_);
lean_dec(v___x_1135_);
if (v___x_1137_ == 0)
{
lean_object* v_val_1138_; lean_object* v___x_1140_; 
v_val_1138_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_1131_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 1, v_val_1138_);
lean_ctor_set(v___x_1111_, 0, v_size_x27_1129_);
v___x_1140_ = v___x_1111_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_size_x27_1129_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_val_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
else
{
lean_object* v___x_1143_; 
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 1, v_buckets_x27_1131_);
lean_ctor_set(v___x_1111_, 0, v_size_x27_1129_);
v___x_1143_ = v___x_1111_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_size_x27_1129_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_buckets_x27_1131_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
else
{
lean_object* v___x_1145_; lean_object* v_buckets_x27_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
lean_inc(v_bkt_1126_);
v___x_1145_ = lean_box(0);
v_buckets_x27_1146_ = lean_array_uset(v_buckets_1109_, v___x_1125_, v___x_1145_);
v___x_1147_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1106_, v_b_1107_, v_bkt_1126_);
v___x_1148_ = lean_array_uset(v_buckets_x27_1146_, v___x_1125_, v___x_1147_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 1, v___x_1148_);
v___x_1150_ = v___x_1111_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_size_1108_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(lean_object* v_snd_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_){
_start:
{
if (lean_obj_tag(v_x_1155_) == 0)
{
return v_x_1154_;
}
else
{
lean_object* v_key_1156_; lean_object* v_value_1157_; lean_object* v_tail_1158_; lean_object* v___y_1160_; lean_object* v___x_1163_; 
v_key_1156_ = lean_ctor_get(v_x_1155_, 0);
lean_inc(v_key_1156_);
v_value_1157_ = lean_ctor_get(v_x_1155_, 1);
lean_inc(v_value_1157_);
v_tail_1158_ = lean_ctor_get(v_x_1155_, 2);
lean_inc(v_tail_1158_);
lean_dec_ref_known(v_x_1155_, 3);
v___x_1163_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_snd_1153_, v_key_1156_);
if (lean_obj_tag(v___x_1163_) == 1)
{
lean_object* v_val_1164_; uint8_t v___x_1165_; 
v_val_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_val_1164_);
lean_dec_ref_known(v___x_1163_, 1);
v___x_1165_ = lean_nat_dec_le(v_value_1157_, v_val_1164_);
if (v___x_1165_ == 0)
{
lean_dec(v_value_1157_);
v___y_1160_ = v_val_1164_;
goto v___jp_1159_;
}
else
{
lean_dec(v_val_1164_);
v___y_1160_ = v_value_1157_;
goto v___jp_1159_;
}
}
else
{
lean_dec(v___x_1163_);
lean_dec(v_value_1157_);
lean_dec(v_key_1156_);
v_x_1155_ = v_tail_1158_;
goto _start;
}
v___jp_1159_:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(v_x_1154_, v_key_1156_, v___y_1160_);
v_x_1154_ = v___x_1161_;
v_x_1155_ = v_tail_1158_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5___boxed(lean_object* v_snd_1167_, lean_object* v_x_1168_, lean_object* v_x_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(v_snd_1167_, v_x_1168_, v_x_1169_);
lean_dec_ref(v_snd_1167_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(lean_object* v_snd_1171_, lean_object* v_as_1172_, size_t v_i_1173_, size_t v_stop_1174_, lean_object* v_b_1175_){
_start:
{
uint8_t v___x_1176_; 
v___x_1176_ = lean_usize_dec_eq(v_i_1173_, v_stop_1174_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1178_; size_t v___x_1179_; size_t v___x_1180_; 
v___x_1177_ = lean_array_uget_borrowed(v_as_1172_, v_i_1173_);
lean_inc(v___x_1177_);
v___x_1178_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(v_snd_1171_, v_b_1175_, v___x_1177_);
v___x_1179_ = ((size_t)1ULL);
v___x_1180_ = lean_usize_add(v_i_1173_, v___x_1179_);
v_i_1173_ = v___x_1180_;
v_b_1175_ = v___x_1178_;
goto _start;
}
else
{
return v_b_1175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6___boxed(lean_object* v_snd_1182_, lean_object* v_as_1183_, lean_object* v_i_1184_, lean_object* v_stop_1185_, lean_object* v_b_1186_){
_start:
{
size_t v_i_boxed_1187_; size_t v_stop_boxed_1188_; lean_object* v_res_1189_; 
v_i_boxed_1187_ = lean_unbox_usize(v_i_1184_);
lean_dec(v_i_1184_);
v_stop_boxed_1188_ = lean_unbox_usize(v_stop_1185_);
lean_dec(v_stop_1185_);
v_res_1189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1182_, v_as_1183_, v_i_boxed_1187_, v_stop_boxed_1188_, v_b_1186_);
lean_dec_ref(v_as_1183_);
lean_dec_ref(v_snd_1182_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(lean_object* v_commonCnt_1190_, lean_object* v_a_1191_, lean_object* v_x_1192_){
_start:
{
if (lean_obj_tag(v_x_1192_) == 0)
{
lean_dec(v_a_1191_);
return v_x_1192_;
}
else
{
lean_object* v_key_1193_; lean_object* v_value_1194_; lean_object* v_tail_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1208_; 
v_key_1193_ = lean_ctor_get(v_x_1192_, 0);
v_value_1194_ = lean_ctor_get(v_x_1192_, 1);
v_tail_1195_ = lean_ctor_get(v_x_1192_, 2);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_x_1192_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1197_ = v_x_1192_;
v_isShared_1198_ = v_isSharedCheck_1208_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_tail_1195_);
lean_inc(v_value_1194_);
lean_inc(v_key_1193_);
lean_dec(v_x_1192_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1208_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
uint8_t v___x_1199_; 
v___x_1199_ = lean_nat_dec_eq(v_key_1193_, v_a_1191_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1200_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1190_, v_a_1191_, v_tail_1195_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 2, v___x_1200_);
v___x_1202_ = v___x_1197_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_key_1193_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_value_1194_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
lean_dec(v_key_1193_);
v___x_1204_ = lean_nat_sub(v_value_1194_, v_commonCnt_1190_);
lean_dec(v_value_1194_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 1, v___x_1204_);
lean_ctor_set(v___x_1197_, 0, v_a_1191_);
v___x_1206_ = v___x_1197_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1191_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1207_, 2, v_tail_1195_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0___boxed(lean_object* v_commonCnt_1209_, lean_object* v_a_1210_, lean_object* v_x_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1209_, v_a_1210_, v_x_1211_);
lean_dec(v_commonCnt_1209_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(lean_object* v_commonCnt_1213_, lean_object* v_m_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v_size_1216_; lean_object* v_buckets_1217_; lean_object* v___x_1218_; uint64_t v___x_1219_; uint64_t v___x_1220_; uint64_t v___x_1221_; uint64_t v_fold_1222_; uint64_t v___x_1223_; uint64_t v___x_1224_; uint64_t v___x_1225_; size_t v___x_1226_; size_t v___x_1227_; size_t v___x_1228_; size_t v___x_1229_; size_t v___x_1230_; lean_object* v_bucket_1231_; uint8_t v___x_1232_; 
v_size_1216_ = lean_ctor_get(v_m_1214_, 0);
v_buckets_1217_ = lean_ctor_get(v_m_1214_, 1);
v___x_1218_ = lean_array_get_size(v_buckets_1217_);
v___x_1219_ = lean_uint64_of_nat(v_a_1215_);
v___x_1220_ = 32ULL;
v___x_1221_ = lean_uint64_shift_right(v___x_1219_, v___x_1220_);
v_fold_1222_ = lean_uint64_xor(v___x_1219_, v___x_1221_);
v___x_1223_ = 16ULL;
v___x_1224_ = lean_uint64_shift_right(v_fold_1222_, v___x_1223_);
v___x_1225_ = lean_uint64_xor(v_fold_1222_, v___x_1224_);
v___x_1226_ = lean_uint64_to_usize(v___x_1225_);
v___x_1227_ = lean_usize_of_nat(v___x_1218_);
v___x_1228_ = ((size_t)1ULL);
v___x_1229_ = lean_usize_sub(v___x_1227_, v___x_1228_);
v___x_1230_ = lean_usize_land(v___x_1226_, v___x_1229_);
v_bucket_1231_ = lean_array_uget_borrowed(v_buckets_1217_, v___x_1230_);
v___x_1232_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1215_, v_bucket_1231_);
if (v___x_1232_ == 0)
{
lean_dec(v_a_1215_);
return v_m_1214_;
}
else
{
lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1243_; 
lean_inc(v_bucket_1231_);
lean_inc_ref(v_buckets_1217_);
lean_inc(v_size_1216_);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_m_1214_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; lean_object* v_unused_1245_; 
v_unused_1244_ = lean_ctor_get(v_m_1214_, 1);
lean_dec(v_unused_1244_);
v_unused_1245_ = lean_ctor_get(v_m_1214_, 0);
lean_dec(v_unused_1245_);
v___x_1234_ = v_m_1214_;
v_isShared_1235_ = v_isSharedCheck_1243_;
goto v_resetjp_1233_;
}
else
{
lean_dec(v_m_1214_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1243_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v_buckets_1237_; lean_object* v_bucket_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1236_ = lean_box(0);
v_buckets_1237_ = lean_array_uset(v_buckets_1217_, v___x_1230_, v___x_1236_);
v_bucket_1238_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1213_, v_a_1215_, v_bucket_1231_);
v___x_1239_ = lean_array_uset(v_buckets_1237_, v___x_1230_, v_bucket_1238_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 1, v___x_1239_);
v___x_1241_ = v___x_1234_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_size_1216_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v___x_1239_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0___boxed(lean_object* v_commonCnt_1246_, lean_object* v_m_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_commonCnt_1246_, v_m_1247_, v_a_1248_);
lean_dec(v_commonCnt_1246_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(lean_object* v_x_1250_, lean_object* v_x_1251_){
_start:
{
if (lean_obj_tag(v_x_1251_) == 0)
{
return v_x_1250_;
}
else
{
lean_object* v_key_1252_; lean_object* v_value_1253_; lean_object* v_tail_1254_; lean_object* v___x_1255_; 
v_key_1252_ = lean_ctor_get(v_x_1251_, 0);
lean_inc(v_key_1252_);
v_value_1253_ = lean_ctor_get(v_x_1251_, 1);
lean_inc(v_value_1253_);
v_tail_1254_ = lean_ctor_get(v_x_1251_, 2);
lean_inc(v_tail_1254_);
lean_dec_ref_known(v_x_1251_, 3);
v___x_1255_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_value_1253_, v_x_1250_, v_key_1252_);
lean_dec(v_value_1253_);
v_x_1250_ = v___x_1255_;
v_x_1251_ = v_tail_1254_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
if (lean_obj_tag(v_x_1258_) == 0)
{
return v_x_1257_;
}
else
{
lean_object* v_key_1259_; lean_object* v_value_1260_; lean_object* v_tail_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v_key_1259_ = lean_ctor_get(v_x_1258_, 0);
lean_inc(v_key_1259_);
v_value_1260_ = lean_ctor_get(v_x_1258_, 1);
lean_inc(v_value_1260_);
v_tail_1261_ = lean_ctor_get(v_x_1258_, 2);
lean_inc(v_tail_1261_);
lean_dec_ref_known(v_x_1258_, 3);
v___x_1262_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_value_1260_, v_x_1257_, v_key_1259_);
lean_dec(v_value_1260_);
v___x_1263_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(v___x_1262_, v_tail_1261_);
return v___x_1263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(lean_object* v_as_1264_, size_t v_i_1265_, size_t v_stop_1266_, lean_object* v_b_1267_){
_start:
{
uint8_t v___x_1268_; 
v___x_1268_ = lean_usize_dec_eq(v_i_1265_, v_stop_1266_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; lean_object* v___x_1270_; size_t v___x_1271_; size_t v___x_1272_; 
v___x_1269_ = lean_array_uget_borrowed(v_as_1264_, v_i_1265_);
lean_inc(v___x_1269_);
v___x_1270_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(v_b_1267_, v___x_1269_);
v___x_1271_ = ((size_t)1ULL);
v___x_1272_ = lean_usize_add(v_i_1265_, v___x_1271_);
v_i_1265_ = v___x_1272_;
v_b_1267_ = v___x_1270_;
goto _start;
}
else
{
return v_b_1267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2___boxed(lean_object* v_as_1274_, lean_object* v_i_1275_, lean_object* v_stop_1276_, lean_object* v_b_1277_){
_start:
{
size_t v_i_boxed_1278_; size_t v_stop_boxed_1279_; lean_object* v_res_1280_; 
v_i_boxed_1278_ = lean_unbox_usize(v_i_1275_);
lean_dec(v_i_1275_);
v_stop_boxed_1279_ = lean_unbox_usize(v_stop_1276_);
lean_dec(v_stop_1276_);
v_res_1280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_as_1274_, v_i_boxed_1278_, v_stop_boxed_1279_, v_b_1277_);
lean_dec_ref(v_as_1274_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(lean_object* v_x_1281_, lean_object* v_y_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v___y_1286_; lean_object* v_fst_1287_; lean_object* v_snd_1288_; lean_object* v_size_1292_; lean_object* v_buckets_1293_; lean_object* v_size_1294_; lean_object* v_buckets_1295_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v_buckets_1304_; lean_object* v___y_1305_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v_buckets_1316_; lean_object* v_fst_1324_; lean_object* v_buckets_1325_; lean_object* v_snd_1326_; uint8_t v___x_1336_; 
v_size_1292_ = lean_ctor_get(v_y_1282_, 0);
lean_inc(v_size_1292_);
v_buckets_1293_ = lean_ctor_get(v_y_1282_, 1);
v_size_1294_ = lean_ctor_get(v_x_1281_, 0);
lean_inc(v_size_1294_);
v_buckets_1295_ = lean_ctor_get(v_x_1281_, 1);
v___x_1336_ = lean_nat_dec_lt(v_size_1292_, v_size_1294_);
if (v___x_1336_ == 0)
{
lean_inc_ref(v_buckets_1295_);
v_fst_1324_ = v_x_1281_;
v_buckets_1325_ = v_buckets_1295_;
v_snd_1326_ = v_y_1282_;
goto v___jp_1323_;
}
else
{
lean_inc_ref(v_buckets_1293_);
v_fst_1324_ = v_y_1282_;
v_buckets_1325_ = v_buckets_1293_;
v_snd_1326_ = v_x_1281_;
goto v___jp_1323_;
}
v___jp_1285_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1289_, 0, v___y_1286_);
lean_ctor_set(v___x_1289_, 1, v_fst_1287_);
lean_ctor_set(v___x_1289_, 2, v_snd_1288_);
v___x_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
lean_ctor_set(v___x_1290_, 1, v_a_1283_);
v___x_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
return v___x_1291_;
}
v___jp_1296_:
{
uint8_t v___x_1300_; 
v___x_1300_ = lean_nat_dec_lt(v_size_1292_, v_size_1294_);
lean_dec(v_size_1294_);
lean_dec(v_size_1292_);
if (v___x_1300_ == 0)
{
v___y_1286_ = v___y_1298_;
v_fst_1287_ = v___y_1297_;
v_snd_1288_ = v___y_1299_;
goto v___jp_1285_;
}
else
{
v___y_1286_ = v___y_1298_;
v_fst_1287_ = v___y_1299_;
v_snd_1288_ = v___y_1297_;
goto v___jp_1285_;
}
}
v___jp_1301_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1306_ = lean_unsigned_to_nat(0u);
v___x_1307_ = lean_array_get_size(v_buckets_1304_);
v___x_1308_ = lean_nat_dec_lt(v___x_1306_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_dec_ref(v_buckets_1304_);
v___y_1297_ = v___y_1305_;
v___y_1298_ = v___y_1303_;
v___y_1299_ = v___y_1302_;
goto v___jp_1296_;
}
else
{
size_t v___x_1309_; size_t v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = ((size_t)0ULL);
v___x_1310_ = lean_usize_of_nat(v___x_1307_);
v___x_1311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1304_, v___x_1309_, v___x_1310_, v___y_1302_);
lean_dec_ref(v_buckets_1304_);
v___y_1297_ = v___y_1305_;
v___y_1298_ = v___y_1303_;
v___y_1299_ = v___x_1311_;
goto v___jp_1296_;
}
}
v___jp_1312_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = lean_array_get_size(v_buckets_1316_);
v___x_1319_ = lean_nat_dec_lt(v___x_1317_, v___x_1318_);
if (v___x_1319_ == 0)
{
v___y_1302_ = v___y_1313_;
v___y_1303_ = v___y_1315_;
v_buckets_1304_ = v_buckets_1316_;
v___y_1305_ = v___y_1314_;
goto v___jp_1301_;
}
else
{
size_t v___x_1320_; size_t v___x_1321_; lean_object* v___x_1322_; 
v___x_1320_ = ((size_t)0ULL);
v___x_1321_ = lean_usize_of_nat(v___x_1318_);
v___x_1322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1316_, v___x_1320_, v___x_1321_, v___y_1314_);
v___y_1302_ = v___y_1313_;
v___y_1303_ = v___y_1315_;
v_buckets_1304_ = v_buckets_1316_;
v___y_1305_ = v___x_1322_;
goto v___jp_1301_;
}
}
v___jp_1323_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1329_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1330_ = lean_array_get_size(v_buckets_1325_);
v___x_1331_ = lean_nat_dec_lt(v___x_1327_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_dec_ref(v_buckets_1325_);
v___y_1313_ = v_snd_1326_;
v___y_1314_ = v_fst_1324_;
v___y_1315_ = v___x_1329_;
v_buckets_1316_ = v___x_1328_;
goto v___jp_1312_;
}
else
{
size_t v___x_1332_; size_t v___x_1333_; lean_object* v___x_1334_; lean_object* v_buckets_1335_; 
v___x_1332_ = ((size_t)0ULL);
v___x_1333_ = lean_usize_of_nat(v___x_1330_);
v___x_1334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1326_, v_buckets_1325_, v___x_1332_, v___x_1333_, v___x_1329_);
lean_dec_ref(v_buckets_1325_);
v_buckets_1335_ = lean_ctor_get(v___x_1334_, 1);
lean_inc_ref(v_buckets_1335_);
v___y_1313_ = v_snd_1326_;
v___y_1314_ = v_fst_1324_;
v___y_1315_ = v___x_1334_;
v_buckets_1316_ = v_buckets_1335_;
goto v___jp_1312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg___boxed(lean_object* v_x_1337_, lean_object* v_y_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1337_, v_y_1338_, v_a_1339_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(lean_object* v_x_1342_, lean_object* v_y_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1342_, v_y_1343_, v_a_1344_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___boxed(lean_object* v_x_1353_, lean_object* v_y_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(v_x_1353_, v_y_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_a_1356_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3(lean_object* v_00_u03b2_1364_, lean_object* v_m_1365_, lean_object* v_a_1366_, lean_object* v_b_1367_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(v_m_1365_, v_a_1366_, v_b_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4(lean_object* v_00_u03b2_1369_, lean_object* v_m_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1370_, v_a_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___boxed(lean_object* v_00_u03b2_1373_, lean_object* v_m_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4(v_00_u03b2_1373_, v_m_1374_, v_a_1375_);
lean_dec(v_a_1375_);
lean_dec_ref(v_m_1374_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5(lean_object* v_00_u03b2_1377_, lean_object* v_a_1378_, lean_object* v_b_1379_, lean_object* v_x_1380_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1378_, v_b_1379_, v_x_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7(lean_object* v_00_u03b2_1382_, lean_object* v_a_1383_, lean_object* v_x_1384_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1383_, v_x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1386_, lean_object* v_a_1387_, lean_object* v_x_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7(v_00_u03b2_1386_, v_a_1387_, v_x_1388_);
lean_dec(v_x_1388_);
lean_dec(v_a_1387_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(lean_object* v_x_1390_, lean_object* v_x_1391_){
_start:
{
if (lean_obj_tag(v_x_1391_) == 0)
{
return v_x_1390_;
}
else
{
lean_object* v_key_1392_; lean_object* v_value_1393_; lean_object* v_tail_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v_key_1392_ = lean_ctor_get(v_x_1391_, 0);
v_value_1393_ = lean_ctor_get(v_x_1391_, 1);
v_tail_1394_ = lean_ctor_get(v_x_1391_, 2);
lean_inc(v_value_1393_);
lean_inc(v_key_1392_);
v___x_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1395_, 0, v_key_1392_);
lean_ctor_set(v___x_1395_, 1, v_value_1393_);
v___x_1396_ = lean_array_push(v_x_1390_, v___x_1395_);
v_x_1390_ = v___x_1396_;
v_x_1391_ = v_tail_1394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___boxed(lean_object* v_x_1398_, lean_object* v_x_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(v_x_1398_, v_x_1399_);
lean_dec(v_x_1399_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(lean_object* v_as_1401_, size_t v_i_1402_, size_t v_stop_1403_, lean_object* v_b_1404_){
_start:
{
uint8_t v___x_1405_; 
v___x_1405_ = lean_usize_dec_eq(v_i_1402_, v_stop_1403_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; lean_object* v___x_1407_; size_t v___x_1408_; size_t v___x_1409_; 
v___x_1406_ = lean_array_uget_borrowed(v_as_1401_, v_i_1402_);
v___x_1407_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(v_b_1404_, v___x_1406_);
v___x_1408_ = ((size_t)1ULL);
v___x_1409_ = lean_usize_add(v_i_1402_, v___x_1408_);
v_i_1402_ = v___x_1409_;
v_b_1404_ = v___x_1407_;
goto _start;
}
else
{
return v_b_1404_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4___boxed(lean_object* v_as_1411_, lean_object* v_i_1412_, lean_object* v_stop_1413_, lean_object* v_b_1414_){
_start:
{
size_t v_i_boxed_1415_; size_t v_stop_boxed_1416_; lean_object* v_res_1417_; 
v_i_boxed_1415_ = lean_unbox_usize(v_i_1412_);
lean_dec(v_i_1412_);
v_stop_boxed_1416_ = lean_unbox_usize(v_stop_1413_);
lean_dec(v_stop_1413_);
v_res_1417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_as_1411_, v_i_boxed_1415_, v_stop_boxed_1416_, v_b_1414_);
lean_dec_ref(v_as_1411_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(lean_object* v_upperBound_1418_, lean_object* v___x_1419_, lean_object* v_op_1420_, lean_object* v_a_1421_, lean_object* v_b_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v___y_1426_; uint8_t v___x_1430_; 
v___x_1430_ = lean_nat_dec_lt(v_a_1421_, v_upperBound_1418_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_dec(v_a_1421_);
lean_dec_ref(v_op_1420_);
lean_dec_ref(v___x_1419_);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v_b_1422_);
lean_ctor_set(v___x_1431_, 1, v___y_1423_);
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
return v___x_1432_;
}
else
{
if (lean_obj_tag(v_b_1422_) == 0)
{
lean_object* v___x_1433_; 
lean_inc_ref(v___x_1419_);
v___x_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1419_);
v___y_1426_ = v___x_1433_;
goto v___jp_1425_;
}
else
{
lean_object* v_val_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1443_; 
v_val_1434_ = lean_ctor_get(v_b_1422_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_b_1422_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1436_ = v_b_1422_;
v_isShared_1437_ = v_isSharedCheck_1443_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_val_1434_);
lean_dec(v_b_1422_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1443_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1441_; 
lean_inc_ref(v_op_1420_);
v___x_1438_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_1420_);
lean_inc_ref(v___x_1419_);
v___x_1439_ = l_Lean_mkAppB(v___x_1438_, v_val_1434_, v___x_1419_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1439_);
v___x_1441_ = v___x_1436_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
v___y_1426_ = v___x_1441_;
goto v___jp_1425_;
}
}
}
}
v___jp_1425_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = lean_unsigned_to_nat(1u);
v___x_1428_ = lean_nat_add(v_a_1421_, v___x_1427_);
lean_dec(v_a_1421_);
v_a_1421_ = v___x_1428_;
v_b_1422_ = v___y_1426_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg___boxed(lean_object* v_upperBound_1444_, lean_object* v___x_1445_, lean_object* v_op_1446_, lean_object* v_a_1447_, lean_object* v_b_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1444_, v___x_1445_, v_op_1446_, v_a_1447_, v_b_1448_, v___y_1449_);
lean_dec(v_upperBound_1444_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(lean_object* v_op_1452_, lean_object* v_as_1453_, size_t v_sz_1454_, size_t v_i_1455_, lean_object* v_b_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
uint8_t v___x_1465_; 
v___x_1465_ = lean_usize_dec_lt(v_i_1455_, v_sz_1454_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec_ref(v_op_1452_);
v___x_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1466_, 0, v_b_1456_);
lean_ctor_set(v___x_1466_, 1, v___y_1457_);
v___x_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
return v___x_1467_;
}
else
{
lean_object* v_a_1468_; lean_object* v_fst_1469_; lean_object* v_snd_1470_; lean_object* v_varToExpr_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v_a_1468_ = lean_array_uget_borrowed(v_as_1453_, v_i_1455_);
v_fst_1469_ = lean_ctor_get(v_a_1468_, 0);
v_snd_1470_ = lean_ctor_get(v_a_1468_, 1);
v_varToExpr_1471_ = lean_ctor_get(v___y_1457_, 2);
v___x_1472_ = l_Lean_instInhabitedExpr;
v___x_1473_ = lean_unsigned_to_nat(0u);
v___x_1474_ = lean_array_get(v___x_1472_, v_varToExpr_1471_, v_fst_1469_);
lean_inc_ref(v_op_1452_);
v___x_1475_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_snd_1470_, v___x_1474_, v_op_1452_, v___x_1473_, v_b_1456_, v___y_1457_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v_fst_1477_; lean_object* v_snd_1478_; size_t v___x_1479_; size_t v___x_1480_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
v_fst_1477_ = lean_ctor_get(v_a_1476_, 0);
lean_inc(v_fst_1477_);
v_snd_1478_ = lean_ctor_get(v_a_1476_, 1);
lean_inc(v_snd_1478_);
lean_dec(v_a_1476_);
v___x_1479_ = ((size_t)1ULL);
v___x_1480_ = lean_usize_add(v_i_1455_, v___x_1479_);
v_i_1455_ = v___x_1480_;
v_b_1456_ = v_fst_1477_;
v___y_1457_ = v_snd_1478_;
goto _start;
}
else
{
lean_dec_ref(v_op_1452_);
return v___x_1475_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1___boxed(lean_object* v_op_1482_, lean_object* v_as_1483_, lean_object* v_sz_1484_, lean_object* v_i_1485_, lean_object* v_b_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
size_t v_sz_boxed_1495_; size_t v_i_boxed_1496_; lean_object* v_res_1497_; 
v_sz_boxed_1495_ = lean_unbox_usize(v_sz_1484_);
lean_dec(v_sz_1484_);
v_i_boxed_1496_ = lean_unbox_usize(v_i_1485_);
lean_dec(v_i_1485_);
v_res_1497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1482_, v_as_1483_, v_sz_boxed_1495_, v_i_boxed_1496_, v_b_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec_ref(v_as_1483_);
return v_res_1497_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(lean_object* v_x1_1498_, lean_object* v_x2_1499_){
_start:
{
lean_object* v_fst_1500_; lean_object* v_fst_1501_; uint8_t v___x_1502_; 
v_fst_1500_ = lean_ctor_get(v_x1_1498_, 0);
v_fst_1501_ = lean_ctor_get(v_x2_1499_, 0);
v___x_1502_ = lean_nat_dec_lt(v_fst_1500_, v_fst_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed(lean_object* v_x1_1503_, lean_object* v_x2_1504_){
_start:
{
uint8_t v_res_1505_; lean_object* v_r_1506_; 
v_res_1505_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v_x1_1503_, v_x2_1504_);
lean_dec_ref(v_x2_1504_);
lean_dec_ref(v_x1_1503_);
v_r_1506_ = lean_box(v_res_1505_);
return v_r_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(lean_object* v_hi_1507_, lean_object* v_pivot_1508_, lean_object* v_as_1509_, lean_object* v_i_1510_, lean_object* v_k_1511_){
_start:
{
uint8_t v___x_1512_; 
v___x_1512_ = lean_nat_dec_lt(v_k_1511_, v_hi_1507_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec(v_k_1511_);
v___x_1513_ = lean_array_fswap(v_as_1509_, v_i_1510_, v_hi_1507_);
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v_i_1510_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
return v___x_1514_;
}
else
{
lean_object* v___x_1515_; lean_object* v_fst_1516_; lean_object* v_fst_1517_; uint8_t v___x_1518_; 
v___x_1515_ = lean_array_fget_borrowed(v_as_1509_, v_k_1511_);
v_fst_1516_ = lean_ctor_get(v___x_1515_, 0);
v_fst_1517_ = lean_ctor_get(v_pivot_1508_, 0);
v___x_1518_ = lean_nat_dec_lt(v_fst_1516_, v_fst_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = lean_unsigned_to_nat(1u);
v___x_1520_ = lean_nat_add(v_k_1511_, v___x_1519_);
lean_dec(v_k_1511_);
v_k_1511_ = v___x_1520_;
goto _start;
}
else
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1522_ = lean_array_fswap(v_as_1509_, v_i_1510_, v_k_1511_);
v___x_1523_ = lean_unsigned_to_nat(1u);
v___x_1524_ = lean_nat_add(v_i_1510_, v___x_1523_);
lean_dec(v_i_1510_);
v___x_1525_ = lean_nat_add(v_k_1511_, v___x_1523_);
lean_dec(v_k_1511_);
v_as_1509_ = v___x_1522_;
v_i_1510_ = v___x_1524_;
v_k_1511_ = v___x_1525_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg___boxed(lean_object* v_hi_1527_, lean_object* v_pivot_1528_, lean_object* v_as_1529_, lean_object* v_i_1530_, lean_object* v_k_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1527_, v_pivot_1528_, v_as_1529_, v_i_1530_, v_k_1531_);
lean_dec_ref(v_pivot_1528_);
lean_dec(v_hi_1527_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(lean_object* v_n_1533_, lean_object* v_as_1534_, lean_object* v_lo_1535_, lean_object* v_hi_1536_){
_start:
{
lean_object* v___y_1538_; uint8_t v___x_1548_; 
v___x_1548_ = lean_nat_dec_lt(v_lo_1535_, v_hi_1536_);
if (v___x_1548_ == 0)
{
lean_dec(v_lo_1535_);
return v_as_1534_;
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v_mid_1551_; lean_object* v___y_1553_; lean_object* v___y_1559_; lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1549_ = lean_nat_add(v_lo_1535_, v_hi_1536_);
v___x_1550_ = lean_unsigned_to_nat(1u);
v_mid_1551_ = lean_nat_shiftr(v___x_1549_, v___x_1550_);
lean_dec(v___x_1549_);
v___x_1564_ = lean_array_fget_borrowed(v_as_1534_, v_mid_1551_);
v___x_1565_ = lean_array_fget_borrowed(v_as_1534_, v_lo_1535_);
v___x_1566_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1564_, v___x_1565_);
if (v___x_1566_ == 0)
{
v___y_1559_ = v_as_1534_;
goto v___jp_1558_;
}
else
{
lean_object* v___x_1567_; 
v___x_1567_ = lean_array_fswap(v_as_1534_, v_lo_1535_, v_mid_1551_);
v___y_1559_ = v___x_1567_;
goto v___jp_1558_;
}
v___jp_1552_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1554_ = lean_array_fget_borrowed(v___y_1553_, v_mid_1551_);
v___x_1555_ = lean_array_fget_borrowed(v___y_1553_, v_hi_1536_);
v___x_1556_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1554_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_dec(v_mid_1551_);
v___y_1538_ = v___y_1553_;
goto v___jp_1537_;
}
else
{
lean_object* v___x_1557_; 
v___x_1557_ = lean_array_fswap(v___y_1553_, v_mid_1551_, v_hi_1536_);
lean_dec(v_mid_1551_);
v___y_1538_ = v___x_1557_;
goto v___jp_1537_;
}
}
v___jp_1558_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; 
v___x_1560_ = lean_array_fget_borrowed(v___y_1559_, v_hi_1536_);
v___x_1561_ = lean_array_fget_borrowed(v___y_1559_, v_lo_1535_);
v___x_1562_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1560_, v___x_1561_);
if (v___x_1562_ == 0)
{
v___y_1553_ = v___y_1559_;
goto v___jp_1552_;
}
else
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_array_fswap(v___y_1559_, v_lo_1535_, v_hi_1536_);
v___y_1553_ = v___x_1563_;
goto v___jp_1552_;
}
}
}
v___jp_1537_:
{
lean_object* v_pivot_1539_; lean_object* v___x_1540_; lean_object* v_fst_1541_; lean_object* v_snd_1542_; uint8_t v___x_1543_; 
v_pivot_1539_ = lean_array_fget(v___y_1538_, v_hi_1536_);
lean_inc_n(v_lo_1535_, 2);
v___x_1540_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1536_, v_pivot_1539_, v___y_1538_, v_lo_1535_, v_lo_1535_);
lean_dec(v_pivot_1539_);
v_fst_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_fst_1541_);
v_snd_1542_ = lean_ctor_get(v___x_1540_, 1);
lean_inc(v_snd_1542_);
lean_dec_ref(v___x_1540_);
v___x_1543_ = lean_nat_dec_le(v_hi_1536_, v_fst_1541_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1544_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1533_, v_snd_1542_, v_lo_1535_, v_fst_1541_);
v___x_1545_ = lean_unsigned_to_nat(1u);
v___x_1546_ = lean_nat_add(v_fst_1541_, v___x_1545_);
lean_dec(v_fst_1541_);
v_as_1534_ = v___x_1544_;
v_lo_1535_ = v___x_1546_;
goto _start;
}
else
{
lean_dec(v_fst_1541_);
lean_dec(v_lo_1535_);
return v_snd_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___boxed(lean_object* v_n_1568_, lean_object* v_as_1569_, lean_object* v_lo_1570_, lean_object* v_hi_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1568_, v_as_1569_, v_lo_1570_, v_hi_1571_);
lean_dec(v_hi_1571_);
lean_dec(v_n_1568_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(lean_object* v_coeff_1573_, lean_object* v_op_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v___y_1584_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1602_; lean_object* v_size_1609_; lean_object* v_buckets_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v_size_1609_ = lean_ctor_get(v_coeff_1573_, 0);
v_buckets_1610_ = lean_ctor_get(v_coeff_1573_, 1);
v___x_1611_ = lean_mk_empty_array_with_capacity(v_size_1609_);
v___x_1612_ = lean_unsigned_to_nat(0u);
v___x_1613_ = lean_array_get_size(v_buckets_1610_);
v___x_1614_ = lean_nat_dec_lt(v___x_1612_, v___x_1613_);
if (v___x_1614_ == 0)
{
v___y_1602_ = v___x_1611_;
goto v___jp_1601_;
}
else
{
size_t v___x_1615_; size_t v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = ((size_t)0ULL);
v___x_1616_ = lean_usize_of_nat(v___x_1613_);
v___x_1617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_buckets_1610_, v___x_1615_, v___x_1616_, v___x_1611_);
v___y_1602_ = v___x_1617_;
goto v___jp_1601_;
}
v___jp_1583_:
{
lean_object* v_acc_1585_; size_t v_sz_1586_; size_t v___x_1587_; lean_object* v___x_1588_; 
v_acc_1585_ = lean_box(0);
v_sz_1586_ = lean_array_size(v___y_1584_);
v___x_1587_ = ((size_t)0ULL);
v___x_1588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1574_, v___y_1584_, v_sz_1586_, v___x_1587_, v_acc_1585_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
lean_dec_ref(v___y_1584_);
return v___x_1588_;
}
v___jp_1589_:
{
lean_object* v___x_1594_; 
v___x_1594_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v___y_1591_, v___y_1590_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec(v___y_1591_);
v___y_1584_ = v___x_1594_;
goto v___jp_1583_;
}
v___jp_1595_:
{
uint8_t v___x_1600_; 
v___x_1600_ = lean_nat_dec_le(v___y_1599_, v___y_1597_);
if (v___x_1600_ == 0)
{
lean_dec(v___y_1597_);
lean_inc(v___y_1599_);
v___y_1590_ = v___y_1596_;
v___y_1591_ = v___y_1598_;
v___y_1592_ = v___y_1599_;
v___y_1593_ = v___y_1599_;
goto v___jp_1589_;
}
else
{
v___y_1590_ = v___y_1596_;
v___y_1591_ = v___y_1598_;
v___y_1592_ = v___y_1599_;
v___y_1593_ = v___y_1597_;
goto v___jp_1589_;
}
}
v___jp_1601_:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
v___x_1603_ = lean_array_get_size(v___y_1602_);
v___x_1604_ = lean_unsigned_to_nat(0u);
v___x_1605_ = lean_nat_dec_eq(v___x_1603_, v___x_1604_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; 
v___x_1606_ = lean_unsigned_to_nat(1u);
v___x_1607_ = lean_nat_sub(v___x_1603_, v___x_1606_);
v___x_1608_ = lean_nat_dec_le(v___x_1604_, v___x_1607_);
if (v___x_1608_ == 0)
{
lean_inc(v___x_1607_);
v___y_1596_ = v___y_1602_;
v___y_1597_ = v___x_1607_;
v___y_1598_ = v___x_1603_;
v___y_1599_ = v___x_1607_;
goto v___jp_1595_;
}
else
{
v___y_1596_ = v___y_1602_;
v___y_1597_ = v___x_1607_;
v___y_1598_ = v___x_1603_;
v___y_1599_ = v___x_1604_;
goto v___jp_1595_;
}
}
else
{
v___y_1584_ = v___y_1602_;
goto v___jp_1583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr___boxed(lean_object* v_coeff_1618_, lean_object* v_op_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_coeff_1618_, v_op_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
lean_dec(v_a_1622_);
lean_dec_ref(v_a_1621_);
lean_dec_ref(v_coeff_1618_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(lean_object* v_upperBound_1629_, lean_object* v___x_1630_, lean_object* v_op_1631_, lean_object* v_inst_1632_, lean_object* v_R_1633_, lean_object* v_a_1634_, lean_object* v_b_1635_, lean_object* v_c_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1629_, v___x_1630_, v_op_1631_, v_a_1634_, v_b_1635_, v___y_1637_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___boxed(lean_object* v_upperBound_1646_, lean_object* v___x_1647_, lean_object* v_op_1648_, lean_object* v_inst_1649_, lean_object* v_R_1650_, lean_object* v_a_1651_, lean_object* v_b_1652_, lean_object* v_c_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(v_upperBound_1646_, v___x_1647_, v_op_1648_, v_inst_1649_, v_R_1650_, v_a_1651_, v_b_1652_, v_c_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v_upperBound_1646_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(lean_object* v_n_1663_, lean_object* v_as_1664_, lean_object* v_lo_1665_, lean_object* v_hi_1666_, lean_object* v_w_1667_, lean_object* v_hlo_1668_, lean_object* v_hhi_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1663_, v_as_1664_, v_lo_1665_, v_hi_1666_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___boxed(lean_object* v_n_1671_, lean_object* v_as_1672_, lean_object* v_lo_1673_, lean_object* v_hi_1674_, lean_object* v_w_1675_, lean_object* v_hlo_1676_, lean_object* v_hhi_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(v_n_1671_, v_as_1672_, v_lo_1673_, v_hi_1674_, v_w_1675_, v_hlo_1676_, v_hhi_1677_);
lean_dec(v_hi_1674_);
lean_dec(v_n_1671_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(lean_object* v_n_1679_, lean_object* v_lo_1680_, lean_object* v_hi_1681_, lean_object* v_hhi_1682_, lean_object* v_pivot_1683_, lean_object* v_as_1684_, lean_object* v_i_1685_, lean_object* v_k_1686_, lean_object* v_ilo_1687_, lean_object* v_ik_1688_, lean_object* v_w_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1681_, v_pivot_1683_, v_as_1684_, v_i_1685_, v_k_1686_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___boxed(lean_object* v_n_1691_, lean_object* v_lo_1692_, lean_object* v_hi_1693_, lean_object* v_hhi_1694_, lean_object* v_pivot_1695_, lean_object* v_as_1696_, lean_object* v_i_1697_, lean_object* v_k_1698_, lean_object* v_ilo_1699_, lean_object* v_ik_1700_, lean_object* v_w_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(v_n_1691_, v_lo_1692_, v_hi_1693_, v_hhi_1694_, v_pivot_1695_, v_as_1696_, v_i_1697_, v_k_1698_, v_ilo_1699_, v_ik_1700_, v_w_1701_);
lean_dec_ref(v_pivot_1695_);
lean_dec(v_hi_1693_);
lean_dec(v_lo_1692_);
lean_dec(v_n_1691_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(lean_object* v_e_1703_, lean_object* v___y_1704_){
_start:
{
uint8_t v___x_1706_; 
v___x_1706_ = l_Lean_Expr_hasMVar(v_e_1703_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; 
v___x_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1707_, 0, v_e_1703_);
return v___x_1707_;
}
else
{
lean_object* v___x_1708_; lean_object* v_mctx_1709_; lean_object* v___x_1710_; lean_object* v_fst_1711_; lean_object* v_snd_1712_; lean_object* v___x_1713_; lean_object* v_cache_1714_; lean_object* v_zetaDeltaFVarIds_1715_; lean_object* v_postponed_1716_; lean_object* v_diag_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1726_; 
v___x_1708_ = lean_st_ref_get(v___y_1704_);
v_mctx_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc_ref(v_mctx_1709_);
lean_dec(v___x_1708_);
v___x_1710_ = l_Lean_instantiateMVarsCore(v_mctx_1709_, v_e_1703_);
v_fst_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_fst_1711_);
v_snd_1712_ = lean_ctor_get(v___x_1710_, 1);
lean_inc(v_snd_1712_);
lean_dec_ref(v___x_1710_);
v___x_1713_ = lean_st_ref_take(v___y_1704_);
v_cache_1714_ = lean_ctor_get(v___x_1713_, 1);
v_zetaDeltaFVarIds_1715_ = lean_ctor_get(v___x_1713_, 2);
v_postponed_1716_ = lean_ctor_get(v___x_1713_, 3);
v_diag_1717_ = lean_ctor_get(v___x_1713_, 4);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1726_ == 0)
{
lean_object* v_unused_1727_; 
v_unused_1727_ = lean_ctor_get(v___x_1713_, 0);
lean_dec(v_unused_1727_);
v___x_1719_ = v___x_1713_;
v_isShared_1720_ = v_isSharedCheck_1726_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_diag_1717_);
lean_inc(v_postponed_1716_);
lean_inc(v_zetaDeltaFVarIds_1715_);
lean_inc(v_cache_1714_);
lean_dec(v___x_1713_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1726_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v_snd_1712_);
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_snd_1712_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_cache_1714_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_zetaDeltaFVarIds_1715_);
lean_ctor_set(v_reuseFailAlloc_1725_, 3, v_postponed_1716_);
lean_ctor_set(v_reuseFailAlloc_1725_, 4, v_diag_1717_);
v___x_1722_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = lean_st_ref_put(v___y_1704_, v___x_1722_);
v___x_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1724_, 0, v_fst_1711_);
return v___x_1724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg___boxed(lean_object* v_e_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1728_, v___y_1729_);
lean_dec(v___y_1729_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(lean_object* v_e_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1732_, v___y_1734_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___boxed(lean_object* v_e_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(v_e_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(lean_object* v_x_1746_, lean_object* v_y_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Lean_Meta_mkEq(v_x_1746_, v_y_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1776_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1756_ = v___x_1753_;
v_isShared_1757_ = v_isSharedCheck_1776_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1776_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set_tag(v___x_1756_, 1);
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
uint8_t v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = 0;
v___x_1761_ = lean_box(0);
v___x_1762_ = l_Lean_Meta_mkFreshExprMVar(v___x_1759_, v___x_1760_, v___x_1761_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
v___x_1764_ = l_Lean_Expr_mvarId_x21(v_a_1763_);
v___x_1765_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v___x_1764_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v___x_1766_; 
lean_dec_ref_known(v___x_1765_, 1);
v___x_1766_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_a_1763_, v_a_1749_);
return v___x_1766_;
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec(v_a_1763_);
v_a_1767_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1765_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1765_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
else
{
return v___x_1762_;
}
}
}
}
else
{
return v___x_1753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC___boxed(lean_object* v_x_1777_, lean_object* v_y_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v_x_1777_, v_y_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
return v_res_1784_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = lean_unsigned_to_nat(32u);
v___x_1786_ = lean_mk_empty_array_with_capacity(v___x_1785_);
v___x_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
return v___x_1787_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1788_ = ((size_t)5ULL);
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = lean_unsigned_to_nat(32u);
v___x_1791_ = lean_mk_empty_array_with_capacity(v___x_1790_);
v___x_1792_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0);
v___x_1793_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
lean_ctor_set(v___x_1793_, 1, v___x_1791_);
lean_ctor_set(v___x_1793_, 2, v___x_1789_);
lean_ctor_set(v___x_1793_, 3, v___x_1789_);
lean_ctor_set_usize(v___x_1793_, 4, v___x_1788_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(lean_object* v___y_1794_){
_start:
{
lean_object* v___x_1796_; lean_object* v_traceState_1797_; lean_object* v_traces_1798_; lean_object* v___x_1799_; lean_object* v_traceState_1800_; lean_object* v_env_1801_; lean_object* v_nextMacroScope_1802_; lean_object* v_ngen_1803_; lean_object* v_auxDeclNGen_1804_; lean_object* v_cache_1805_; lean_object* v_messages_1806_; lean_object* v_infoState_1807_; lean_object* v_snapshotTasks_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1827_; 
v___x_1796_ = lean_st_ref_get(v___y_1794_);
v_traceState_1797_ = lean_ctor_get(v___x_1796_, 4);
lean_inc_ref(v_traceState_1797_);
lean_dec(v___x_1796_);
v_traces_1798_ = lean_ctor_get(v_traceState_1797_, 0);
lean_inc_ref(v_traces_1798_);
lean_dec_ref(v_traceState_1797_);
v___x_1799_ = lean_st_ref_take(v___y_1794_);
v_traceState_1800_ = lean_ctor_get(v___x_1799_, 4);
v_env_1801_ = lean_ctor_get(v___x_1799_, 0);
v_nextMacroScope_1802_ = lean_ctor_get(v___x_1799_, 1);
v_ngen_1803_ = lean_ctor_get(v___x_1799_, 2);
v_auxDeclNGen_1804_ = lean_ctor_get(v___x_1799_, 3);
v_cache_1805_ = lean_ctor_get(v___x_1799_, 5);
v_messages_1806_ = lean_ctor_get(v___x_1799_, 6);
v_infoState_1807_ = lean_ctor_get(v___x_1799_, 7);
v_snapshotTasks_1808_ = lean_ctor_get(v___x_1799_, 8);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1810_ = v___x_1799_;
v_isShared_1811_ = v_isSharedCheck_1827_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_snapshotTasks_1808_);
lean_inc(v_infoState_1807_);
lean_inc(v_messages_1806_);
lean_inc(v_cache_1805_);
lean_inc(v_traceState_1800_);
lean_inc(v_auxDeclNGen_1804_);
lean_inc(v_ngen_1803_);
lean_inc(v_nextMacroScope_1802_);
lean_inc(v_env_1801_);
lean_dec(v___x_1799_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1827_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
uint64_t v_tid_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1825_; 
v_tid_1812_ = lean_ctor_get_uint64(v_traceState_1800_, sizeof(void*)*1);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_traceState_1800_);
if (v_isSharedCheck_1825_ == 0)
{
lean_object* v_unused_1826_; 
v_unused_1826_ = lean_ctor_get(v_traceState_1800_, 0);
lean_dec(v_unused_1826_);
v___x_1814_ = v_traceState_1800_;
v_isShared_1815_ = v_isSharedCheck_1825_;
goto v_resetjp_1813_;
}
else
{
lean_dec(v_traceState_1800_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1825_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1816_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v___x_1816_);
v___x_1818_ = v___x_1814_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1816_);
lean_ctor_set_uint64(v_reuseFailAlloc_1824_, sizeof(void*)*1, v_tid_1812_);
v___x_1818_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1820_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 4, v___x_1818_);
v___x_1820_ = v___x_1810_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_env_1801_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_nextMacroScope_1802_);
lean_ctor_set(v_reuseFailAlloc_1823_, 2, v_ngen_1803_);
lean_ctor_set(v_reuseFailAlloc_1823_, 3, v_auxDeclNGen_1804_);
lean_ctor_set(v_reuseFailAlloc_1823_, 4, v___x_1818_);
lean_ctor_set(v_reuseFailAlloc_1823_, 5, v_cache_1805_);
lean_ctor_set(v_reuseFailAlloc_1823_, 6, v_messages_1806_);
lean_ctor_set(v_reuseFailAlloc_1823_, 7, v_infoState_1807_);
lean_ctor_set(v_reuseFailAlloc_1823_, 8, v_snapshotTasks_1808_);
v___x_1820_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = lean_st_ref_put(v___y_1794_, v___x_1820_);
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v_traces_1798_);
return v___x_1822_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___boxed(lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1828_);
lean_dec(v___y_1828_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1839_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
return v_res_1852_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(lean_object* v_opts_1853_, lean_object* v_opt_1854_){
_start:
{
lean_object* v_name_1855_; lean_object* v_defValue_1856_; lean_object* v_map_1857_; lean_object* v___x_1858_; 
v_name_1855_ = lean_ctor_get(v_opt_1854_, 0);
v_defValue_1856_ = lean_ctor_get(v_opt_1854_, 1);
v_map_1857_ = lean_ctor_get(v_opts_1853_, 0);
v___x_1858_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1857_, v_name_1855_);
if (lean_obj_tag(v___x_1858_) == 0)
{
uint8_t v___x_1859_; 
v___x_1859_ = lean_unbox(v_defValue_1856_);
return v___x_1859_;
}
else
{
lean_object* v_val_1860_; 
v_val_1860_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_val_1860_);
lean_dec_ref_known(v___x_1858_, 1);
if (lean_obj_tag(v_val_1860_) == 1)
{
uint8_t v_v_1861_; 
v_v_1861_ = lean_ctor_get_uint8(v_val_1860_, 0);
lean_dec_ref_known(v_val_1860_, 0);
return v_v_1861_;
}
else
{
uint8_t v___x_1862_; 
lean_dec(v_val_1860_);
v___x_1862_ = lean_unbox(v_defValue_1856_);
return v___x_1862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object* v_opts_1863_, lean_object* v_opt_1864_){
_start:
{
uint8_t v_res_1865_; lean_object* v_r_1866_; 
v_res_1865_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_1863_, v_opt_1864_);
lean_dec_ref(v_opt_1864_);
lean_dec_ref(v_opts_1863_);
v_r_1866_ = lean_box(v_res_1865_);
return v_r_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(lean_object* v_cls_1867_, lean_object* v_____do__lift_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_options_1879_; uint8_t v_hasTrace_1880_; 
v_options_1879_ = lean_ctor_get(v___y_1876_, 2);
v_hasTrace_1880_ = lean_ctor_get_uint8(v_options_1879_, sizeof(void*)*1);
if (v_hasTrace_1880_ == 0)
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
lean_dec(v_cls_1867_);
v___x_1881_ = lean_box(v_hasTrace_1880_);
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
return v___x_1882_;
}
else
{
lean_object* v___x_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1883_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_1884_ = l_Lean_Name_append(v___x_1883_, v_cls_1867_);
v___x_1885_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_1868_, v_options_1879_, v___x_1884_);
lean_dec(v___x_1884_);
v___x_1886_ = lean_box(v___x_1885_);
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
return v___x_1887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0___boxed(lean_object* v_cls_1888_, lean_object* v_____do__lift_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_1888_, v_____do__lift_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v_____do__lift_1889_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1(lean_object* v___x_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lean_mkAppB(v___x_1901_, v___y_1902_, v___y_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(lean_object* v_val_1905_, lean_object* v_lhs_1906_, lean_object* v_rhs_1907_, lean_object* v_P_1908_, uint8_t v___x_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v___x_1918_; 
lean_inc_ref(v_lhs_1906_);
lean_inc_ref(v_val_1905_);
v___x_1918_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1905_, v_lhs_1906_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v_fst_1920_; lean_object* v_snd_1921_; lean_object* v___x_1922_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref_known(v___x_1918_, 1);
v_fst_1920_ = lean_ctor_get(v_a_1919_, 0);
lean_inc(v_fst_1920_);
v_snd_1921_ = lean_ctor_get(v_a_1919_, 1);
lean_inc(v_snd_1921_);
lean_dec(v_a_1919_);
lean_inc_ref(v_rhs_1907_);
lean_inc_ref(v_val_1905_);
v___x_1922_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1905_, v_rhs_1907_, v_snd_1921_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v_fst_1924_; lean_object* v_snd_1925_; lean_object* v___x_1926_; lean_object* v_a_1927_; lean_object* v_fst_1928_; lean_object* v_snd_1929_; lean_object* v_common_1930_; lean_object* v_x_1931_; lean_object* v_y_1932_; lean_object* v___x_1933_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v___x_1922_, 1);
v_fst_1924_ = lean_ctor_get(v_a_1923_, 0);
lean_inc(v_fst_1924_);
v_snd_1925_ = lean_ctor_get(v_a_1923_, 1);
lean_inc(v_snd_1925_);
lean_dec(v_a_1923_);
v___x_1926_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_1920_, v_fst_1924_, v_snd_1925_);
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref(v___x_1926_);
v_fst_1928_ = lean_ctor_get(v_a_1927_, 0);
lean_inc(v_fst_1928_);
v_snd_1929_ = lean_ctor_get(v_a_1927_, 1);
lean_inc(v_snd_1929_);
lean_dec(v_a_1927_);
v_common_1930_ = lean_ctor_get(v_fst_1928_, 0);
lean_inc_ref(v_common_1930_);
v_x_1931_ = lean_ctor_get(v_fst_1928_, 1);
lean_inc_ref(v_x_1931_);
v_y_1932_ = lean_ctor_get(v_fst_1928_, 2);
lean_inc_ref(v_y_1932_);
lean_dec(v_fst_1928_);
lean_inc_ref(v_val_1905_);
v___x_1933_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_1930_, v_val_1905_, v_snd_1929_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec_ref(v_common_1930_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v_fst_1935_; lean_object* v_snd_1936_; lean_object* v___x_1937_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref_known(v___x_1933_, 1);
v_fst_1935_ = lean_ctor_get(v_a_1934_, 0);
lean_inc(v_fst_1935_);
v_snd_1936_ = lean_ctor_get(v_a_1934_, 1);
lean_inc(v_snd_1936_);
lean_dec(v_a_1934_);
lean_inc_ref(v_val_1905_);
v___x_1937_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_1931_, v_val_1905_, v_snd_1936_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec_ref(v_x_1931_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v_fst_1939_; lean_object* v_snd_1940_; lean_object* v___x_1941_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref_known(v___x_1937_, 1);
v_fst_1939_ = lean_ctor_get(v_a_1938_, 0);
lean_inc(v_fst_1939_);
v_snd_1940_ = lean_ctor_get(v_a_1938_, 1);
lean_inc(v_snd_1940_);
lean_dec(v_a_1938_);
lean_inc_ref(v_val_1905_);
v___x_1941_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_1932_, v_val_1905_, v_snd_1940_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec_ref(v_y_1932_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_2006_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1944_ = v___x_1941_;
v_isShared_1945_ = v_isSharedCheck_2006_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1941_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_2006_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v_fst_1946_; lean_object* v_snd_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_2005_; 
v_fst_1946_ = lean_ctor_get(v_a_1942_, 0);
v_snd_1947_ = lean_ctor_get(v_a_1942_, 1);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_a_1942_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1949_ = v_a_1942_;
v_isShared_1950_ = v_isSharedCheck_2005_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_snd_1947_);
lean_inc(v_fst_1946_);
lean_dec(v_a_1942_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_2005_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___x_1995_; lean_object* v___f_1996_; lean_object* v___y_1998_; lean_object* v___x_2002_; 
lean_inc_ref(v_val_1905_);
v___x_1995_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_1905_);
v___f_1996_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_1996_, 0, v___x_1995_);
lean_inc(v_fst_1935_);
lean_inc_ref(v___f_1996_);
v___x_2002_ = l_Option_merge___redArg(v___f_1996_, v_fst_1935_, v_fst_1939_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v___x_2003_; 
lean_inc_ref(v_val_1905_);
v___x_2003_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1905_);
v___y_1998_ = v___x_2003_;
goto v___jp_1997_;
}
else
{
lean_object* v_val_2004_; 
v_val_2004_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_val_2004_);
lean_dec_ref_known(v___x_2002_, 1);
v___y_1998_ = v_val_2004_;
goto v___jp_1997_;
}
v___jp_1951_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
lean_inc_ref(v_P_1908_);
v___x_1954_ = l_Lean_mkAppB(v_P_1908_, v_lhs_1906_, v_rhs_1907_);
v___x_1955_ = l_Lean_mkAppB(v_P_1908_, v___y_1952_, v___y_1953_);
v___x_1956_ = lean_expr_eqv(v___x_1954_, v___x_1955_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; 
lean_del_object(v___x_1944_);
lean_inc_ref(v___x_1955_);
v___x_1957_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_1954_, v___x_1955_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___x_1959_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v___x_1959_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1955_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1971_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1962_ = v___x_1959_;
v_isShared_1963_ = v_isSharedCheck_1971_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1959_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1971_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1964_; lean_object* v___x_1966_; 
v___x_1964_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1964_, 0, v_a_1960_);
lean_ctor_set(v___x_1964_, 1, v_a_1958_);
lean_ctor_set_uint8(v___x_1964_, sizeof(void*)*2, v___x_1956_);
lean_ctor_set_uint8(v___x_1964_, sizeof(void*)*2 + 1, v___x_1956_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_1964_);
v___x_1966_ = v___x_1949_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_snd_1947_);
v___x_1966_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1968_; 
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1966_);
v___x_1968_ = v___x_1962_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1966_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec(v_a_1958_);
lean_del_object(v___x_1949_);
lean_dec(v_snd_1947_);
v_a_1972_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1959_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1959_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1949_);
lean_dec(v_snd_1947_);
v_a_1980_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1957_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1957_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1990_; 
lean_dec_ref(v___x_1955_);
lean_dec_ref(v___x_1954_);
v___x_1988_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1988_, 0, v___x_1909_);
lean_ctor_set_uint8(v___x_1988_, 1, v___x_1909_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_1988_);
v___x_1990_ = v___x_1949_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_snd_1947_);
v___x_1990_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1992_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 0, v___x_1990_);
v___x_1992_ = v___x_1944_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
v___jp_1997_:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Option_merge___redArg(v___f_1996_, v_fst_1935_, v_fst_1946_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v___x_2000_; 
v___x_2000_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1905_);
v___y_1952_ = v___y_1998_;
v___y_1953_ = v___x_2000_;
goto v___jp_1951_;
}
else
{
lean_object* v_val_2001_; 
lean_dec_ref(v_val_1905_);
v_val_2001_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_val_2001_);
lean_dec_ref_known(v___x_1999_, 1);
v___y_1952_ = v___y_1998_;
v___y_1953_ = v_val_2001_;
goto v___jp_1951_;
}
}
}
}
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_dec(v_fst_1939_);
lean_dec(v_fst_1935_);
lean_dec_ref(v_P_1908_);
lean_dec_ref(v_rhs_1907_);
lean_dec_ref(v_lhs_1906_);
lean_dec_ref(v_val_1905_);
v_a_2007_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_1941_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_1941_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec(v_fst_1935_);
lean_dec_ref(v_y_1932_);
lean_dec_ref(v_P_1908_);
lean_dec_ref(v_rhs_1907_);
lean_dec_ref(v_lhs_1906_);
lean_dec_ref(v_val_1905_);
v_a_2015_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_1937_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_1937_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec_ref(v_y_1932_);
lean_dec_ref(v_x_1931_);
lean_dec_ref(v_P_1908_);
lean_dec_ref(v_rhs_1907_);
lean_dec_ref(v_lhs_1906_);
lean_dec_ref(v_val_1905_);
v_a_2023_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_1933_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_1933_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec(v_fst_1920_);
lean_dec_ref(v_P_1908_);
lean_dec_ref(v_rhs_1907_);
lean_dec_ref(v_lhs_1906_);
lean_dec_ref(v_val_1905_);
v_a_2031_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_1922_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_1922_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec_ref(v_P_1908_);
lean_dec_ref(v_rhs_1907_);
lean_dec_ref(v_lhs_1906_);
lean_dec_ref(v_val_1905_);
v_a_2039_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_1918_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_1918_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object* v_val_2047_, lean_object* v_lhs_2048_, lean_object* v_rhs_2049_, lean_object* v_P_2050_, lean_object* v___x_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
uint8_t v___x_187453__boxed_2060_; lean_object* v_res_2061_; 
v___x_187453__boxed_2060_ = lean_unbox(v___x_2051_);
v_res_2061_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(v_val_2047_, v_lhs_2048_, v_rhs_2049_, v_P_2050_, v___x_187453__boxed_2060_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
return v_res_2061_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_2064_ = l_Lean_stringToMessageData(v___x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(lean_object* v_x_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1);
v___x_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object* v_x_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(v_x_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v_x_2078_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object* v_cls_2090_, lean_object* v_msg_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_ref_2097_; lean_object* v___x_2098_; lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2143_; 
v_ref_2097_ = lean_ctor_get(v___y_2094_, 5);
v___x_2098_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2143_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2143_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; lean_object* v_traceState_2104_; lean_object* v_env_2105_; lean_object* v_nextMacroScope_2106_; lean_object* v_ngen_2107_; lean_object* v_auxDeclNGen_2108_; lean_object* v_cache_2109_; lean_object* v_messages_2110_; lean_object* v_infoState_2111_; lean_object* v_snapshotTasks_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2142_; 
v___x_2103_ = lean_st_ref_take(v___y_2095_);
v_traceState_2104_ = lean_ctor_get(v___x_2103_, 4);
v_env_2105_ = lean_ctor_get(v___x_2103_, 0);
v_nextMacroScope_2106_ = lean_ctor_get(v___x_2103_, 1);
v_ngen_2107_ = lean_ctor_get(v___x_2103_, 2);
v_auxDeclNGen_2108_ = lean_ctor_get(v___x_2103_, 3);
v_cache_2109_ = lean_ctor_get(v___x_2103_, 5);
v_messages_2110_ = lean_ctor_get(v___x_2103_, 6);
v_infoState_2111_ = lean_ctor_get(v___x_2103_, 7);
v_snapshotTasks_2112_ = lean_ctor_get(v___x_2103_, 8);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2114_ = v___x_2103_;
v_isShared_2115_ = v_isSharedCheck_2142_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_snapshotTasks_2112_);
lean_inc(v_infoState_2111_);
lean_inc(v_messages_2110_);
lean_inc(v_cache_2109_);
lean_inc(v_traceState_2104_);
lean_inc(v_auxDeclNGen_2108_);
lean_inc(v_ngen_2107_);
lean_inc(v_nextMacroScope_2106_);
lean_inc(v_env_2105_);
lean_dec(v___x_2103_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2142_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
uint64_t v_tid_2116_; lean_object* v_traces_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2141_; 
v_tid_2116_ = lean_ctor_get_uint64(v_traceState_2104_, sizeof(void*)*1);
v_traces_2117_ = lean_ctor_get(v_traceState_2104_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_traceState_2104_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2119_ = v_traceState_2104_;
v_isShared_2120_ = v_isSharedCheck_2141_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_traces_2117_);
lean_dec(v_traceState_2104_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2141_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2121_; double v___x_2122_; uint8_t v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2131_; 
v___x_2121_ = lean_box(0);
v___x_2122_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_2123_ = 0;
v___x_2124_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_2125_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2125_, 0, v_cls_2090_);
lean_ctor_set(v___x_2125_, 1, v___x_2121_);
lean_ctor_set(v___x_2125_, 2, v___x_2124_);
lean_ctor_set_float(v___x_2125_, sizeof(void*)*3, v___x_2122_);
lean_ctor_set_float(v___x_2125_, sizeof(void*)*3 + 8, v___x_2122_);
lean_ctor_set_uint8(v___x_2125_, sizeof(void*)*3 + 16, v___x_2123_);
v___x_2126_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_2127_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2125_);
lean_ctor_set(v___x_2127_, 1, v_a_2099_);
lean_ctor_set(v___x_2127_, 2, v___x_2126_);
lean_inc(v_ref_2097_);
v___x_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2128_, 0, v_ref_2097_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = l_Lean_PersistentArray_push___redArg(v_traces_2117_, v___x_2128_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v___x_2129_);
v___x_2131_ = v___x_2119_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2129_);
lean_ctor_set_uint64(v_reuseFailAlloc_2140_, sizeof(void*)*1, v_tid_2116_);
v___x_2131_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2133_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 4, v___x_2131_);
v___x_2133_ = v___x_2114_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_env_2105_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_nextMacroScope_2106_);
lean_ctor_set(v_reuseFailAlloc_2139_, 2, v_ngen_2107_);
lean_ctor_set(v_reuseFailAlloc_2139_, 3, v_auxDeclNGen_2108_);
lean_ctor_set(v_reuseFailAlloc_2139_, 4, v___x_2131_);
lean_ctor_set(v_reuseFailAlloc_2139_, 5, v_cache_2109_);
lean_ctor_set(v_reuseFailAlloc_2139_, 6, v_messages_2110_);
lean_ctor_set(v_reuseFailAlloc_2139_, 7, v_infoState_2111_);
lean_ctor_set(v_reuseFailAlloc_2139_, 8, v_snapshotTasks_2112_);
v___x_2133_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2137_; 
v___x_2134_ = lean_st_ref_put(v___y_2095_, v___x_2133_);
v___x_2135_ = lean_box(0);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2135_);
v___x_2137_ = v___x_2101_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2135_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object* v_cls_2144_, lean_object* v_msg_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2144_, v_msg_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
return v_res_2151_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2154_ = l_Lean_stringToMessageData(v___x_2153_);
return v___x_2154_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3(void){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2));
v___x_2157_ = l_Lean_stringToMessageData(v___x_2156_);
return v___x_2157_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5(void){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4));
v___x_2160_ = l_Lean_stringToMessageData(v___x_2159_);
return v___x_2160_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2161_ = lean_box(0);
v___x_2162_ = lean_unsigned_to_nat(16u);
v___x_2163_ = lean_mk_array(v___x_2162_, v___x_2161_);
return v___x_2163_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6);
v___x_2165_ = lean_unsigned_to_nat(0u);
v___x_2166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
lean_ctor_set(v___x_2166_, 1, v___x_2164_);
return v___x_2166_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9));
v___x_2171_ = l_Lean_stringToMessageData(v___x_2170_);
return v___x_2171_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11));
v___x_2174_ = l_Lean_stringToMessageData(v___x_2173_);
return v___x_2174_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13));
v___x_2177_ = l_Lean_stringToMessageData(v___x_2176_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(lean_object* v_lhs_2178_, lean_object* v_rhs_2179_, uint8_t v___x_2180_, lean_object* v___f_2181_, lean_object* v_cls_2182_, lean_object* v_P_2183_, lean_object* v_____r_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2204_; 
lean_inc_ref(v_lhs_2178_);
v___x_2204_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2178_);
if (lean_obj_tag(v___x_2204_) == 1)
{
lean_object* v_val_2205_; lean_object* v___x_2206_; 
v_val_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_val_2205_);
lean_dec_ref_known(v___x_2204_, 1);
lean_inc_ref(v_rhs_2179_);
v___x_2206_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2179_);
if (lean_obj_tag(v___x_2206_) == 1)
{
lean_object* v_val_2207_; uint8_t v___x_2246_; 
v_val_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_val_2207_);
lean_dec_ref_known(v___x_2206_, 1);
v___x_2246_ = lean_expr_eqv(v_val_2205_, v_val_2207_);
if (v___x_2246_ == 0)
{
lean_dec_ref(v_P_2183_);
goto v___jp_2208_;
}
else
{
if (v___x_2180_ == 0)
{
lean_object* v_options_2247_; lean_object* v_inheritedTraceOptions_2248_; uint8_t v_hasTrace_2249_; lean_object* v___x_2250_; lean_object* v___f_2251_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; 
lean_dec(v_val_2207_);
lean_dec_ref(v___f_2181_);
v_options_2247_ = lean_ctor_get(v___y_2192_, 2);
v_inheritedTraceOptions_2248_ = lean_ctor_get(v___y_2192_, 13);
v_hasTrace_2249_ = lean_ctor_get_uint8(v_options_2247_, sizeof(void*)*1);
v___x_2250_ = lean_box(v___x_2180_);
lean_inc(v_val_2205_);
v___f_2251_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 13, 5);
lean_closure_set(v___f_2251_, 0, v_val_2205_);
lean_closure_set(v___f_2251_, 1, v_lhs_2178_);
lean_closure_set(v___f_2251_, 2, v_rhs_2179_);
lean_closure_set(v___f_2251_, 3, v_P_2183_);
lean_closure_set(v___f_2251_, 4, v___x_2250_);
if (v_hasTrace_2249_ == 0)
{
lean_dec(v_cls_2182_);
v___y_2253_ = v___y_2188_;
v___y_2254_ = v___y_2189_;
v___y_2255_ = v___y_2190_;
v___y_2256_ = v___y_2191_;
v___y_2257_ = v___y_2192_;
v___y_2258_ = v___y_2193_;
goto v___jp_2252_;
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2264_; uint8_t v___x_2265_; 
v___x_2263_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2182_);
v___x_2264_ = l_Lean_Name_append(v___x_2263_, v_cls_2182_);
v___x_2265_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2248_, v_options_2247_, v___x_2264_);
lean_dec(v___x_2264_);
if (v___x_2265_ == 0)
{
lean_dec(v_cls_2182_);
v___y_2253_ = v___y_2188_;
v___y_2254_ = v___y_2189_;
v___y_2255_ = v___y_2190_;
v___y_2256_ = v___y_2191_;
v___y_2257_ = v___y_2192_;
v___y_2258_ = v___y_2193_;
goto v___jp_2252_;
}
else
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2266_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10);
lean_inc(v_val_2205_);
v___x_2267_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2205_);
v___x_2268_ = l_Lean_MessageData_ofExpr(v___x_2267_);
v___x_2269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2266_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12);
v___x_2271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2269_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
v___x_2272_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2182_, v___x_2271_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_dec_ref_known(v___x_2272_, 1);
v___y_2253_ = v___y_2188_;
v___y_2254_ = v___y_2189_;
v___y_2255_ = v___y_2190_;
v___y_2256_ = v___y_2191_;
v___y_2257_ = v___y_2192_;
v___y_2258_ = v___y_2193_;
goto v___jp_2252_;
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec_ref(v___f_2251_);
lean_dec(v_val_2205_);
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2272_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2272_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
v___jp_2252_:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2259_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7);
v___x_2260_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8));
v___x_2261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2261_, 0, v_val_2205_);
lean_ctor_set(v___x_2261_, 1, v___x_2259_);
lean_ctor_set(v___x_2261_, 2, v___x_2260_);
v___x_2262_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___f_2251_, v___x_2261_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
return v___x_2262_;
}
}
else
{
lean_dec_ref(v_P_2183_);
goto v___jp_2208_;
}
}
v___jp_2208_:
{
lean_object* v_inheritedTraceOptions_2209_; lean_object* v___x_2210_; 
v_inheritedTraceOptions_2209_ = lean_ctor_get(v___y_2192_, 13);
lean_inc(v___y_2193_);
lean_inc_ref(v___y_2192_);
lean_inc(v___y_2191_);
lean_inc_ref(v___y_2190_);
lean_inc(v___y_2189_);
lean_inc_ref(v___y_2188_);
lean_inc(v___y_2187_);
lean_inc_ref(v___y_2186_);
lean_inc(v___y_2185_);
lean_inc_ref(v_inheritedTraceOptions_2209_);
v___x_2210_ = lean_apply_11(v___f_2181_, v_inheritedTraceOptions_2209_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, lean_box(0));
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; uint8_t v___x_2212_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2211_);
lean_dec_ref_known(v___x_2210_, 1);
v___x_2212_ = lean_unbox(v_a_2211_);
lean_dec(v_a_2211_);
if (v___x_2212_ == 0)
{
lean_dec(v_val_2207_);
lean_dec(v_val_2205_);
lean_dec(v_cls_2182_);
lean_dec_ref(v_rhs_2179_);
lean_dec_ref(v_lhs_2178_);
goto v___jp_2195_;
}
else
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2213_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1);
v___x_2214_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2205_);
v___x_2215_ = l_Lean_MessageData_ofExpr(v___x_2214_);
v___x_2216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2213_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3);
v___x_2218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2216_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
v___x_2219_ = l_Lean_indentExpr(v_lhs_2178_);
v___x_2220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2218_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
v___x_2221_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5);
v___x_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2220_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2207_);
v___x_2224_ = l_Lean_MessageData_ofExpr(v___x_2223_);
v___x_2225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2222_);
lean_ctor_set(v___x_2225_, 1, v___x_2224_);
v___x_2226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
lean_ctor_set(v___x_2226_, 1, v___x_2217_);
v___x_2227_ = l_Lean_indentExpr(v_rhs_2179_);
v___x_2228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2226_);
lean_ctor_set(v___x_2228_, 1, v___x_2227_);
v___x_2229_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2182_, v___x_2228_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_dec_ref_known(v___x_2229_, 1);
goto v___jp_2195_;
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec(v_val_2207_);
lean_dec(v_val_2205_);
lean_dec(v_cls_2182_);
lean_dec_ref(v_rhs_2179_);
lean_dec_ref(v_lhs_2178_);
v_a_2238_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2210_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2210_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2281_; lean_object* v___x_2282_; 
lean_dec(v___x_2206_);
lean_dec(v_val_2205_);
lean_dec_ref(v_P_2183_);
lean_dec_ref(v_lhs_2178_);
v_inheritedTraceOptions_2281_ = lean_ctor_get(v___y_2192_, 13);
lean_inc(v___y_2193_);
lean_inc_ref(v___y_2192_);
lean_inc(v___y_2191_);
lean_inc_ref(v___y_2190_);
lean_inc(v___y_2189_);
lean_inc_ref(v___y_2188_);
lean_inc(v___y_2187_);
lean_inc_ref(v___y_2186_);
lean_inc(v___y_2185_);
lean_inc_ref(v_inheritedTraceOptions_2281_);
v___x_2282_ = lean_apply_11(v___f_2181_, v_inheritedTraceOptions_2281_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, lean_box(0));
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; uint8_t v___x_2284_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2282_, 1);
v___x_2284_ = lean_unbox(v_a_2283_);
lean_dec(v_a_2283_);
if (v___x_2284_ == 0)
{
lean_dec(v_cls_2182_);
lean_dec_ref(v_rhs_2179_);
goto v___jp_2198_;
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2285_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_2286_ = l_Lean_indentExpr(v_rhs_2179_);
v___x_2287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2285_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
v___x_2288_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2182_, v___x_2287_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_dec_ref_known(v___x_2288_, 1);
goto v___jp_2198_;
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_dec(v_cls_2182_);
lean_dec_ref(v_rhs_2179_);
v_a_2297_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2282_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2282_);
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
lean_object* v_inheritedTraceOptions_2305_; lean_object* v___x_2306_; 
lean_dec(v___x_2204_);
lean_dec_ref(v_P_2183_);
lean_dec_ref(v_rhs_2179_);
v_inheritedTraceOptions_2305_ = lean_ctor_get(v___y_2192_, 13);
lean_inc(v___y_2193_);
lean_inc_ref(v___y_2192_);
lean_inc(v___y_2191_);
lean_inc_ref(v___y_2190_);
lean_inc(v___y_2189_);
lean_inc_ref(v___y_2188_);
lean_inc(v___y_2187_);
lean_inc_ref(v___y_2186_);
lean_inc(v___y_2185_);
lean_inc_ref(v_inheritedTraceOptions_2305_);
v___x_2306_ = lean_apply_11(v___f_2181_, v_inheritedTraceOptions_2305_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, lean_box(0));
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; uint8_t v___x_2308_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2308_ = lean_unbox(v_a_2307_);
lean_dec(v_a_2307_);
if (v___x_2308_ == 0)
{
lean_dec(v_cls_2182_);
lean_dec_ref(v_lhs_2178_);
goto v___jp_2201_;
}
else
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2309_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_2310_ = l_Lean_indentExpr(v_lhs_2178_);
v___x_2311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2309_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
v___x_2312_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2182_, v___x_2311_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_dec_ref_known(v___x_2312_, 1);
goto v___jp_2201_;
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec(v_cls_2182_);
lean_dec_ref(v_lhs_2178_);
v_a_2321_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2306_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2306_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
v___jp_2195_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2196_, 0, v___x_2180_);
lean_ctor_set_uint8(v___x_2196_, 1, v___x_2180_);
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
return v___x_2197_;
}
v___jp_2198_:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2199_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2199_, 0, v___x_2180_);
lean_ctor_set_uint8(v___x_2199_, 1, v___x_2180_);
v___x_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
return v___x_2200_;
}
v___jp_2201_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2202_, 0, v___x_2180_);
lean_ctor_set_uint8(v___x_2202_, 1, v___x_2180_);
v___x_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
return v___x_2203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___boxed(lean_object** _args){
lean_object* v_lhs_2329_ = _args[0];
lean_object* v_rhs_2330_ = _args[1];
lean_object* v___x_2331_ = _args[2];
lean_object* v___f_2332_ = _args[3];
lean_object* v_cls_2333_ = _args[4];
lean_object* v_P_2334_ = _args[5];
lean_object* v_____r_2335_ = _args[6];
lean_object* v___y_2336_ = _args[7];
lean_object* v___y_2337_ = _args[8];
lean_object* v___y_2338_ = _args[9];
lean_object* v___y_2339_ = _args[10];
lean_object* v___y_2340_ = _args[11];
lean_object* v___y_2341_ = _args[12];
lean_object* v___y_2342_ = _args[13];
lean_object* v___y_2343_ = _args[14];
lean_object* v___y_2344_ = _args[15];
lean_object* v___y_2345_ = _args[16];
_start:
{
uint8_t v___x_187937__boxed_2346_; lean_object* v_res_2347_; 
v___x_187937__boxed_2346_ = lean_unbox(v___x_2331_);
v_res_2347_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2329_, v_rhs_2330_, v___x_187937__boxed_2346_, v___f_2332_, v_cls_2333_, v_P_2334_, v_____r_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(lean_object* v_val_2348_, lean_object* v_lhs_2349_, lean_object* v_rhs_2350_, lean_object* v_P_2351_, uint8_t v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v___x_2361_; 
lean_inc_ref(v_lhs_2349_);
lean_inc_ref(v_val_2348_);
v___x_2361_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_2348_, v_lhs_2349_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v_fst_2363_; lean_object* v_snd_2364_; lean_object* v___x_2365_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v_fst_2363_ = lean_ctor_get(v_a_2362_, 0);
lean_inc(v_fst_2363_);
v_snd_2364_ = lean_ctor_get(v_a_2362_, 1);
lean_inc(v_snd_2364_);
lean_dec(v_a_2362_);
lean_inc_ref(v_rhs_2350_);
lean_inc_ref(v_val_2348_);
v___x_2365_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_2348_, v_rhs_2350_, v_snd_2364_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v_a_2366_; lean_object* v_fst_2367_; lean_object* v_snd_2368_; lean_object* v___x_2369_; lean_object* v_a_2370_; lean_object* v_fst_2371_; lean_object* v_snd_2372_; lean_object* v_common_2373_; lean_object* v_x_2374_; lean_object* v_y_2375_; lean_object* v___x_2376_; 
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc(v_a_2366_);
lean_dec_ref_known(v___x_2365_, 1);
v_fst_2367_ = lean_ctor_get(v_a_2366_, 0);
lean_inc(v_fst_2367_);
v_snd_2368_ = lean_ctor_get(v_a_2366_, 1);
lean_inc(v_snd_2368_);
lean_dec(v_a_2366_);
v___x_2369_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_2363_, v_fst_2367_, v_snd_2368_);
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_a_2370_);
lean_dec_ref(v___x_2369_);
v_fst_2371_ = lean_ctor_get(v_a_2370_, 0);
lean_inc(v_fst_2371_);
v_snd_2372_ = lean_ctor_get(v_a_2370_, 1);
lean_inc(v_snd_2372_);
lean_dec(v_a_2370_);
v_common_2373_ = lean_ctor_get(v_fst_2371_, 0);
lean_inc_ref(v_common_2373_);
v_x_2374_ = lean_ctor_get(v_fst_2371_, 1);
lean_inc_ref(v_x_2374_);
v_y_2375_ = lean_ctor_get(v_fst_2371_, 2);
lean_inc_ref(v_y_2375_);
lean_dec(v_fst_2371_);
lean_inc_ref(v_val_2348_);
v___x_2376_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_2373_, v_val_2348_, v_snd_2372_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
lean_dec_ref(v_common_2373_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v_fst_2378_; lean_object* v_snd_2379_; lean_object* v___x_2380_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
lean_dec_ref_known(v___x_2376_, 1);
v_fst_2378_ = lean_ctor_get(v_a_2377_, 0);
lean_inc(v_fst_2378_);
v_snd_2379_ = lean_ctor_get(v_a_2377_, 1);
lean_inc(v_snd_2379_);
lean_dec(v_a_2377_);
lean_inc_ref(v_val_2348_);
v___x_2380_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_2374_, v_val_2348_, v_snd_2379_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
lean_dec_ref(v_x_2374_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v_fst_2382_; lean_object* v_snd_2383_; lean_object* v___x_2384_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2380_, 1);
v_fst_2382_ = lean_ctor_get(v_a_2381_, 0);
lean_inc(v_fst_2382_);
v_snd_2383_ = lean_ctor_get(v_a_2381_, 1);
lean_inc(v_snd_2383_);
lean_dec(v_a_2381_);
lean_inc_ref(v_val_2348_);
v___x_2384_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_2375_, v_val_2348_, v_snd_2383_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
lean_dec_ref(v_y_2375_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2449_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2387_ = v___x_2384_;
v_isShared_2388_ = v_isSharedCheck_2449_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2384_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2449_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v_fst_2389_; lean_object* v_snd_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2448_; 
v_fst_2389_ = lean_ctor_get(v_a_2385_, 0);
v_snd_2390_ = lean_ctor_get(v_a_2385_, 1);
v_isSharedCheck_2448_ = !lean_is_exclusive(v_a_2385_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2392_ = v_a_2385_;
v_isShared_2393_ = v_isSharedCheck_2448_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_snd_2390_);
lean_inc(v_fst_2389_);
lean_dec(v_a_2385_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2448_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___x_2438_; lean_object* v___f_2439_; lean_object* v___y_2441_; lean_object* v___x_2445_; 
lean_inc_ref(v_val_2348_);
v___x_2438_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2348_);
v___f_2439_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_2439_, 0, v___x_2438_);
lean_inc(v_fst_2378_);
lean_inc_ref(v___f_2439_);
v___x_2445_ = l_Option_merge___redArg(v___f_2439_, v_fst_2378_, v_fst_2382_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v___x_2446_; 
lean_inc_ref(v_val_2348_);
v___x_2446_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_2348_);
v___y_2441_ = v___x_2446_;
goto v___jp_2440_;
}
else
{
lean_object* v_val_2447_; 
v_val_2447_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_val_2447_);
lean_dec_ref_known(v___x_2445_, 1);
v___y_2441_ = v_val_2447_;
goto v___jp_2440_;
}
v___jp_2394_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
lean_inc_ref(v_P_2351_);
v___x_2397_ = l_Lean_mkAppB(v_P_2351_, v_lhs_2349_, v_rhs_2350_);
v___x_2398_ = l_Lean_mkAppB(v_P_2351_, v___y_2395_, v___y_2396_);
v___x_2399_ = lean_expr_eqv(v___x_2397_, v___x_2398_);
if (v___x_2399_ == 0)
{
lean_object* v___x_2400_; 
lean_del_object(v___x_2387_);
lean_inc_ref(v___x_2398_);
v___x_2400_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_2397_, v___x_2398_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2402_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___x_2400_, 1);
v___x_2402_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2398_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2414_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2405_ = v___x_2402_;
v_isShared_2406_ = v_isSharedCheck_2414_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2402_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2414_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2407_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2407_, 0, v_a_2403_);
lean_ctor_set(v___x_2407_, 1, v_a_2401_);
lean_ctor_set_uint8(v___x_2407_, sizeof(void*)*2, v___x_2399_);
lean_ctor_set_uint8(v___x_2407_, sizeof(void*)*2 + 1, v___x_2399_);
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v___x_2407_);
v___x_2409_ = v___x_2392_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v_snd_2390_);
v___x_2409_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2411_; 
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v___x_2409_);
v___x_2411_ = v___x_2405_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_dec(v_a_2401_);
lean_del_object(v___x_2392_);
lean_dec(v_snd_2390_);
v_a_2415_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2402_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2402_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
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
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
lean_dec_ref(v___x_2398_);
lean_del_object(v___x_2392_);
lean_dec(v_snd_2390_);
v_a_2423_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2425_ = v___x_2400_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2400_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
else
{
lean_object* v___x_2431_; lean_object* v___x_2433_; 
lean_dec_ref(v___x_2398_);
lean_dec_ref(v___x_2397_);
v___x_2431_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2431_, 0, v___y_2352_);
lean_ctor_set_uint8(v___x_2431_, 1, v___y_2352_);
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v___x_2431_);
v___x_2433_ = v___x_2392_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_snd_2390_);
v___x_2433_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
lean_object* v___x_2435_; 
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 0, v___x_2433_);
v___x_2435_ = v___x_2387_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2433_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
v___jp_2440_:
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Option_merge___redArg(v___f_2439_, v_fst_2378_, v_fst_2389_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_2348_);
v___y_2395_ = v___y_2441_;
v___y_2396_ = v___x_2443_;
goto v___jp_2394_;
}
else
{
lean_object* v_val_2444_; 
lean_dec_ref(v_val_2348_);
v_val_2444_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_val_2444_);
lean_dec_ref_known(v___x_2442_, 1);
v___y_2395_ = v___y_2441_;
v___y_2396_ = v_val_2444_;
goto v___jp_2394_;
}
}
}
}
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
lean_dec(v_fst_2382_);
lean_dec(v_fst_2378_);
lean_dec_ref(v_P_2351_);
lean_dec_ref(v_rhs_2350_);
lean_dec_ref(v_lhs_2349_);
lean_dec_ref(v_val_2348_);
v_a_2450_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2384_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2384_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
lean_dec(v_fst_2378_);
lean_dec_ref(v_y_2375_);
lean_dec_ref(v_P_2351_);
lean_dec_ref(v_rhs_2350_);
lean_dec_ref(v_lhs_2349_);
lean_dec_ref(v_val_2348_);
v_a_2458_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2380_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2380_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec_ref(v_y_2375_);
lean_dec_ref(v_x_2374_);
lean_dec_ref(v_P_2351_);
lean_dec_ref(v_rhs_2350_);
lean_dec_ref(v_lhs_2349_);
lean_dec_ref(v_val_2348_);
v_a_2466_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2376_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2376_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec(v_fst_2363_);
lean_dec_ref(v_P_2351_);
lean_dec_ref(v_rhs_2350_);
lean_dec_ref(v_lhs_2349_);
lean_dec_ref(v_val_2348_);
v_a_2474_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2365_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2365_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_dec_ref(v_P_2351_);
lean_dec_ref(v_rhs_2350_);
lean_dec_ref(v_lhs_2349_);
lean_dec_ref(v_val_2348_);
v_a_2482_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2361_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2361_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed(lean_object* v_val_2490_, lean_object* v_lhs_2491_, lean_object* v_rhs_2492_, lean_object* v_P_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
uint8_t v___y_188266__boxed_2503_; lean_object* v_res_2504_; 
v___y_188266__boxed_2503_ = lean_unbox(v___y_2494_);
v_res_2504_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(v_val_2490_, v_lhs_2491_, v_rhs_2492_, v_P_2493_, v___y_188266__boxed_2503_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(lean_object* v_lhs_2505_, lean_object* v_rhs_2506_, lean_object* v_P_2507_, lean_object* v_cls_2508_, uint8_t v___x_2509_, lean_object* v___f_2510_, uint8_t v___x_2511_, lean_object* v_____r_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v___x_2529_; 
lean_inc_ref(v_lhs_2505_);
v___x_2529_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2505_);
if (lean_obj_tag(v___x_2529_) == 1)
{
lean_object* v_val_2530_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; uint8_t v___y_2544_; lean_object* v___x_2568_; 
v_val_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_val_2530_);
lean_dec_ref_known(v___x_2529_, 1);
lean_inc_ref(v_rhs_2506_);
v___x_2568_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2506_);
if (lean_obj_tag(v___x_2568_) == 1)
{
lean_object* v_val_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2616_; 
v_val_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2616_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_val_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2616_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
uint8_t v___x_2573_; 
v___x_2573_ = lean_expr_eqv(v_val_2530_, v_val_2569_);
if (v___x_2573_ == 0)
{
if (v___x_2509_ == 0)
{
lean_del_object(v___x_2571_);
lean_dec(v_val_2569_);
lean_dec_ref(v___f_2510_);
v___y_2544_ = v___x_2509_;
goto v___jp_2543_;
}
else
{
lean_object* v_inheritedTraceOptions_2579_; lean_object* v___x_2580_; 
lean_dec_ref(v_P_2507_);
v_inheritedTraceOptions_2579_ = lean_ctor_get(v___y_2520_, 13);
lean_inc(v___y_2521_);
lean_inc_ref(v___y_2520_);
lean_inc(v___y_2519_);
lean_inc_ref(v___y_2518_);
lean_inc(v___y_2517_);
lean_inc_ref(v___y_2516_);
lean_inc(v___y_2515_);
lean_inc_ref(v___y_2514_);
lean_inc(v___y_2513_);
lean_inc_ref(v_inheritedTraceOptions_2579_);
v___x_2580_ = lean_apply_11(v___f_2510_, v_inheritedTraceOptions_2579_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, lean_box(0));
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; uint8_t v___x_2582_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2581_);
lean_dec_ref_known(v___x_2580_, 1);
v___x_2582_ = lean_unbox(v_a_2581_);
lean_dec(v_a_2581_);
if (v___x_2582_ == 0)
{
lean_dec(v_val_2569_);
lean_dec(v_val_2530_);
lean_dec(v_cls_2508_);
lean_dec_ref(v_rhs_2506_);
lean_dec_ref(v_lhs_2505_);
goto v___jp_2574_;
}
else
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2583_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1);
v___x_2584_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2530_);
v___x_2585_ = l_Lean_MessageData_ofExpr(v___x_2584_);
v___x_2586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2583_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
v___x_2587_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3);
v___x_2588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2586_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
v___x_2589_ = l_Lean_indentExpr(v_lhs_2505_);
v___x_2590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2588_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
v___x_2591_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5);
v___x_2592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2590_);
lean_ctor_set(v___x_2592_, 1, v___x_2591_);
v___x_2593_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2569_);
v___x_2594_ = l_Lean_MessageData_ofExpr(v___x_2593_);
v___x_2595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2592_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
v___x_2596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
lean_ctor_set(v___x_2596_, 1, v___x_2587_);
v___x_2597_ = l_Lean_indentExpr(v_rhs_2506_);
v___x_2598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2596_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
v___x_2599_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2508_, v___x_2598_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_dec_ref_known(v___x_2599_, 1);
goto v___jp_2574_;
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_del_object(v___x_2571_);
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2599_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2599_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
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
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_del_object(v___x_2571_);
lean_dec(v_val_2569_);
lean_dec(v_val_2530_);
lean_dec(v_cls_2508_);
lean_dec_ref(v_rhs_2506_);
lean_dec_ref(v_lhs_2505_);
v_a_2608_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2580_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2580_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
else
{
lean_del_object(v___x_2571_);
lean_dec(v_val_2569_);
lean_dec_ref(v___f_2510_);
v___y_2544_ = v___x_2511_;
goto v___jp_2543_;
}
v___jp_2574_:
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2575_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2575_, 0, v___x_2573_);
lean_ctor_set_uint8(v___x_2575_, 1, v___x_2573_);
if (v_isShared_2572_ == 0)
{
lean_ctor_set_tag(v___x_2571_, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2575_);
v___x_2577_ = v___x_2571_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2617_; lean_object* v___x_2618_; 
lean_dec(v___x_2568_);
lean_dec(v_val_2530_);
lean_dec_ref(v_P_2507_);
lean_dec_ref(v_lhs_2505_);
v_inheritedTraceOptions_2617_ = lean_ctor_get(v___y_2520_, 13);
lean_inc(v___y_2521_);
lean_inc_ref(v___y_2520_);
lean_inc(v___y_2519_);
lean_inc_ref(v___y_2518_);
lean_inc(v___y_2517_);
lean_inc_ref(v___y_2516_);
lean_inc(v___y_2515_);
lean_inc_ref(v___y_2514_);
lean_inc(v___y_2513_);
lean_inc_ref(v_inheritedTraceOptions_2617_);
v___x_2618_ = lean_apply_11(v___f_2510_, v_inheritedTraceOptions_2617_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, lean_box(0));
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; uint8_t v___x_2620_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2618_, 1);
v___x_2620_ = lean_unbox(v_a_2619_);
lean_dec(v_a_2619_);
if (v___x_2620_ == 0)
{
lean_dec(v_cls_2508_);
lean_dec_ref(v_rhs_2506_);
goto v___jp_2523_;
}
else
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2621_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_2622_ = l_Lean_indentExpr(v_rhs_2506_);
v___x_2623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2621_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
v___x_2624_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2508_, v___x_2623_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_dec_ref_known(v___x_2624_, 1);
goto v___jp_2523_;
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2624_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2624_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec(v_cls_2508_);
lean_dec_ref(v_rhs_2506_);
v_a_2633_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2618_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2618_);
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
v___jp_2531_:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2539_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7);
v___x_2540_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8));
v___x_2541_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2541_, 0, v_val_2530_);
lean_ctor_set(v___x_2541_, 1, v___x_2539_);
lean_ctor_set(v___x_2541_, 2, v___x_2540_);
v___x_2542_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___y_2532_, v___x_2541_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
return v___x_2542_;
}
v___jp_2543_:
{
lean_object* v_options_2545_; lean_object* v_inheritedTraceOptions_2546_; uint8_t v_hasTrace_2547_; lean_object* v___x_2548_; lean_object* v___f_2549_; 
v_options_2545_ = lean_ctor_get(v___y_2520_, 2);
v_inheritedTraceOptions_2546_ = lean_ctor_get(v___y_2520_, 13);
v_hasTrace_2547_ = lean_ctor_get_uint8(v_options_2545_, sizeof(void*)*1);
v___x_2548_ = lean_box(v___y_2544_);
lean_inc(v_val_2530_);
v___f_2549_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed), 13, 5);
lean_closure_set(v___f_2549_, 0, v_val_2530_);
lean_closure_set(v___f_2549_, 1, v_lhs_2505_);
lean_closure_set(v___f_2549_, 2, v_rhs_2506_);
lean_closure_set(v___f_2549_, 3, v_P_2507_);
lean_closure_set(v___f_2549_, 4, v___x_2548_);
if (v_hasTrace_2547_ == 0)
{
lean_dec(v_cls_2508_);
v___y_2532_ = v___f_2549_;
v___y_2533_ = v___y_2516_;
v___y_2534_ = v___y_2517_;
v___y_2535_ = v___y_2518_;
v___y_2536_ = v___y_2519_;
v___y_2537_ = v___y_2520_;
v___y_2538_ = v___y_2521_;
goto v___jp_2531_;
}
else
{
lean_object* v___x_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; 
v___x_2550_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2508_);
v___x_2551_ = l_Lean_Name_append(v___x_2550_, v_cls_2508_);
v___x_2552_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2546_, v_options_2545_, v___x_2551_);
lean_dec(v___x_2551_);
if (v___x_2552_ == 0)
{
lean_dec(v_cls_2508_);
v___y_2532_ = v___f_2549_;
v___y_2533_ = v___y_2516_;
v___y_2534_ = v___y_2517_;
v___y_2535_ = v___y_2518_;
v___y_2536_ = v___y_2519_;
v___y_2537_ = v___y_2520_;
v___y_2538_ = v___y_2521_;
goto v___jp_2531_;
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2553_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10);
lean_inc(v_val_2530_);
v___x_2554_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2530_);
v___x_2555_ = l_Lean_MessageData_ofExpr(v___x_2554_);
v___x_2556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2553_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12);
v___x_2558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2556_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2508_, v___x_2558_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_dec_ref_known(v___x_2559_, 1);
v___y_2532_ = v___f_2549_;
v___y_2533_ = v___y_2516_;
v___y_2534_ = v___y_2517_;
v___y_2535_ = v___y_2518_;
v___y_2536_ = v___y_2519_;
v___y_2537_ = v___y_2520_;
v___y_2538_ = v___y_2521_;
goto v___jp_2531_;
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
lean_dec_ref(v___f_2549_);
lean_dec(v_val_2530_);
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2641_; lean_object* v___x_2642_; 
lean_dec(v___x_2529_);
lean_dec_ref(v_P_2507_);
lean_dec_ref(v_rhs_2506_);
v_inheritedTraceOptions_2641_ = lean_ctor_get(v___y_2520_, 13);
lean_inc(v___y_2521_);
lean_inc_ref(v___y_2520_);
lean_inc(v___y_2519_);
lean_inc_ref(v___y_2518_);
lean_inc(v___y_2517_);
lean_inc_ref(v___y_2516_);
lean_inc(v___y_2515_);
lean_inc_ref(v___y_2514_);
lean_inc(v___y_2513_);
lean_inc_ref(v_inheritedTraceOptions_2641_);
v___x_2642_ = lean_apply_11(v___f_2510_, v_inheritedTraceOptions_2641_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, lean_box(0));
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; uint8_t v___x_2644_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___x_2642_, 1);
v___x_2644_ = lean_unbox(v_a_2643_);
lean_dec(v_a_2643_);
if (v___x_2644_ == 0)
{
lean_dec(v_cls_2508_);
lean_dec_ref(v_lhs_2505_);
goto v___jp_2526_;
}
else
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2645_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_2646_ = l_Lean_indentExpr(v_lhs_2505_);
v___x_2647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2645_);
lean_ctor_set(v___x_2647_, 1, v___x_2646_);
v___x_2648_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2508_, v___x_2647_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_dec_ref_known(v___x_2648_, 1);
goto v___jp_2526_;
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2648_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2648_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
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
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
lean_dec(v_cls_2508_);
lean_dec_ref(v_lhs_2505_);
v_a_2657_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2642_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2642_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
v___jp_2523_:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2524_, 0, v___x_2511_);
lean_ctor_set_uint8(v___x_2524_, 1, v___x_2511_);
v___x_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2524_);
return v___x_2525_;
}
v___jp_2526_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2527_, 0, v___x_2511_);
lean_ctor_set_uint8(v___x_2527_, 1, v___x_2511_);
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
return v___x_2528_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___boxed(lean_object** _args){
lean_object* v_lhs_2665_ = _args[0];
lean_object* v_rhs_2666_ = _args[1];
lean_object* v_P_2667_ = _args[2];
lean_object* v_cls_2668_ = _args[3];
lean_object* v___x_2669_ = _args[4];
lean_object* v___f_2670_ = _args[5];
lean_object* v___x_2671_ = _args[6];
lean_object* v_____r_2672_ = _args[7];
lean_object* v___y_2673_ = _args[8];
lean_object* v___y_2674_ = _args[9];
lean_object* v___y_2675_ = _args[10];
lean_object* v___y_2676_ = _args[11];
lean_object* v___y_2677_ = _args[12];
lean_object* v___y_2678_ = _args[13];
lean_object* v___y_2679_ = _args[14];
lean_object* v___y_2680_ = _args[15];
lean_object* v___y_2681_ = _args[16];
lean_object* v___y_2682_ = _args[17];
_start:
{
uint8_t v___x_188588__boxed_2683_; uint8_t v___x_188590__boxed_2684_; lean_object* v_res_2685_; 
v___x_188588__boxed_2683_ = lean_unbox(v___x_2669_);
v___x_188590__boxed_2684_ = lean_unbox(v___x_2671_);
v_res_2685_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2665_, v_rhs_2666_, v_P_2667_, v_cls_2668_, v___x_188588__boxed_2683_, v___f_2670_, v___x_188590__boxed_2684_, v_____r_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
return v_res_2685_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(lean_object* v_e_2686_){
_start:
{
if (lean_obj_tag(v_e_2686_) == 0)
{
uint8_t v___x_2687_; 
v___x_2687_ = 2;
return v___x_2687_;
}
else
{
uint8_t v___x_2688_; 
v___x_2688_ = 0;
return v___x_2688_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5___boxed(lean_object* v_e_2689_){
_start:
{
uint8_t v_res_2690_; lean_object* v_r_2691_; 
v_res_2690_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_e_2689_);
lean_dec_ref(v_e_2689_);
v_r_2691_ = lean_box(v_res_2690_);
return v_r_2691_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(lean_object* v_x_2692_){
_start:
{
if (lean_obj_tag(v_x_2692_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
v_a_2694_ = lean_ctor_get(v_x_2692_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_x_2692_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v_x_2692_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v_x_2692_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
lean_ctor_set_tag(v___x_2696_, 1);
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
v_a_2702_ = lean_ctor_get(v_x_2692_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_x_2692_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v_x_2692_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v_x_2692_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
lean_ctor_set_tag(v___x_2704_, 0);
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg___boxed(lean_object* v_x_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_2710_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(lean_object* v_opts_2713_, lean_object* v_opt_2714_){
_start:
{
lean_object* v_name_2715_; lean_object* v_defValue_2716_; lean_object* v_map_2717_; lean_object* v___x_2718_; 
v_name_2715_ = lean_ctor_get(v_opt_2714_, 0);
v_defValue_2716_ = lean_ctor_get(v_opt_2714_, 1);
v_map_2717_ = lean_ctor_get(v_opts_2713_, 0);
v___x_2718_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2717_, v_name_2715_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_inc(v_defValue_2716_);
return v_defValue_2716_;
}
else
{
lean_object* v_val_2719_; 
v_val_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_val_2719_);
lean_dec_ref_known(v___x_2718_, 1);
if (lean_obj_tag(v_val_2719_) == 3)
{
lean_object* v_v_2720_; 
v_v_2720_ = lean_ctor_get(v_val_2719_, 0);
lean_inc(v_v_2720_);
lean_dec_ref_known(v_val_2719_, 1);
return v_v_2720_;
}
else
{
lean_dec(v_val_2719_);
lean_inc(v_defValue_2716_);
return v_defValue_2716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6___boxed(lean_object* v_opts_2721_, lean_object* v_opt_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2721_, v_opt_2722_);
lean_dec_ref(v_opt_2722_);
lean_dec_ref(v_opts_2721_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(size_t v_sz_2724_, size_t v_i_2725_, lean_object* v_bs_2726_){
_start:
{
uint8_t v___x_2727_; 
v___x_2727_ = lean_usize_dec_lt(v_i_2725_, v_sz_2724_);
if (v___x_2727_ == 0)
{
return v_bs_2726_;
}
else
{
lean_object* v_v_2728_; lean_object* v_msg_2729_; lean_object* v___x_2730_; lean_object* v_bs_x27_2731_; size_t v___x_2732_; size_t v___x_2733_; lean_object* v___x_2734_; 
v_v_2728_ = lean_array_uget_borrowed(v_bs_2726_, v_i_2725_);
v_msg_2729_ = lean_ctor_get(v_v_2728_, 1);
lean_inc_ref(v_msg_2729_);
v___x_2730_ = lean_unsigned_to_nat(0u);
v_bs_x27_2731_ = lean_array_uset(v_bs_2726_, v_i_2725_, v___x_2730_);
v___x_2732_ = ((size_t)1ULL);
v___x_2733_ = lean_usize_add(v_i_2725_, v___x_2732_);
v___x_2734_ = lean_array_uset(v_bs_x27_2731_, v_i_2725_, v_msg_2729_);
v_i_2725_ = v___x_2733_;
v_bs_2726_ = v___x_2734_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2736_, lean_object* v_i_2737_, lean_object* v_bs_2738_){
_start:
{
size_t v_sz_boxed_2739_; size_t v_i_boxed_2740_; lean_object* v_res_2741_; 
v_sz_boxed_2739_ = lean_unbox_usize(v_sz_2736_);
lean_dec(v_sz_2736_);
v_i_boxed_2740_ = lean_unbox_usize(v_i_2737_);
lean_dec(v_i_2737_);
v_res_2741_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_boxed_2739_, v_i_boxed_2740_, v_bs_2738_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(lean_object* v_oldTraces_2742_, lean_object* v_data_2743_, lean_object* v_ref_2744_, lean_object* v_msg_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v_fileName_2751_; lean_object* v_fileMap_2752_; lean_object* v_options_2753_; lean_object* v_currRecDepth_2754_; lean_object* v_maxRecDepth_2755_; lean_object* v_ref_2756_; lean_object* v_currNamespace_2757_; lean_object* v_openDecls_2758_; lean_object* v_initHeartbeats_2759_; lean_object* v_maxHeartbeats_2760_; lean_object* v_quotContext_2761_; lean_object* v_currMacroScope_2762_; uint8_t v_diag_2763_; lean_object* v_cancelTk_x3f_2764_; uint8_t v_suppressElabErrors_2765_; lean_object* v_inheritedTraceOptions_2766_; lean_object* v___x_2767_; lean_object* v_traceState_2768_; lean_object* v_traces_2769_; lean_object* v_ref_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; size_t v_sz_2773_; size_t v___x_2774_; lean_object* v___x_2775_; lean_object* v_msg_2776_; lean_object* v___x_2777_; lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2815_; 
v_fileName_2751_ = lean_ctor_get(v___y_2748_, 0);
v_fileMap_2752_ = lean_ctor_get(v___y_2748_, 1);
v_options_2753_ = lean_ctor_get(v___y_2748_, 2);
v_currRecDepth_2754_ = lean_ctor_get(v___y_2748_, 3);
v_maxRecDepth_2755_ = lean_ctor_get(v___y_2748_, 4);
v_ref_2756_ = lean_ctor_get(v___y_2748_, 5);
v_currNamespace_2757_ = lean_ctor_get(v___y_2748_, 6);
v_openDecls_2758_ = lean_ctor_get(v___y_2748_, 7);
v_initHeartbeats_2759_ = lean_ctor_get(v___y_2748_, 8);
v_maxHeartbeats_2760_ = lean_ctor_get(v___y_2748_, 9);
v_quotContext_2761_ = lean_ctor_get(v___y_2748_, 10);
v_currMacroScope_2762_ = lean_ctor_get(v___y_2748_, 11);
v_diag_2763_ = lean_ctor_get_uint8(v___y_2748_, sizeof(void*)*14);
v_cancelTk_x3f_2764_ = lean_ctor_get(v___y_2748_, 12);
v_suppressElabErrors_2765_ = lean_ctor_get_uint8(v___y_2748_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2766_ = lean_ctor_get(v___y_2748_, 13);
v___x_2767_ = lean_st_ref_get(v___y_2749_);
v_traceState_2768_ = lean_ctor_get(v___x_2767_, 4);
lean_inc_ref(v_traceState_2768_);
lean_dec(v___x_2767_);
v_traces_2769_ = lean_ctor_get(v_traceState_2768_, 0);
lean_inc_ref(v_traces_2769_);
lean_dec_ref(v_traceState_2768_);
v_ref_2770_ = l_Lean_replaceRef(v_ref_2744_, v_ref_2756_);
lean_inc_ref(v_inheritedTraceOptions_2766_);
lean_inc(v_cancelTk_x3f_2764_);
lean_inc(v_currMacroScope_2762_);
lean_inc(v_quotContext_2761_);
lean_inc(v_maxHeartbeats_2760_);
lean_inc(v_initHeartbeats_2759_);
lean_inc(v_openDecls_2758_);
lean_inc(v_currNamespace_2757_);
lean_inc(v_maxRecDepth_2755_);
lean_inc(v_currRecDepth_2754_);
lean_inc_ref(v_options_2753_);
lean_inc_ref(v_fileMap_2752_);
lean_inc_ref(v_fileName_2751_);
v___x_2771_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2771_, 0, v_fileName_2751_);
lean_ctor_set(v___x_2771_, 1, v_fileMap_2752_);
lean_ctor_set(v___x_2771_, 2, v_options_2753_);
lean_ctor_set(v___x_2771_, 3, v_currRecDepth_2754_);
lean_ctor_set(v___x_2771_, 4, v_maxRecDepth_2755_);
lean_ctor_set(v___x_2771_, 5, v_ref_2770_);
lean_ctor_set(v___x_2771_, 6, v_currNamespace_2757_);
lean_ctor_set(v___x_2771_, 7, v_openDecls_2758_);
lean_ctor_set(v___x_2771_, 8, v_initHeartbeats_2759_);
lean_ctor_set(v___x_2771_, 9, v_maxHeartbeats_2760_);
lean_ctor_set(v___x_2771_, 10, v_quotContext_2761_);
lean_ctor_set(v___x_2771_, 11, v_currMacroScope_2762_);
lean_ctor_set(v___x_2771_, 12, v_cancelTk_x3f_2764_);
lean_ctor_set(v___x_2771_, 13, v_inheritedTraceOptions_2766_);
lean_ctor_set_uint8(v___x_2771_, sizeof(void*)*14, v_diag_2763_);
lean_ctor_set_uint8(v___x_2771_, sizeof(void*)*14 + 1, v_suppressElabErrors_2765_);
v___x_2772_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2769_);
lean_dec_ref(v_traces_2769_);
v_sz_2773_ = lean_array_size(v___x_2772_);
v___x_2774_ = ((size_t)0ULL);
v___x_2775_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_2773_, v___x_2774_, v___x_2772_);
v_msg_2776_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2776_, 0, v_data_2743_);
lean_ctor_set(v_msg_2776_, 1, v_msg_2745_);
lean_ctor_set(v_msg_2776_, 2, v___x_2775_);
v___x_2777_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2776_, v___y_2746_, v___y_2747_, v___x_2771_, v___y_2749_);
lean_dec_ref_known(v___x_2771_, 14);
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2780_ = v___x_2777_;
v_isShared_2781_ = v_isSharedCheck_2815_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2777_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2815_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2782_; lean_object* v_traceState_2783_; lean_object* v_env_2784_; lean_object* v_nextMacroScope_2785_; lean_object* v_ngen_2786_; lean_object* v_auxDeclNGen_2787_; lean_object* v_cache_2788_; lean_object* v_messages_2789_; lean_object* v_infoState_2790_; lean_object* v_snapshotTasks_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2814_; 
v___x_2782_ = lean_st_ref_take(v___y_2749_);
v_traceState_2783_ = lean_ctor_get(v___x_2782_, 4);
v_env_2784_ = lean_ctor_get(v___x_2782_, 0);
v_nextMacroScope_2785_ = lean_ctor_get(v___x_2782_, 1);
v_ngen_2786_ = lean_ctor_get(v___x_2782_, 2);
v_auxDeclNGen_2787_ = lean_ctor_get(v___x_2782_, 3);
v_cache_2788_ = lean_ctor_get(v___x_2782_, 5);
v_messages_2789_ = lean_ctor_get(v___x_2782_, 6);
v_infoState_2790_ = lean_ctor_get(v___x_2782_, 7);
v_snapshotTasks_2791_ = lean_ctor_get(v___x_2782_, 8);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2793_ = v___x_2782_;
v_isShared_2794_ = v_isSharedCheck_2814_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_snapshotTasks_2791_);
lean_inc(v_infoState_2790_);
lean_inc(v_messages_2789_);
lean_inc(v_cache_2788_);
lean_inc(v_traceState_2783_);
lean_inc(v_auxDeclNGen_2787_);
lean_inc(v_ngen_2786_);
lean_inc(v_nextMacroScope_2785_);
lean_inc(v_env_2784_);
lean_dec(v___x_2782_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2814_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
uint64_t v_tid_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2812_; 
v_tid_2795_ = lean_ctor_get_uint64(v_traceState_2783_, sizeof(void*)*1);
v_isSharedCheck_2812_ = !lean_is_exclusive(v_traceState_2783_);
if (v_isSharedCheck_2812_ == 0)
{
lean_object* v_unused_2813_; 
v_unused_2813_ = lean_ctor_get(v_traceState_2783_, 0);
lean_dec(v_unused_2813_);
v___x_2797_ = v_traceState_2783_;
v_isShared_2798_ = v_isSharedCheck_2812_;
goto v_resetjp_2796_;
}
else
{
lean_dec(v_traceState_2783_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2812_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2802_; 
v___x_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2799_, 0, v_ref_2744_);
lean_ctor_set(v___x_2799_, 1, v_a_2778_);
v___x_2800_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2742_, v___x_2799_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 0, v___x_2800_);
v___x_2802_ = v___x_2797_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2800_);
lean_ctor_set_uint64(v_reuseFailAlloc_2811_, sizeof(void*)*1, v_tid_2795_);
v___x_2802_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2804_; 
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 4, v___x_2802_);
v___x_2804_ = v___x_2793_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_env_2784_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v_nextMacroScope_2785_);
lean_ctor_set(v_reuseFailAlloc_2810_, 2, v_ngen_2786_);
lean_ctor_set(v_reuseFailAlloc_2810_, 3, v_auxDeclNGen_2787_);
lean_ctor_set(v_reuseFailAlloc_2810_, 4, v___x_2802_);
lean_ctor_set(v_reuseFailAlloc_2810_, 5, v_cache_2788_);
lean_ctor_set(v_reuseFailAlloc_2810_, 6, v_messages_2789_);
lean_ctor_set(v_reuseFailAlloc_2810_, 7, v_infoState_2790_);
lean_ctor_set(v_reuseFailAlloc_2810_, 8, v_snapshotTasks_2791_);
v___x_2804_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2808_; 
v___x_2805_ = lean_st_ref_put(v___y_2749_, v___x_2804_);
v___x_2806_ = lean_box(0);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v___x_2806_);
v___x_2808_ = v___x_2780_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2806_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_2816_, lean_object* v_data_2817_, lean_object* v_ref_2818_, lean_object* v_msg_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_2816_, v_data_2817_, v_ref_2818_, v_msg_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
return v_res_2825_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__0));
v___x_2828_ = l_Lean_stringToMessageData(v___x_2827_);
return v___x_2828_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2829_; double v___x_2830_; 
v___x_2829_ = lean_unsigned_to_nat(1000u);
v___x_2830_ = lean_float_of_nat(v___x_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(lean_object* v_cls_2831_, uint8_t v_collapsed_2832_, lean_object* v_tag_2833_, lean_object* v_opts_2834_, uint8_t v_clsEnabled_2835_, lean_object* v_oldTraces_2836_, lean_object* v_msg_2837_, lean_object* v_resStartStop_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v_fst_2849_; lean_object* v_snd_2850_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v_data_2854_; lean_object* v_fst_2865_; lean_object* v_snd_2866_; lean_object* v___x_2867_; uint8_t v___x_2868_; lean_object* v___y_2870_; lean_object* v_a_2871_; uint8_t v___y_2886_; double v___y_2917_; 
v_fst_2849_ = lean_ctor_get(v_resStartStop_2838_, 0);
lean_inc(v_fst_2849_);
v_snd_2850_ = lean_ctor_get(v_resStartStop_2838_, 1);
lean_inc(v_snd_2850_);
lean_dec_ref(v_resStartStop_2838_);
v_fst_2865_ = lean_ctor_get(v_snd_2850_, 0);
lean_inc(v_fst_2865_);
v_snd_2866_ = lean_ctor_get(v_snd_2850_, 1);
lean_inc(v_snd_2866_);
lean_dec(v_snd_2850_);
v___x_2867_ = l_Lean_trace_profiler;
v___x_2868_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_2834_, v___x_2867_);
if (v___x_2868_ == 0)
{
v___y_2886_ = v___x_2868_;
goto v___jp_2885_;
}
else
{
lean_object* v___x_2922_; uint8_t v___x_2923_; 
v___x_2922_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2923_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_2834_, v___x_2922_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; lean_object* v___x_2925_; double v___x_2926_; double v___x_2927_; double v___x_2928_; 
v___x_2924_ = l_Lean_trace_profiler_threshold;
v___x_2925_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2834_, v___x_2924_);
v___x_2926_ = lean_float_of_nat(v___x_2925_);
v___x_2927_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2);
v___x_2928_ = lean_float_div(v___x_2926_, v___x_2927_);
v___y_2917_ = v___x_2928_;
goto v___jp_2916_;
}
else
{
lean_object* v___x_2929_; lean_object* v___x_2930_; double v___x_2931_; 
v___x_2929_ = l_Lean_trace_profiler_threshold;
v___x_2930_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2834_, v___x_2929_);
v___x_2931_ = lean_float_of_nat(v___x_2930_);
v___y_2917_ = v___x_2931_;
goto v___jp_2916_;
}
}
v___jp_2851_:
{
lean_object* v___x_2855_; 
lean_inc(v___y_2853_);
v___x_2855_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_2836_, v_data_2854_, v___y_2853_, v___y_2852_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v___x_2856_; 
lean_dec_ref_known(v___x_2855_, 1);
v___x_2856_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_fst_2849_);
return v___x_2856_;
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec(v_fst_2849_);
v_a_2857_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2855_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2855_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
v___jp_2869_:
{
uint8_t v_result_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; double v___x_2875_; lean_object* v_data_2876_; 
v_result_2872_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_fst_2849_);
v___x_2873_ = lean_box(v_result_2872_);
v___x_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2873_);
v___x_2875_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2833_);
lean_inc_ref(v___x_2874_);
lean_inc(v_cls_2831_);
v_data_2876_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2876_, 0, v_cls_2831_);
lean_ctor_set(v_data_2876_, 1, v___x_2874_);
lean_ctor_set(v_data_2876_, 2, v_tag_2833_);
lean_ctor_set_float(v_data_2876_, sizeof(void*)*3, v___x_2875_);
lean_ctor_set_float(v_data_2876_, sizeof(void*)*3 + 8, v___x_2875_);
lean_ctor_set_uint8(v_data_2876_, sizeof(void*)*3 + 16, v_collapsed_2832_);
if (v___x_2868_ == 0)
{
lean_dec_ref_known(v___x_2874_, 1);
lean_dec(v_snd_2866_);
lean_dec(v_fst_2865_);
lean_dec_ref(v_tag_2833_);
lean_dec(v_cls_2831_);
v___y_2852_ = v_a_2871_;
v___y_2853_ = v___y_2870_;
v_data_2854_ = v_data_2876_;
goto v___jp_2851_;
}
else
{
lean_object* v_data_2877_; double v___x_2878_; double v___x_2879_; 
lean_dec_ref_known(v_data_2876_, 3);
v_data_2877_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2877_, 0, v_cls_2831_);
lean_ctor_set(v_data_2877_, 1, v___x_2874_);
lean_ctor_set(v_data_2877_, 2, v_tag_2833_);
v___x_2878_ = lean_unbox_float(v_fst_2865_);
lean_dec(v_fst_2865_);
lean_ctor_set_float(v_data_2877_, sizeof(void*)*3, v___x_2878_);
v___x_2879_ = lean_unbox_float(v_snd_2866_);
lean_dec(v_snd_2866_);
lean_ctor_set_float(v_data_2877_, sizeof(void*)*3 + 8, v___x_2879_);
lean_ctor_set_uint8(v_data_2877_, sizeof(void*)*3 + 16, v_collapsed_2832_);
v___y_2852_ = v_a_2871_;
v___y_2853_ = v___y_2870_;
v_data_2854_ = v_data_2877_;
goto v___jp_2851_;
}
}
v___jp_2880_:
{
lean_object* v_ref_2881_; lean_object* v___x_2882_; 
v_ref_2881_ = lean_ctor_get(v___y_2846_, 5);
lean_inc(v___y_2847_);
lean_inc_ref(v___y_2846_);
lean_inc(v___y_2845_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc_ref(v___y_2842_);
lean_inc(v___y_2841_);
lean_inc_ref(v___y_2840_);
lean_inc(v___y_2839_);
lean_inc(v_fst_2849_);
v___x_2882_ = lean_apply_11(v_msg_2837_, v_fst_2849_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, lean_box(0));
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref_known(v___x_2882_, 1);
v___y_2870_ = v_ref_2881_;
v_a_2871_ = v_a_2883_;
goto v___jp_2869_;
}
else
{
lean_object* v___x_2884_; 
lean_dec_ref_known(v___x_2882_, 1);
v___x_2884_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1);
v___y_2870_ = v_ref_2881_;
v_a_2871_ = v___x_2884_;
goto v___jp_2869_;
}
}
v___jp_2885_:
{
if (v_clsEnabled_2835_ == 0)
{
if (v___y_2886_ == 0)
{
lean_object* v___x_2887_; lean_object* v_traceState_2888_; lean_object* v_env_2889_; lean_object* v_nextMacroScope_2890_; lean_object* v_ngen_2891_; lean_object* v_auxDeclNGen_2892_; lean_object* v_cache_2893_; lean_object* v_messages_2894_; lean_object* v_infoState_2895_; lean_object* v_snapshotTasks_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2915_; 
lean_dec(v_snd_2866_);
lean_dec(v_fst_2865_);
lean_dec_ref(v_msg_2837_);
lean_dec_ref(v_tag_2833_);
lean_dec(v_cls_2831_);
v___x_2887_ = lean_st_ref_take(v___y_2847_);
v_traceState_2888_ = lean_ctor_get(v___x_2887_, 4);
v_env_2889_ = lean_ctor_get(v___x_2887_, 0);
v_nextMacroScope_2890_ = lean_ctor_get(v___x_2887_, 1);
v_ngen_2891_ = lean_ctor_get(v___x_2887_, 2);
v_auxDeclNGen_2892_ = lean_ctor_get(v___x_2887_, 3);
v_cache_2893_ = lean_ctor_get(v___x_2887_, 5);
v_messages_2894_ = lean_ctor_get(v___x_2887_, 6);
v_infoState_2895_ = lean_ctor_get(v___x_2887_, 7);
v_snapshotTasks_2896_ = lean_ctor_get(v___x_2887_, 8);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2898_ = v___x_2887_;
v_isShared_2899_ = v_isSharedCheck_2915_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_snapshotTasks_2896_);
lean_inc(v_infoState_2895_);
lean_inc(v_messages_2894_);
lean_inc(v_cache_2893_);
lean_inc(v_traceState_2888_);
lean_inc(v_auxDeclNGen_2892_);
lean_inc(v_ngen_2891_);
lean_inc(v_nextMacroScope_2890_);
lean_inc(v_env_2889_);
lean_dec(v___x_2887_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2915_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
uint64_t v_tid_2900_; lean_object* v_traces_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2914_; 
v_tid_2900_ = lean_ctor_get_uint64(v_traceState_2888_, sizeof(void*)*1);
v_traces_2901_ = lean_ctor_get(v_traceState_2888_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v_traceState_2888_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2903_ = v_traceState_2888_;
v_isShared_2904_ = v_isSharedCheck_2914_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_traces_2901_);
lean_dec(v_traceState_2888_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2914_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2905_; lean_object* v___x_2907_; 
v___x_2905_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2836_, v_traces_2901_);
lean_dec_ref(v_traces_2901_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v___x_2905_);
v___x_2907_ = v___x_2903_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2905_);
lean_ctor_set_uint64(v_reuseFailAlloc_2913_, sizeof(void*)*1, v_tid_2900_);
v___x_2907_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
lean_object* v___x_2909_; 
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 4, v___x_2907_);
v___x_2909_ = v___x_2898_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_env_2889_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_nextMacroScope_2890_);
lean_ctor_set(v_reuseFailAlloc_2912_, 2, v_ngen_2891_);
lean_ctor_set(v_reuseFailAlloc_2912_, 3, v_auxDeclNGen_2892_);
lean_ctor_set(v_reuseFailAlloc_2912_, 4, v___x_2907_);
lean_ctor_set(v_reuseFailAlloc_2912_, 5, v_cache_2893_);
lean_ctor_set(v_reuseFailAlloc_2912_, 6, v_messages_2894_);
lean_ctor_set(v_reuseFailAlloc_2912_, 7, v_infoState_2895_);
lean_ctor_set(v_reuseFailAlloc_2912_, 8, v_snapshotTasks_2896_);
v___x_2909_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2910_ = lean_st_ref_put(v___y_2847_, v___x_2909_);
v___x_2911_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_fst_2849_);
return v___x_2911_;
}
}
}
}
}
else
{
goto v___jp_2880_;
}
}
else
{
goto v___jp_2880_;
}
}
v___jp_2916_:
{
double v___x_2918_; double v___x_2919_; double v___x_2920_; uint8_t v___x_2921_; 
v___x_2918_ = lean_unbox_float(v_snd_2866_);
v___x_2919_ = lean_unbox_float(v_fst_2865_);
v___x_2920_ = lean_float_sub(v___x_2918_, v___x_2919_);
v___x_2921_ = lean_float_decLt(v___y_2917_, v___x_2920_);
v___y_2886_ = v___x_2921_;
goto v___jp_2885_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___boxed(lean_object** _args){
lean_object* v_cls_2932_ = _args[0];
lean_object* v_collapsed_2933_ = _args[1];
lean_object* v_tag_2934_ = _args[2];
lean_object* v_opts_2935_ = _args[3];
lean_object* v_clsEnabled_2936_ = _args[4];
lean_object* v_oldTraces_2937_ = _args[5];
lean_object* v_msg_2938_ = _args[6];
lean_object* v_resStartStop_2939_ = _args[7];
lean_object* v___y_2940_ = _args[8];
lean_object* v___y_2941_ = _args[9];
lean_object* v___y_2942_ = _args[10];
lean_object* v___y_2943_ = _args[11];
lean_object* v___y_2944_ = _args[12];
lean_object* v___y_2945_ = _args[13];
lean_object* v___y_2946_ = _args[14];
lean_object* v___y_2947_ = _args[15];
lean_object* v___y_2948_ = _args[16];
lean_object* v___y_2949_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2950_; uint8_t v_clsEnabled_boxed_2951_; lean_object* v_res_2952_; 
v_collapsed_boxed_2950_ = lean_unbox(v_collapsed_2933_);
v_clsEnabled_boxed_2951_ = lean_unbox(v_clsEnabled_2936_);
v_res_2952_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_2932_, v_collapsed_boxed_2950_, v_tag_2934_, v_opts_2935_, v_clsEnabled_boxed_2951_, v_oldTraces_2937_, v_msg_2938_, v_resStartStop_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec_ref(v_opts_2935_);
return v_res_2952_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3(void){
_start:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2958_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2));
v___x_2959_ = l_Lean_stringToMessageData(v___x_2958_);
return v___x_2959_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5(void){
_start:
{
lean_object* v___x_2961_; double v___x_2962_; 
v___x_2961_ = lean_unsigned_to_nat(1000000000u);
v___x_2962_ = lean_float_of_nat(v___x_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(lean_object* v_P_2963_, lean_object* v_lhs_2964_, lean_object* v_rhs_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_){
_start:
{
uint8_t v___y_2977_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v_options_2999_; lean_object* v_inheritedTraceOptions_3000_; uint8_t v_hasTrace_3001_; lean_object* v_cls_3002_; lean_object* v___f_3003_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; uint8_t v_____do__lift_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; 
v_options_2999_ = lean_ctor_get(v_a_2973_, 2);
v_inheritedTraceOptions_3000_ = lean_ctor_get(v_a_2973_, 13);
v_hasTrace_3001_ = lean_ctor_get_uint8(v_options_2999_, sizeof(void*)*1);
v_cls_3002_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___f_3003_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1));
if (v_hasTrace_3001_ == 0)
{
lean_object* v___x_3127_; lean_object* v_a_3128_; uint8_t v___x_3129_; 
v___x_3127_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3002_, v_inheritedTraceOptions_3000_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3128_);
lean_dec_ref(v___x_3127_);
v___x_3129_ = lean_unbox(v_a_3128_);
lean_dec(v_a_3128_);
v_____do__lift_3104_ = v___x_3129_;
v___y_3105_ = v_a_2966_;
v___y_3106_ = v_a_2967_;
v___y_3107_ = v_a_2968_;
v___y_3108_ = v_a_2969_;
v___y_3109_ = v_a_2970_;
v___y_3110_ = v_a_2971_;
v___y_3111_ = v_a_2972_;
v___y_3112_ = v_a_2973_;
v___y_3113_ = v_a_2974_;
goto v___jp_3103_;
}
else
{
lean_object* v___f_3130_; uint8_t v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; uint8_t v___x_3134_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v_a_3138_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v_a_3150_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v_a_3168_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v_a_3183_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; 
v___f_3130_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4));
v___x_3131_ = 0;
v___x_3132_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_3133_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3134_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3000_, v_options_2999_, v___x_3133_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3231_; uint8_t v___x_3232_; 
v___x_3231_ = l_Lean_trace_profiler;
v___x_3232_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_2999_, v___x_3231_);
if (v___x_3232_ == 0)
{
lean_object* v___x_3233_; lean_object* v_a_3234_; uint8_t v___x_3235_; 
v___x_3233_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3002_, v_inheritedTraceOptions_3000_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
lean_inc(v_a_3234_);
lean_dec_ref(v___x_3233_);
v___x_3235_ = lean_unbox(v_a_3234_);
lean_dec(v_a_3234_);
v_____do__lift_3104_ = v___x_3235_;
v___y_3105_ = v_a_2966_;
v___y_3106_ = v_a_2967_;
v___y_3107_ = v_a_2968_;
v___y_3108_ = v_a_2969_;
v___y_3109_ = v_a_2970_;
v___y_3110_ = v_a_2971_;
v___y_3111_ = v_a_2972_;
v___y_3112_ = v_a_2973_;
v___y_3113_ = v_a_2974_;
goto v___jp_3103_;
}
else
{
goto v___jp_3198_;
}
}
else
{
goto v___jp_3198_;
}
v___jp_3135_:
{
lean_object* v___x_3139_; double v___x_3140_; double v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3139_ = lean_io_get_num_heartbeats();
v___x_3140_ = lean_float_of_nat(v___y_3136_);
v___x_3141_ = lean_float_of_nat(v___x_3139_);
v___x_3142_ = lean_box_float(v___x_3140_);
v___x_3143_ = lean_box_float(v___x_3141_);
v___x_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3142_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
v___x_3145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3145_, 0, v_a_3138_);
lean_ctor_set(v___x_3145_, 1, v___x_3144_);
v___x_3146_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_3002_, v___x_3131_, v___x_3132_, v_options_2999_, v___x_3134_, v___y_3137_, v___f_3130_, v___x_3145_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_3146_;
}
v___jp_3147_:
{
lean_object* v___x_3151_; 
v___x_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3151_, 0, v_a_3150_);
v___y_3136_ = v___y_3148_;
v___y_3137_ = v___y_3149_;
v_a_3138_ = v___x_3151_;
goto v___jp_3135_;
}
v___jp_3152_:
{
if (lean_obj_tag(v___y_3155_) == 0)
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
v_a_3156_ = lean_ctor_get(v___y_3155_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___y_3155_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___y_3155_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___y_3155_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
lean_ctor_set_tag(v___x_3158_, 1);
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
v___y_3136_ = v___y_3153_;
v___y_3137_ = v___y_3154_;
v_a_3138_ = v___x_3161_;
goto v___jp_3135_;
}
}
}
else
{
lean_object* v_a_3164_; 
v_a_3164_ = lean_ctor_get(v___y_3155_, 0);
lean_inc(v_a_3164_);
lean_dec_ref_known(v___y_3155_, 1);
v___y_3148_ = v___y_3153_;
v___y_3149_ = v___y_3154_;
v_a_3150_ = v_a_3164_;
goto v___jp_3147_;
}
}
v___jp_3165_:
{
lean_object* v___x_3169_; double v___x_3170_; double v___x_3171_; double v___x_3172_; double v___x_3173_; double v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3169_ = lean_io_mono_nanos_now();
v___x_3170_ = lean_float_of_nat(v___y_3167_);
v___x_3171_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5);
v___x_3172_ = lean_float_div(v___x_3170_, v___x_3171_);
v___x_3173_ = lean_float_of_nat(v___x_3169_);
v___x_3174_ = lean_float_div(v___x_3173_, v___x_3171_);
v___x_3175_ = lean_box_float(v___x_3172_);
v___x_3176_ = lean_box_float(v___x_3174_);
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3175_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3178_, 0, v_a_3168_);
lean_ctor_set(v___x_3178_, 1, v___x_3177_);
v___x_3179_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_3002_, v___x_3131_, v___x_3132_, v_options_2999_, v___x_3134_, v___y_3166_, v___f_3130_, v___x_3178_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_3179_;
}
v___jp_3180_:
{
lean_object* v___x_3184_; 
v___x_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3184_, 0, v_a_3183_);
v___y_3166_ = v___y_3181_;
v___y_3167_ = v___y_3182_;
v_a_3168_ = v___x_3184_;
goto v___jp_3165_;
}
v___jp_3185_:
{
if (lean_obj_tag(v___y_3188_) == 0)
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
v_a_3189_ = lean_ctor_get(v___y_3188_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___y_3188_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___y_3188_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___y_3188_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
lean_ctor_set_tag(v___x_3191_, 1);
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
v___y_3166_ = v___y_3186_;
v___y_3167_ = v___y_3187_;
v_a_3168_ = v___x_3194_;
goto v___jp_3165_;
}
}
}
else
{
lean_object* v_a_3197_; 
v_a_3197_ = lean_ctor_get(v___y_3188_, 0);
lean_inc(v_a_3197_);
lean_dec_ref_known(v___y_3188_, 1);
v___y_3181_ = v___y_3186_;
v___y_3182_ = v___y_3187_;
v_a_3183_ = v_a_3197_;
goto v___jp_3180_;
}
}
v___jp_3198_:
{
lean_object* v___x_3199_; lean_object* v_a_3200_; lean_object* v___x_3201_; uint8_t v___x_3202_; 
v___x_3199_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v_a_2974_);
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3200_);
lean_dec_ref(v___x_3199_);
v___x_3201_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3202_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_2999_, v___x_3201_);
if (v___x_3202_ == 0)
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v_a_3205_; uint8_t v___x_3206_; 
v___x_3203_ = lean_io_mono_nanos_now();
v___x_3204_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3002_, v_inheritedTraceOptions_3000_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref(v___x_3204_);
v___x_3206_ = lean_unbox(v_a_3205_);
lean_dec(v_a_3205_);
if (v___x_3206_ == 0)
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3207_ = lean_box(0);
v___x_3208_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2964_, v_rhs_2965_, v___x_3202_, v___f_3003_, v_cls_3002_, v_P_2963_, v___x_3207_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3186_ = v_a_3200_;
v___y_3187_ = v___x_3203_;
v___y_3188_ = v___x_3208_;
goto v___jp_3185_;
}
else
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3209_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_2965_);
lean_inc_ref(v_lhs_2964_);
lean_inc_ref(v_P_2963_);
v___x_3210_ = l_Lean_mkAppB(v_P_2963_, v_lhs_2964_, v_rhs_2965_);
v___x_3211_ = l_Lean_indentExpr(v___x_3210_);
v___x_3212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3209_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
v___x_3213_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3002_, v___x_3212_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; lean_object* v___x_3215_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_a_3214_);
lean_dec_ref_known(v___x_3213_, 1);
v___x_3215_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2964_, v_rhs_2965_, v___x_3202_, v___f_3003_, v_cls_3002_, v_P_2963_, v_a_3214_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3186_ = v_a_3200_;
v___y_3187_ = v___x_3203_;
v___y_3188_ = v___x_3215_;
goto v___jp_3185_;
}
else
{
lean_object* v_a_3216_; 
lean_dec_ref(v_rhs_2965_);
lean_dec_ref(v_lhs_2964_);
lean_dec_ref(v_P_2963_);
v_a_3216_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_a_3216_);
lean_dec_ref_known(v___x_3213_, 1);
v___y_3181_ = v_a_3200_;
v___y_3182_ = v___x_3203_;
v_a_3183_ = v_a_3216_;
goto v___jp_3180_;
}
}
}
else
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v_a_3219_; uint8_t v___x_3220_; 
v___x_3217_ = lean_io_get_num_heartbeats();
v___x_3218_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3002_, v_inheritedTraceOptions_3000_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_a_3219_);
lean_dec_ref(v___x_3218_);
v___x_3220_ = lean_unbox(v_a_3219_);
lean_dec(v_a_3219_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = lean_box(0);
v___x_3222_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2964_, v_rhs_2965_, v_P_2963_, v_cls_3002_, v___x_3202_, v___f_3003_, v___x_3131_, v___x_3221_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3153_ = v___x_3217_;
v___y_3154_ = v_a_3200_;
v___y_3155_ = v___x_3222_;
goto v___jp_3152_;
}
else
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3223_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_2965_);
lean_inc_ref(v_lhs_2964_);
lean_inc_ref(v_P_2963_);
v___x_3224_ = l_Lean_mkAppB(v_P_2963_, v_lhs_2964_, v_rhs_2965_);
v___x_3225_ = l_Lean_indentExpr(v___x_3224_);
v___x_3226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3223_);
lean_ctor_set(v___x_3226_, 1, v___x_3225_);
v___x_3227_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3002_, v___x_3226_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; lean_object* v___x_3229_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_a_3228_);
lean_dec_ref_known(v___x_3227_, 1);
v___x_3229_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2964_, v_rhs_2965_, v_P_2963_, v_cls_3002_, v___x_3202_, v___f_3003_, v___x_3131_, v_a_3228_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3153_ = v___x_3217_;
v___y_3154_ = v_a_3200_;
v___y_3155_ = v___x_3229_;
goto v___jp_3152_;
}
else
{
lean_object* v_a_3230_; 
lean_dec_ref(v_rhs_2965_);
lean_dec_ref(v_lhs_2964_);
lean_dec_ref(v_P_2963_);
v_a_3230_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_a_3230_);
lean_dec_ref_known(v___x_3227_, 1);
v___y_3148_ = v___x_3217_;
v___y_3149_ = v_a_3200_;
v_a_3150_ = v_a_3230_;
goto v___jp_3147_;
}
}
}
}
}
v___jp_2976_:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2978_, 0, v___y_2977_);
lean_ctor_set_uint8(v___x_2978_, 1, v___y_2977_);
v___x_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2978_);
return v___x_2979_;
}
v___jp_2980_:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2981_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_2982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2981_);
return v___x_2982_;
}
v___jp_2983_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
return v___x_2985_;
}
v___jp_2986_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2995_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7);
v___x_2996_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8));
v___x_2997_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2997_, 0, v___y_2988_);
lean_ctor_set(v___x_2997_, 1, v___x_2995_);
lean_ctor_set(v___x_2997_, 2, v___x_2996_);
v___x_2998_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___y_2987_, v___x_2997_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
return v___x_2998_;
}
v___jp_3004_:
{
lean_object* v___x_3014_; 
lean_inc_ref(v_lhs_2964_);
v___x_3014_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2964_);
if (lean_obj_tag(v___x_3014_) == 1)
{
lean_object* v_val_3015_; lean_object* v___x_3016_; 
v_val_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_val_3015_);
lean_dec_ref_known(v___x_3014_, 1);
lean_inc_ref(v_rhs_2965_);
v___x_3016_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2965_);
if (lean_obj_tag(v___x_3016_) == 1)
{
lean_object* v_val_3017_; uint8_t v___x_3018_; 
v_val_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_val_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v___x_3018_ = lean_expr_eqv(v_val_3015_, v_val_3017_);
if (v___x_3018_ == 0)
{
lean_object* v_inheritedTraceOptions_3019_; lean_object* v___x_3020_; lean_object* v_a_3021_; uint8_t v___x_3022_; 
lean_dec_ref(v_P_2963_);
v_inheritedTraceOptions_3019_ = lean_ctor_get(v___y_3012_, 13);
v___x_3020_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3002_, v_inheritedTraceOptions_3019_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref(v___x_3020_);
v___x_3022_ = lean_unbox(v_a_3021_);
lean_dec(v_a_3021_);
if (v___x_3022_ == 0)
{
lean_dec(v_val_3017_);
lean_dec(v_val_3015_);
lean_dec_ref(v_rhs_2965_);
lean_dec_ref(v_lhs_2964_);
v___y_2977_ = v___x_3018_;
goto v___jp_2976_;
}
else
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3023_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1);
v___x_3024_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3015_);
v___x_3025_ = l_Lean_MessageData_ofExpr(v___x_3024_);
v___x_3026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3023_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
v___x_3027_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3);
v___x_3028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3026_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
v___x_3029_ = l_Lean_indentExpr(v_lhs_2964_);
v___x_3030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3028_);
lean_ctor_set(v___x_3030_, 1, v___x_3029_);
v___x_3031_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5);
v___x_3032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3030_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3017_);
v___x_3034_ = l_Lean_MessageData_ofExpr(v___x_3033_);
v___x_3035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3032_);
lean_ctor_set(v___x_3035_, 1, v___x_3034_);
v___x_3036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
lean_ctor_set(v___x_3036_, 1, v___x_3027_);
v___x_3037_ = l_Lean_indentExpr(v_rhs_2965_);
v___x_3038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3036_);
lean_ctor_set(v___x_3038_, 1, v___x_3037_);
v___x_3039_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3002_, v___x_3038_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_dec_ref_known(v___x_3039_, 1);
v___y_2977_ = v___x_3018_;
goto v___jp_2976_;
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_3039_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_3039_);
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
else
{
lean_object* v_options_3048_; lean_object* v_inheritedTraceOptions_3049_; uint8_t v_hasTrace_3050_; uint8_t v___x_3051_; lean_object* v___x_3052_; lean_object* v___f_3053_; 
lean_dec(v_val_3017_);
v_options_3048_ = lean_ctor_get(v___y_3012_, 2);
v_inheritedTraceOptions_3049_ = lean_ctor_get(v___y_3012_, 13);
v_hasTrace_3050_ = lean_ctor_get_uint8(v_options_3048_, sizeof(void*)*1);
v___x_3051_ = 0;
v___x_3052_ = lean_box(v___x_3051_);
lean_inc(v_val_3015_);
v___f_3053_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 13, 5);
lean_closure_set(v___f_3053_, 0, v_val_3015_);
lean_closure_set(v___f_3053_, 1, v_lhs_2964_);
lean_closure_set(v___f_3053_, 2, v_rhs_2965_);
lean_closure_set(v___f_3053_, 3, v_P_2963_);
lean_closure_set(v___f_3053_, 4, v___x_3052_);
if (v_hasTrace_3050_ == 0)
{
v___y_2987_ = v___f_3053_;
v___y_2988_ = v_val_3015_;
v___y_2989_ = v___y_3008_;
v___y_2990_ = v___y_3009_;
v___y_2991_ = v___y_3010_;
v___y_2992_ = v___y_3011_;
v___y_2993_ = v___y_3012_;
v___y_2994_ = v___y_3013_;
goto v___jp_2986_;
}
else
{
lean_object* v___x_3054_; uint8_t v___x_3055_; 
v___x_3054_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3055_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3049_, v_options_3048_, v___x_3054_);
if (v___x_3055_ == 0)
{
v___y_2987_ = v___f_3053_;
v___y_2988_ = v_val_3015_;
v___y_2989_ = v___y_3008_;
v___y_2990_ = v___y_3009_;
v___y_2991_ = v___y_3010_;
v___y_2992_ = v___y_3011_;
v___y_2993_ = v___y_3012_;
v___y_2994_ = v___y_3013_;
goto v___jp_2986_;
}
else
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3056_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10);
lean_inc(v_val_3015_);
v___x_3057_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3015_);
v___x_3058_ = l_Lean_MessageData_ofExpr(v___x_3057_);
v___x_3059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3056_);
lean_ctor_set(v___x_3059_, 1, v___x_3058_);
v___x_3060_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12);
v___x_3061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3059_);
lean_ctor_set(v___x_3061_, 1, v___x_3060_);
v___x_3062_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3002_, v___x_3061_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_dec_ref_known(v___x_3062_, 1);
v___y_2987_ = v___f_3053_;
v___y_2988_ = v_val_3015_;
v___y_2989_ = v___y_3008_;
v___y_2990_ = v___y_3009_;
v___y_2991_ = v___y_3010_;
v___y_2992_ = v___y_3011_;
v___y_2993_ = v___y_3012_;
v___y_2994_ = v___y_3013_;
goto v___jp_2986_;
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_dec_ref(v___f_3053_);
lean_dec(v_val_3015_);
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_3062_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_3062_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_3071_; lean_object* v___x_3072_; lean_object* v_a_3073_; uint8_t v___x_3074_; 
lean_dec(v___x_3016_);
lean_dec(v_val_3015_);
lean_dec_ref(v_lhs_2964_);
lean_dec_ref(v_P_2963_);
v_inheritedTraceOptions_3071_ = lean_ctor_get(v___y_3012_, 13);
v___x_3072_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3002_, v_inheritedTraceOptions_3071_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_a_3073_);
lean_dec_ref(v___x_3072_);
v___x_3074_ = lean_unbox(v_a_3073_);
lean_dec(v_a_3073_);
if (v___x_3074_ == 0)
{
lean_dec_ref(v_rhs_2965_);
goto v___jp_2983_;
}
else
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3075_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_3076_ = l_Lean_indentExpr(v_rhs_2965_);
v___x_3077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3075_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
v___x_3078_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3002_, v___x_3077_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_dec_ref_known(v___x_3078_, 1);
goto v___jp_2983_;
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_3078_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3078_);
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
}
}
else
{
lean_object* v_inheritedTraceOptions_3087_; lean_object* v___x_3088_; lean_object* v_a_3089_; uint8_t v___x_3090_; 
lean_dec(v___x_3014_);
lean_dec_ref(v_rhs_2965_);
lean_dec_ref(v_P_2963_);
v_inheritedTraceOptions_3087_ = lean_ctor_get(v___y_3012_, 13);
v___x_3088_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3002_, v_inheritedTraceOptions_3087_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_a_3089_);
lean_dec_ref(v___x_3088_);
v___x_3090_ = lean_unbox(v_a_3089_);
lean_dec(v_a_3089_);
if (v___x_3090_ == 0)
{
lean_dec_ref(v_lhs_2964_);
goto v___jp_2980_;
}
else
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3091_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_3092_ = l_Lean_indentExpr(v_lhs_2964_);
v___x_3093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3091_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
v___x_3094_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3002_, v___x_3093_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_dec_ref_known(v___x_3094_, 1);
goto v___jp_2980_;
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3094_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3094_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
}
}
v___jp_3103_:
{
if (v_____do__lift_3104_ == 0)
{
v___y_3005_ = v___y_3105_;
v___y_3006_ = v___y_3106_;
v___y_3007_ = v___y_3107_;
v___y_3008_ = v___y_3108_;
v___y_3009_ = v___y_3109_;
v___y_3010_ = v___y_3110_;
v___y_3011_ = v___y_3111_;
v___y_3012_ = v___y_3112_;
v___y_3013_ = v___y_3113_;
goto v___jp_3004_;
}
else
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3114_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_2965_);
lean_inc_ref(v_lhs_2964_);
lean_inc_ref(v_P_2963_);
v___x_3115_ = l_Lean_mkAppB(v_P_2963_, v_lhs_2964_, v_rhs_2965_);
v___x_3116_ = l_Lean_indentExpr(v___x_3115_);
v___x_3117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3114_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
v___x_3118_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3002_, v___x_3117_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_dec_ref_known(v___x_3118_, 1);
v___y_3005_ = v___y_3105_;
v___y_3006_ = v___y_3106_;
v___y_3007_ = v___y_3107_;
v___y_3008_ = v___y_3108_;
v___y_3009_ = v___y_3109_;
v___y_3010_ = v___y_3110_;
v___y_3011_ = v___y_3111_;
v___y_3012_ = v___y_3112_;
v___y_3013_ = v___y_3113_;
goto v___jp_3004_;
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec_ref(v_rhs_2965_);
lean_dec_ref(v_lhs_2964_);
lean_dec_ref(v_P_2963_);
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3118_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3118_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___boxed(lean_object* v_P_3236_, lean_object* v_lhs_3237_, lean_object* v_rhs_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v_P_3236_, v_lhs_3237_, v_rhs_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_);
lean_dec(v_a_3247_);
lean_dec_ref(v_a_3246_);
lean_dec(v_a_3245_);
lean_dec_ref(v_a_3244_);
lean_dec(v_a_3243_);
lean_dec_ref(v_a_3242_);
lean_dec(v_a_3241_);
lean_dec_ref(v_a_3240_);
lean_dec(v_a_3239_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(lean_object* v_cls_3250_, lean_object* v_msg_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
lean_object* v___x_3262_; 
v___x_3262_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3250_, v_msg_3251_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object* v_cls_3263_, lean_object* v_msg_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(v_cls_3263_, v_msg_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec(v___y_3265_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(lean_object* v_00_u03b1_3276_, lean_object* v_x_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_3277_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___boxed(lean_object* v_00_u03b1_3289_, lean_object* v_x_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(v_00_u03b1_3289_, v_x_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(lean_object* v_oldTraces_3302_, lean_object* v_data_3303_, lean_object* v_ref_3304_, lean_object* v_msg_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_3302_, v_data_3303_, v_ref_3304_, v_msg_3305_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___boxed(lean_object* v_oldTraces_3317_, lean_object* v_data_3318_, lean_object* v_ref_3319_, lean_object* v_msg_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(v_oldTraces_3317_, v_data_3318_, v_ref_3319_, v_msg_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec(v___y_3321_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(lean_object* v_x_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0___boxed(lean_object* v_x_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v_x_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(lean_object* v_arg_3362_, lean_object* v_arg_3363_, lean_object* v_arg_3364_, lean_object* v_arg_3365_, lean_object* v_____r_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v___x_3377_; 
lean_inc_ref(v_arg_3362_);
v___x_3377_ = l_Lean_Meta_getDecLevel(v_arg_3362_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3378_);
lean_dec_ref_known(v___x_3377_, 1);
v___x_3379_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2));
v___x_3380_ = lean_box(0);
v___x_3381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3381_, 0, v_a_3378_);
lean_ctor_set(v___x_3381_, 1, v___x_3380_);
v___x_3382_ = l_Lean_Expr_const___override(v___x_3379_, v___x_3381_);
v___x_3383_ = l_Lean_mkAppB(v___x_3382_, v_arg_3362_, v_arg_3363_);
v___x_3384_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3383_, v_arg_3364_, v_arg_3365_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
return v___x_3384_;
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
lean_dec_ref(v_arg_3365_);
lean_dec_ref(v_arg_3364_);
lean_dec_ref(v_arg_3363_);
lean_dec_ref(v_arg_3362_);
v_a_3385_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3377_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3377_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___boxed(lean_object* v_arg_3393_, lean_object* v_arg_3394_, lean_object* v_arg_3395_, lean_object* v_arg_3396_, lean_object* v_____r_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3393_, v_arg_3394_, v_arg_3395_, v_arg_3396_, v_____r_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(lean_object* v_arg_3412_, lean_object* v_arg_3413_, lean_object* v_arg_3414_, lean_object* v_____r_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
lean_object* v___x_3426_; 
lean_inc_ref(v_arg_3412_);
v___x_3426_ = l_Lean_Meta_getLevel(v_arg_3412_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_a_3427_);
lean_dec_ref_known(v___x_3426_, 1);
v___x_3428_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1));
v___x_3429_ = lean_box(0);
v___x_3430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3430_, 0, v_a_3427_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
v___x_3431_ = l_Lean_Expr_const___override(v___x_3428_, v___x_3430_);
v___x_3432_ = l_Lean_Expr_app___override(v___x_3431_, v_arg_3412_);
v___x_3433_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3432_, v_arg_3413_, v_arg_3414_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
return v___x_3433_;
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec_ref(v_arg_3414_);
lean_dec_ref(v_arg_3413_);
lean_dec_ref(v_arg_3412_);
v_a_3434_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3426_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3426_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___boxed(lean_object* v_arg_3442_, lean_object* v_arg_3443_, lean_object* v_arg_3444_, lean_object* v_____r_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
lean_object* v_res_3456_; 
v_res_3456_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3442_, v_arg_3443_, v_arg_3444_, v_____r_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
return v_res_3456_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1(void){
_start:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3458_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0));
v___x_3459_ = l_Lean_stringToMessageData(v___x_3458_);
return v___x_3459_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2(void){
_start:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3460_ = l_Lean_checkEmoji;
v___x_3461_ = l_Lean_stringToMessageData(v___x_3460_);
return v___x_3461_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3(void){
_start:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3462_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2);
v___x_3463_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1);
v___x_3464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
lean_ctor_set(v___x_3464_, 1, v___x_3462_);
return v___x_3464_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5(void){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3466_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4));
v___x_3467_ = l_Lean_stringToMessageData(v___x_3466_);
return v___x_3467_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6(void){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3468_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5);
v___x_3469_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3);
v___x_3470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
lean_ctor_set(v___x_3470_, 1, v___x_3468_);
return v___x_3470_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8(void){
_start:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3472_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7));
v___x_3473_ = l_Lean_stringToMessageData(v___x_3472_);
return v___x_3473_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9(void){
_start:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3474_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8);
v___x_3475_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3);
v___x_3476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3475_);
lean_ctor_set(v___x_3476_, 1, v___x_3474_);
return v___x_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(lean_object* v_e_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_){
_start:
{
lean_object* v___y_3489_; lean_object* v___x_3521_; 
v___x_3521_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3477_, v_a_3484_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; lean_object* v___x_3523_; uint8_t v___x_3524_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3522_);
lean_dec_ref_known(v___x_3521_, 1);
v___x_3523_ = l_Lean_Expr_cleanupAnnotations(v_a_3522_);
v___x_3524_ = l_Lean_Expr_isApp(v___x_3523_);
if (v___x_3524_ == 0)
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
lean_dec_ref(v___x_3523_);
v___x_3525_ = lean_box(0);
v___x_3526_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3525_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
v___y_3489_ = v___x_3526_;
goto v___jp_3488_;
}
else
{
lean_object* v_arg_3527_; lean_object* v___x_3528_; uint8_t v___x_3529_; 
v_arg_3527_ = lean_ctor_get(v___x_3523_, 1);
lean_inc_ref(v_arg_3527_);
v___x_3528_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3523_);
v___x_3529_ = l_Lean_Expr_isApp(v___x_3528_);
if (v___x_3529_ == 0)
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
lean_dec_ref(v___x_3528_);
lean_dec_ref(v_arg_3527_);
v___x_3530_ = lean_box(0);
v___x_3531_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3530_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
v___y_3489_ = v___x_3531_;
goto v___jp_3488_;
}
else
{
lean_object* v_arg_3532_; lean_object* v___x_3533_; uint8_t v___x_3534_; 
v_arg_3532_ = lean_ctor_get(v___x_3528_, 1);
lean_inc_ref(v_arg_3532_);
v___x_3533_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3528_);
v___x_3534_ = l_Lean_Expr_isApp(v___x_3533_);
if (v___x_3534_ == 0)
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
lean_dec_ref(v___x_3533_);
lean_dec_ref(v_arg_3532_);
lean_dec_ref(v_arg_3527_);
v___x_3535_ = lean_box(0);
v___x_3536_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3535_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
v___y_3489_ = v___x_3536_;
goto v___jp_3488_;
}
else
{
lean_object* v_arg_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; uint8_t v___x_3540_; 
v_arg_3537_ = lean_ctor_get(v___x_3533_, 1);
lean_inc_ref(v_arg_3537_);
v___x_3538_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3533_);
v___x_3539_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1));
v___x_3540_ = l_Lean_Expr_isConstOf(v___x_3538_, v___x_3539_);
if (v___x_3540_ == 0)
{
uint8_t v___x_3541_; 
v___x_3541_ = l_Lean_Expr_isApp(v___x_3538_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
lean_dec_ref(v___x_3538_);
lean_dec_ref(v_arg_3537_);
lean_dec_ref(v_arg_3532_);
lean_dec_ref(v_arg_3527_);
v___x_3542_ = lean_box(0);
v___x_3543_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3542_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
v___y_3489_ = v___x_3543_;
goto v___jp_3488_;
}
else
{
lean_object* v_arg_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; uint8_t v___x_3547_; 
v_arg_3544_ = lean_ctor_get(v___x_3538_, 1);
lean_inc_ref(v_arg_3544_);
v___x_3545_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3538_);
v___x_3546_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2));
v___x_3547_ = l_Lean_Expr_isConstOf(v___x_3545_, v___x_3546_);
lean_dec_ref(v___x_3545_);
if (v___x_3547_ == 0)
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
lean_dec_ref(v_arg_3544_);
lean_dec_ref(v_arg_3537_);
lean_dec_ref(v_arg_3532_);
lean_dec_ref(v_arg_3527_);
v___x_3548_ = lean_box(0);
v___x_3549_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3548_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
v___y_3489_ = v___x_3549_;
goto v___jp_3488_;
}
else
{
lean_object* v_options_3550_; lean_object* v_inheritedTraceOptions_3551_; uint8_t v_hasTrace_3552_; 
v_options_3550_ = lean_ctor_get(v_a_3485_, 2);
v_inheritedTraceOptions_3551_ = lean_ctor_get(v_a_3485_, 13);
v_hasTrace_3552_ = lean_ctor_get_uint8(v_options_3550_, sizeof(void*)*1);
if (v_hasTrace_3552_ == 0)
{
goto v___jp_3553_;
}
else
{
lean_object* v___x_3556_; lean_object* v___x_3557_; uint8_t v___x_3558_; 
v___x_3556_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3557_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3558_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3551_, v_options_3550_, v___x_3557_);
if (v___x_3558_ == 0)
{
goto v___jp_3553_;
}
else
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3559_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6);
v___x_3560_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3556_, v___x_3559_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v_a_3561_; lean_object* v___x_3562_; 
v_a_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_a_3561_);
lean_dec_ref_known(v___x_3560_, 1);
v___x_3562_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3544_, v_arg_3537_, v_arg_3532_, v_arg_3527_, v_a_3561_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
v___y_3489_ = v___x_3562_;
goto v___jp_3488_;
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_dec_ref(v_arg_3544_);
lean_dec_ref(v_arg_3537_);
lean_dec_ref(v_arg_3532_);
lean_dec_ref(v_arg_3527_);
v_a_3563_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3560_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3560_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
}
v___jp_3553_:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3554_ = lean_box(0);
v___x_3555_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3544_, v_arg_3537_, v_arg_3532_, v_arg_3527_, v___x_3554_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
v___y_3489_ = v___x_3555_;
goto v___jp_3488_;
}
}
}
}
else
{
lean_object* v_options_3571_; lean_object* v_inheritedTraceOptions_3572_; uint8_t v_hasTrace_3573_; 
lean_dec_ref(v___x_3538_);
v_options_3571_ = lean_ctor_get(v_a_3485_, 2);
v_inheritedTraceOptions_3572_ = lean_ctor_get(v_a_3485_, 13);
v_hasTrace_3573_ = lean_ctor_get_uint8(v_options_3571_, sizeof(void*)*1);
if (v_hasTrace_3573_ == 0)
{
goto v___jp_3574_;
}
else
{
lean_object* v___x_3577_; lean_object* v___x_3578_; uint8_t v___x_3579_; 
v___x_3577_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3578_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3579_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3572_, v_options_3571_, v___x_3578_);
if (v___x_3579_ == 0)
{
goto v___jp_3574_;
}
else
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3580_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9);
v___x_3581_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3577_, v___x_3580_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; lean_object* v___x_3583_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3582_);
lean_dec_ref_known(v___x_3581_, 1);
v___x_3583_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3537_, v_arg_3532_, v_arg_3527_, v_a_3582_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
v___y_3489_ = v___x_3583_;
goto v___jp_3488_;
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_dec_ref(v_arg_3537_);
lean_dec_ref(v_arg_3532_);
lean_dec_ref(v_arg_3527_);
v_a_3584_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3581_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3581_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3584_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
}
v___jp_3574_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3575_ = lean_box(0);
v___x_3576_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3537_, v_arg_3532_, v_arg_3527_, v___x_3575_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
v___y_3489_ = v___x_3576_;
goto v___jp_3488_;
}
}
}
}
}
}
else
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
v_a_3592_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3521_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3521_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
v___jp_3488_:
{
if (lean_obj_tag(v___y_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3520_; 
v_a_3490_ = lean_ctor_get(v___y_3489_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___y_3489_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3492_ = v___y_3489_;
v_isShared_3493_ = v_isSharedCheck_3520_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___y_3489_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3520_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
if (lean_obj_tag(v_a_3490_) == 0)
{
uint8_t v_contextDependent_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3505_; 
v_contextDependent_3494_ = lean_ctor_get_uint8(v_a_3490_, 1);
v_isSharedCheck_3505_ = !lean_is_exclusive(v_a_3490_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3496_ = v_a_3490_;
v_isShared_3497_ = v_isSharedCheck_3505_;
goto v_resetjp_3495_;
}
else
{
lean_dec(v_a_3490_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3505_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
uint8_t v___x_3498_; lean_object* v___x_3500_; 
v___x_3498_ = 1;
if (v_isShared_3497_ == 0)
{
v___x_3500_ = v___x_3496_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_3504_, 1, v_contextDependent_3494_);
v___x_3500_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
lean_object* v___x_3502_; 
lean_ctor_set_uint8(v___x_3500_, 0, v___x_3498_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v___x_3500_);
v___x_3502_ = v___x_3492_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3500_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
else
{
lean_object* v_e_x27_3506_; lean_object* v_proof_3507_; uint8_t v_contextDependent_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3519_; 
v_e_x27_3506_ = lean_ctor_get(v_a_3490_, 0);
v_proof_3507_ = lean_ctor_get(v_a_3490_, 1);
v_contextDependent_3508_ = lean_ctor_get_uint8(v_a_3490_, sizeof(void*)*2 + 1);
v_isSharedCheck_3519_ = !lean_is_exclusive(v_a_3490_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3510_ = v_a_3490_;
v_isShared_3511_ = v_isSharedCheck_3519_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_proof_3507_);
lean_inc(v_e_x27_3506_);
lean_dec(v_a_3490_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3519_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
uint8_t v___x_3512_; lean_object* v___x_3514_; 
v___x_3512_ = 1;
if (v_isShared_3511_ == 0)
{
v___x_3514_ = v___x_3510_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_e_x27_3506_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v_proof_3507_);
lean_ctor_set_uint8(v_reuseFailAlloc_3518_, sizeof(void*)*2 + 1, v_contextDependent_3508_);
v___x_3514_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
lean_object* v___x_3516_; 
lean_ctor_set_uint8(v___x_3514_, sizeof(void*)*2, v___x_3512_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v___x_3514_);
v___x_3516_ = v___x_3492_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3514_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
}
}
else
{
return v___y_3489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed(lean_object* v_e_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(v_e_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_);
lean_dec(v_a_3609_);
lean_dec_ref(v_a_3608_);
lean_dec(v_a_3607_);
lean_dec_ref(v_a_3606_);
lean_dec(v_a_3605_);
lean_dec_ref(v_a_3604_);
lean_dec(v_a_3603_);
lean_dec_ref(v_a_3602_);
lean_dec(v_a_3601_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(lean_object* v_x_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v___x_3625_; 
lean_inc(v___y_3619_);
lean_inc_ref(v___y_3618_);
lean_inc(v___y_3617_);
lean_inc_ref(v___y_3616_);
lean_inc(v___y_3615_);
lean_inc(v___y_3614_);
lean_inc_ref(v___y_3613_);
v___x_3625_ = lean_apply_12(v_x_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, lean_box(0));
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed(lean_object* v_x_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(v_x_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object* v_mvarId_3640_, lean_object* v_x_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v___f_3654_; lean_object* v___x_3655_; 
lean_inc(v___y_3648_);
lean_inc_ref(v___y_3647_);
lean_inc(v___y_3646_);
lean_inc_ref(v___y_3645_);
lean_inc(v___y_3644_);
lean_inc(v___y_3643_);
lean_inc_ref(v___y_3642_);
v___f_3654_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_3654_, 0, v_x_3641_);
lean_closure_set(v___f_3654_, 1, v___y_3642_);
lean_closure_set(v___f_3654_, 2, v___y_3643_);
lean_closure_set(v___f_3654_, 3, v___y_3644_);
lean_closure_set(v___f_3654_, 4, v___y_3645_);
lean_closure_set(v___f_3654_, 5, v___y_3646_);
lean_closure_set(v___f_3654_, 6, v___y_3647_);
lean_closure_set(v___f_3654_, 7, v___y_3648_);
v___x_3655_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3640_, v___f_3654_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3655_) == 0)
{
return v___x_3655_;
}
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___x_3655_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3655_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object* v_mvarId_3664_, lean_object* v_x_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_mvarId_3664_, v_x_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v___y_3668_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(lean_object* v_00_u03b1_3679_, lean_object* v_mvarId_3680_, lean_object* v_x_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
lean_object* v___x_3694_; 
v___x_3694_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_mvarId_3680_, v_x_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object* v_00_u03b1_3695_, lean_object* v_mvarId_3696_, lean_object* v_x_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(v_00_u03b1_3695_, v_mvarId_3696_, v_x_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v___y_3700_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0(lean_object* v_x_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_){
_start:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0___boxed(lean_object* v_x_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0(v_x_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
lean_dec(v___y_3731_);
lean_dec_ref(v___y_3730_);
lean_dec(v___y_3729_);
lean_dec_ref(v___y_3728_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
lean_dec(v___y_3725_);
lean_dec_ref(v_x_3724_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(lean_object* v_snd_3736_, lean_object* v_a_3737_, lean_object* v___x_3738_, lean_object* v_____r_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3752_ = lean_array_push(v_snd_3736_, v_a_3737_);
v___x_3753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3738_);
lean_ctor_set(v___x_3753_, 1, v___x_3752_);
v___x_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3753_);
v___x_3755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3754_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1___boxed(lean_object* v_snd_3756_, lean_object* v_a_3757_, lean_object* v___x_3758_, lean_object* v_____r_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(v_snd_3756_, v_a_3757_, v___x_3758_, v_____r_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
lean_dec(v___y_3766_);
lean_dec_ref(v___y_3765_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object* v_cls_3773_, lean_object* v_msg_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_){
_start:
{
lean_object* v_ref_3780_; lean_object* v___x_3781_; lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3826_; 
v_ref_3780_ = lean_ctor_get(v___y_3777_, 5);
v___x_3781_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3784_ = v___x_3781_;
v_isShared_3785_ = v_isSharedCheck_3826_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v___x_3781_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3826_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3786_; lean_object* v_traceState_3787_; lean_object* v_env_3788_; lean_object* v_nextMacroScope_3789_; lean_object* v_ngen_3790_; lean_object* v_auxDeclNGen_3791_; lean_object* v_cache_3792_; lean_object* v_messages_3793_; lean_object* v_infoState_3794_; lean_object* v_snapshotTasks_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3825_; 
v___x_3786_ = lean_st_ref_take(v___y_3778_);
v_traceState_3787_ = lean_ctor_get(v___x_3786_, 4);
v_env_3788_ = lean_ctor_get(v___x_3786_, 0);
v_nextMacroScope_3789_ = lean_ctor_get(v___x_3786_, 1);
v_ngen_3790_ = lean_ctor_get(v___x_3786_, 2);
v_auxDeclNGen_3791_ = lean_ctor_get(v___x_3786_, 3);
v_cache_3792_ = lean_ctor_get(v___x_3786_, 5);
v_messages_3793_ = lean_ctor_get(v___x_3786_, 6);
v_infoState_3794_ = lean_ctor_get(v___x_3786_, 7);
v_snapshotTasks_3795_ = lean_ctor_get(v___x_3786_, 8);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3797_ = v___x_3786_;
v_isShared_3798_ = v_isSharedCheck_3825_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_snapshotTasks_3795_);
lean_inc(v_infoState_3794_);
lean_inc(v_messages_3793_);
lean_inc(v_cache_3792_);
lean_inc(v_traceState_3787_);
lean_inc(v_auxDeclNGen_3791_);
lean_inc(v_ngen_3790_);
lean_inc(v_nextMacroScope_3789_);
lean_inc(v_env_3788_);
lean_dec(v___x_3786_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3825_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
uint64_t v_tid_3799_; lean_object* v_traces_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3824_; 
v_tid_3799_ = lean_ctor_get_uint64(v_traceState_3787_, sizeof(void*)*1);
v_traces_3800_ = lean_ctor_get(v_traceState_3787_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v_traceState_3787_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3802_ = v_traceState_3787_;
v_isShared_3803_ = v_isSharedCheck_3824_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_traces_3800_);
lean_dec(v_traceState_3787_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3824_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3804_; double v___x_3805_; uint8_t v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3814_; 
v___x_3804_ = lean_box(0);
v___x_3805_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_3806_ = 0;
v___x_3807_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_3808_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3808_, 0, v_cls_3773_);
lean_ctor_set(v___x_3808_, 1, v___x_3804_);
lean_ctor_set(v___x_3808_, 2, v___x_3807_);
lean_ctor_set_float(v___x_3808_, sizeof(void*)*3, v___x_3805_);
lean_ctor_set_float(v___x_3808_, sizeof(void*)*3 + 8, v___x_3805_);
lean_ctor_set_uint8(v___x_3808_, sizeof(void*)*3 + 16, v___x_3806_);
v___x_3809_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_3810_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3808_);
lean_ctor_set(v___x_3810_, 1, v_a_3782_);
lean_ctor_set(v___x_3810_, 2, v___x_3809_);
lean_inc(v_ref_3780_);
v___x_3811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3811_, 0, v_ref_3780_);
lean_ctor_set(v___x_3811_, 1, v___x_3810_);
v___x_3812_ = l_Lean_PersistentArray_push___redArg(v_traces_3800_, v___x_3811_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 0, v___x_3812_);
v___x_3814_ = v___x_3802_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v___x_3812_);
lean_ctor_set_uint64(v_reuseFailAlloc_3823_, sizeof(void*)*1, v_tid_3799_);
v___x_3814_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
lean_object* v___x_3816_; 
if (v_isShared_3798_ == 0)
{
lean_ctor_set(v___x_3797_, 4, v___x_3814_);
v___x_3816_ = v___x_3797_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_env_3788_);
lean_ctor_set(v_reuseFailAlloc_3822_, 1, v_nextMacroScope_3789_);
lean_ctor_set(v_reuseFailAlloc_3822_, 2, v_ngen_3790_);
lean_ctor_set(v_reuseFailAlloc_3822_, 3, v_auxDeclNGen_3791_);
lean_ctor_set(v_reuseFailAlloc_3822_, 4, v___x_3814_);
lean_ctor_set(v_reuseFailAlloc_3822_, 5, v_cache_3792_);
lean_ctor_set(v_reuseFailAlloc_3822_, 6, v_messages_3793_);
lean_ctor_set(v_reuseFailAlloc_3822_, 7, v_infoState_3794_);
lean_ctor_set(v_reuseFailAlloc_3822_, 8, v_snapshotTasks_3795_);
v___x_3816_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3820_; 
v___x_3817_ = lean_st_ref_put(v___y_3778_, v___x_3816_);
v___x_3818_ = lean_box(0);
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 0, v___x_3818_);
v___x_3820_ = v___x_3784_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v___x_3818_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object* v_cls_3827_, lean_object* v_msg_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
lean_object* v_res_3834_; 
v_res_3834_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_cls_3827_, v_msg_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(uint8_t v___x_3835_, lean_object* v___f_3836_, lean_object* v_____r_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
lean_object* v___x_3850_; lean_object* v_caches_3851_; lean_object* v_typeAnalysis_3852_; lean_object* v_target_3853_; lean_object* v_hypotheses_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3864_; 
v___x_3850_ = lean_st_ref_take(v___y_3839_);
v_caches_3851_ = lean_ctor_get(v___x_3850_, 0);
v_typeAnalysis_3852_ = lean_ctor_get(v___x_3850_, 1);
v_target_3853_ = lean_ctor_get(v___x_3850_, 2);
v_hypotheses_3854_ = lean_ctor_get(v___x_3850_, 3);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3856_ = v___x_3850_;
v_isShared_3857_ = v_isSharedCheck_3864_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_hypotheses_3854_);
lean_inc(v_target_3853_);
lean_inc(v_typeAnalysis_3852_);
lean_inc(v_caches_3851_);
lean_dec(v___x_3850_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3864_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3859_; 
if (v_isShared_3857_ == 0)
{
v___x_3859_ = v___x_3856_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_caches_3851_);
lean_ctor_set(v_reuseFailAlloc_3863_, 1, v_typeAnalysis_3852_);
lean_ctor_set(v_reuseFailAlloc_3863_, 2, v_target_3853_);
lean_ctor_set(v_reuseFailAlloc_3863_, 3, v_hypotheses_3854_);
v___x_3859_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
lean_ctor_set_uint8(v___x_3859_, sizeof(void*)*4, v___x_3835_);
v___x_3860_ = lean_st_ref_put(v___y_3839_, v___x_3859_);
v___x_3861_ = lean_box(0);
lean_inc(v___y_3848_);
lean_inc_ref(v___y_3847_);
lean_inc(v___y_3846_);
lean_inc_ref(v___y_3845_);
lean_inc(v___y_3844_);
lean_inc_ref(v___y_3843_);
lean_inc(v___y_3842_);
lean_inc_ref(v___y_3841_);
lean_inc(v___y_3840_);
lean_inc(v___y_3839_);
lean_inc_ref(v___y_3838_);
v___x_3862_ = lean_apply_13(v___f_3836_, v___x_3861_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, lean_box(0));
return v___x_3862_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2___boxed(lean_object* v___x_3865_, lean_object* v___f_3866_, lean_object* v_____r_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
uint8_t v___x_10030__boxed_3880_; lean_object* v_res_3881_; 
v___x_10030__boxed_3880_ = lean_unbox(v___x_3865_);
v_res_3881_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_10030__boxed_3880_, v___f_3866_, v_____r_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3870_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
return v_res_3881_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3883_; lean_object* v___f_3884_; lean_object* v_methods_3885_; 
v___x_3883_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed), 11, 0);
v___f_3884_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__0));
v_methods_3885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_methods_3885_, 0, v___f_3884_);
lean_ctor_set(v_methods_3885_, 1, v___x_3883_);
return v_methods_3885_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3887_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__2));
v___x_3888_ = l_Lean_stringToMessageData(v___x_3887_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object* v_upperBound_3889_, lean_object* v___x_3890_, lean_object* v_config_3891_, lean_object* v_a_3892_, lean_object* v_b_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_){
_start:
{
lean_object* v___y_3907_; uint8_t v___x_3929_; 
v___x_3929_ = lean_nat_dec_lt(v_a_3892_, v_upperBound_3889_);
if (v___x_3929_ == 0)
{
lean_object* v___x_3930_; 
lean_dec(v_a_3892_);
lean_dec_ref(v_config_3891_);
v___x_3930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3930_, 0, v_b_3893_);
return v___x_3930_;
}
else
{
uint8_t v___x_3931_; lean_object* v_methods_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3931_ = 1;
v_methods_3932_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1);
v___x_3933_ = lean_array_fget_borrowed(v___x_3890_, v_a_3892_);
lean_inc(v___x_3933_);
lean_inc_ref(v_config_3891_);
v___x_3934_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v___x_3931_, v_methods_3932_, v_config_3891_, v___x_3933_, v___y_3895_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; lean_object* v_snd_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3998_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
lean_inc(v_a_3935_);
lean_dec_ref_known(v___x_3934_, 1);
v_snd_3936_ = lean_ctor_get(v_b_3893_, 1);
v_isSharedCheck_3998_ = !lean_is_exclusive(v_b_3893_);
if (v_isSharedCheck_3998_ == 0)
{
lean_object* v_unused_3999_; 
v_unused_3999_ = lean_ctor_get(v_b_3893_, 0);
lean_dec(v_unused_3999_);
v___x_3938_ = v_b_3893_;
v_isShared_3939_ = v_isSharedCheck_3998_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_snd_3936_);
lean_dec(v_b_3893_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3998_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v_type_3940_; lean_object* v_value_3941_; uint8_t v___x_3942_; 
v_type_3940_ = lean_ctor_get(v_a_3935_, 1);
v_value_3941_ = lean_ctor_get(v_a_3935_, 2);
lean_inc_ref(v_type_3940_);
v___x_3942_ = l_Lean_Expr_isFalse(v_type_3940_);
if (v___x_3942_ == 0)
{
lean_object* v_type_3943_; lean_object* v___x_3944_; lean_object* v___f_3945_; uint8_t v___x_3973_; 
lean_del_object(v___x_3938_);
v_type_3943_ = lean_ctor_get(v___x_3933_, 1);
v___x_3944_ = lean_box(0);
lean_inc(v_a_3935_);
lean_inc(v_snd_3936_);
v___f_3945_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1___boxed), 16, 3);
lean_closure_set(v___f_3945_, 0, v_snd_3936_);
lean_closure_set(v___f_3945_, 1, v_a_3935_);
lean_closure_set(v___f_3945_, 2, v___x_3944_);
v___x_3973_ = lean_expr_eqv(v_type_3943_, v_type_3940_);
if (v___x_3973_ == 0)
{
lean_inc_ref(v_type_3940_);
lean_dec(v_snd_3936_);
lean_dec(v_a_3935_);
goto v___jp_3949_;
}
else
{
if (v___x_3942_ == 0)
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
lean_dec_ref(v___f_3945_);
v___x_3974_ = lean_box(0);
v___x_3975_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(v_snd_3936_, v_a_3935_, v___x_3944_, v___x_3974_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
v___y_3907_ = v___x_3975_;
goto v___jp_3906_;
}
else
{
lean_inc_ref(v_type_3940_);
lean_dec(v_snd_3936_);
lean_dec(v_a_3935_);
goto v___jp_3949_;
}
}
v___jp_3946_:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3947_ = lean_box(0);
v___x_3948_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_3929_, v___f_3945_, v___x_3947_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
v___y_3907_ = v___x_3948_;
goto v___jp_3906_;
}
v___jp_3949_:
{
lean_object* v_options_3950_; uint8_t v_hasTrace_3951_; 
v_options_3950_ = lean_ctor_get(v___y_3903_, 2);
v_hasTrace_3951_ = lean_ctor_get_uint8(v_options_3950_, sizeof(void*)*1);
if (v_hasTrace_3951_ == 0)
{
lean_dec_ref(v_type_3940_);
goto v___jp_3946_;
}
else
{
lean_object* v_inheritedTraceOptions_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; uint8_t v___x_3955_; 
v_inheritedTraceOptions_3952_ = lean_ctor_get(v___y_3903_, 13);
v___x_3953_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3954_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3955_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3952_, v_options_3950_, v___x_3954_);
if (v___x_3955_ == 0)
{
lean_dec_ref(v_type_3940_);
goto v___jp_3946_;
}
else
{
lean_object* v_type_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v_type_3956_ = lean_ctor_get(v___x_3933_, 1);
lean_inc_ref(v_type_3956_);
v___x_3957_ = l_Lean_MessageData_ofExpr(v_type_3956_);
v___x_3958_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3);
v___x_3959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3957_);
lean_ctor_set(v___x_3959_, 1, v___x_3958_);
v___x_3960_ = l_Lean_MessageData_ofExpr(v_type_3940_);
v___x_3961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3959_);
lean_ctor_set(v___x_3961_, 1, v___x_3960_);
v___x_3962_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v___x_3953_, v___x_3961_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v_a_3963_; lean_object* v___x_3964_; 
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
lean_inc(v_a_3963_);
lean_dec_ref_known(v___x_3962_, 1);
v___x_3964_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_3929_, v___f_3945_, v_a_3963_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
v___y_3907_ = v___x_3964_;
goto v___jp_3906_;
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
lean_dec_ref(v___f_3945_);
lean_dec(v_a_3892_);
lean_dec_ref(v_config_3891_);
v_a_3965_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3962_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3962_);
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
}
else
{
lean_object* v___x_3976_; 
lean_inc_ref(v_value_3941_);
lean_dec(v_a_3935_);
lean_dec(v_a_3892_);
lean_dec_ref(v_config_3891_);
v___x_3976_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_3941_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3988_; 
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3988_ == 0)
{
lean_object* v_unused_3989_; 
v_unused_3989_ = lean_ctor_get(v___x_3976_, 0);
lean_dec(v_unused_3989_);
v___x_3978_ = v___x_3976_;
v_isShared_3979_ = v_isSharedCheck_3988_;
goto v_resetjp_3977_;
}
else
{
lean_dec(v___x_3976_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3988_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3983_; 
v___x_3980_ = lean_box(v___x_3929_);
v___x_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3980_);
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 0, v___x_3981_);
v___x_3983_ = v___x_3938_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v___x_3981_);
lean_ctor_set(v_reuseFailAlloc_3987_, 1, v_snd_3936_);
v___x_3983_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
lean_object* v___x_3985_; 
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 0, v___x_3983_);
v___x_3985_ = v___x_3978_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v___x_3983_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_del_object(v___x_3938_);
lean_dec(v_snd_3936_);
v_a_3990_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3976_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3976_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
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
}
}
else
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
lean_dec_ref(v_b_3893_);
lean_dec(v_a_3892_);
lean_dec_ref(v_config_3891_);
v_a_4000_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4002_ = v___x_3934_;
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3934_);
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
v___jp_3906_:
{
if (lean_obj_tag(v___y_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3920_; 
v_a_3908_ = lean_ctor_get(v___y_3907_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___y_3907_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3910_ = v___y_3907_;
v_isShared_3911_ = v_isSharedCheck_3920_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___y_3907_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3920_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
if (lean_obj_tag(v_a_3908_) == 0)
{
lean_object* v_a_3912_; lean_object* v___x_3914_; 
lean_dec(v_a_3892_);
lean_dec_ref(v_config_3891_);
v_a_3912_ = lean_ctor_get(v_a_3908_, 0);
lean_inc(v_a_3912_);
lean_dec_ref_known(v_a_3908_, 1);
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 0, v_a_3912_);
v___x_3914_ = v___x_3910_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3912_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
else
{
lean_object* v_a_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
lean_del_object(v___x_3910_);
v_a_3916_ = lean_ctor_get(v_a_3908_, 0);
lean_inc(v_a_3916_);
lean_dec_ref_known(v_a_3908_, 1);
v___x_3917_ = lean_unsigned_to_nat(1u);
v___x_3918_ = lean_nat_add(v_a_3892_, v___x_3917_);
lean_dec(v_a_3892_);
v_a_3892_ = v___x_3918_;
v_b_3893_ = v_a_3916_;
goto _start;
}
}
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
lean_dec(v_a_3892_);
lean_dec_ref(v_config_3891_);
v_a_3921_ = lean_ctor_get(v___y_3907_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___y_3907_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___y_3907_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___y_3907_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_4008_ = _args[0];
lean_object* v___x_4009_ = _args[1];
lean_object* v_config_4010_ = _args[2];
lean_object* v_a_4011_ = _args[3];
lean_object* v_b_4012_ = _args[4];
lean_object* v___y_4013_ = _args[5];
lean_object* v___y_4014_ = _args[6];
lean_object* v___y_4015_ = _args[7];
lean_object* v___y_4016_ = _args[8];
lean_object* v___y_4017_ = _args[9];
lean_object* v___y_4018_ = _args[10];
lean_object* v___y_4019_ = _args[11];
lean_object* v___y_4020_ = _args[12];
lean_object* v___y_4021_ = _args[13];
lean_object* v___y_4022_ = _args[14];
lean_object* v___y_4023_ = _args[15];
lean_object* v___y_4024_ = _args[16];
_start:
{
lean_object* v_res_4025_; 
v_res_4025_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_upperBound_4008_, v___x_4009_, v_config_4010_, v_a_4011_, v_b_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec_ref(v___x_4009_);
lean_dec(v_upperBound_4008_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(lean_object* v_config_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v___x_4039_; lean_object* v_hypotheses_4040_; lean_object* v___x_4041_; lean_object* v_newHyps_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4039_ = lean_st_ref_get(v___y_4028_);
v_hypotheses_4040_ = lean_ctor_get(v___x_4039_, 3);
lean_inc_ref(v_hypotheses_4040_);
lean_dec(v___x_4039_);
v___x_4041_ = lean_array_get_size(v_hypotheses_4040_);
v_newHyps_4042_ = lean_mk_empty_array_with_capacity(v___x_4041_);
v___x_4043_ = lean_unsigned_to_nat(0u);
v___x_4044_ = lean_box(0);
v___x_4045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4044_);
lean_ctor_set(v___x_4045_, 1, v_newHyps_4042_);
v___x_4046_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v___x_4041_, v_hypotheses_4040_, v_config_4026_, v___x_4043_, v___x_4045_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
lean_dec_ref(v_hypotheses_4040_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4076_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4076_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4049_ = v___x_4046_;
v_isShared_4050_ = v_isSharedCheck_4076_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4046_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4076_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v_fst_4051_; 
v_fst_4051_ = lean_ctor_get(v_a_4047_, 0);
if (lean_obj_tag(v_fst_4051_) == 0)
{
lean_object* v_snd_4052_; lean_object* v___x_4053_; lean_object* v_caches_4054_; lean_object* v_typeAnalysis_4055_; lean_object* v_target_4056_; uint8_t v_didChange_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4070_; 
v_snd_4052_ = lean_ctor_get(v_a_4047_, 1);
lean_inc(v_snd_4052_);
lean_dec(v_a_4047_);
v___x_4053_ = lean_st_ref_take(v___y_4028_);
v_caches_4054_ = lean_ctor_get(v___x_4053_, 0);
v_typeAnalysis_4055_ = lean_ctor_get(v___x_4053_, 1);
v_target_4056_ = lean_ctor_get(v___x_4053_, 2);
v_didChange_4057_ = lean_ctor_get_uint8(v___x_4053_, sizeof(void*)*4);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4070_ == 0)
{
lean_object* v_unused_4071_; 
v_unused_4071_ = lean_ctor_get(v___x_4053_, 3);
lean_dec(v_unused_4071_);
v___x_4059_ = v___x_4053_;
v_isShared_4060_ = v_isSharedCheck_4070_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_target_4056_);
lean_inc(v_typeAnalysis_4055_);
lean_inc(v_caches_4054_);
lean_dec(v___x_4053_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4070_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
lean_ctor_set(v___x_4059_, 3, v_snd_4052_);
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_caches_4054_);
lean_ctor_set(v_reuseFailAlloc_4069_, 1, v_typeAnalysis_4055_);
lean_ctor_set(v_reuseFailAlloc_4069_, 2, v_target_4056_);
lean_ctor_set(v_reuseFailAlloc_4069_, 3, v_snd_4052_);
lean_ctor_set_uint8(v_reuseFailAlloc_4069_, sizeof(void*)*4, v_didChange_4057_);
v___x_4062_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
lean_object* v___x_4063_; uint8_t v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4067_; 
v___x_4063_ = lean_st_ref_put(v___y_4028_, v___x_4062_);
v___x_4064_ = 0;
v___x_4065_ = lean_box(v___x_4064_);
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 0, v___x_4065_);
v___x_4067_ = v___x_4049_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v___x_4065_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
}
else
{
lean_object* v_val_4072_; lean_object* v___x_4074_; 
lean_inc_ref(v_fst_4051_);
lean_dec(v_a_4047_);
v_val_4072_ = lean_ctor_get(v_fst_4051_, 0);
lean_inc(v_val_4072_);
lean_dec_ref_known(v_fst_4051_, 1);
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 0, v_val_4072_);
v___x_4074_ = v___x_4049_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_val_4072_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
}
}
else
{
lean_object* v_a_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4084_; 
v_a_4077_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4084_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4084_ == 0)
{
v___x_4079_ = v___x_4046_;
v_isShared_4080_ = v_isSharedCheck_4084_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_a_4077_);
lean_dec(v___x_4046_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed(lean_object* v_config_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_){
_start:
{
lean_object* v_res_4098_; 
v_res_4098_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(v_config_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec(v___y_4088_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
return v_res_4098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v_config_4111_; lean_object* v___x_4112_; lean_object* v_maxSteps_4113_; lean_object* v_target_4114_; lean_object* v___x_4115_; lean_object* v_config_4116_; lean_object* v___f_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v_config_4111_ = lean_ctor_get(v___y_4099_, 0);
v___x_4112_ = lean_st_ref_get(v___y_4100_);
v_maxSteps_4113_ = lean_ctor_get(v_config_4111_, 1);
v_target_4114_ = lean_ctor_get(v___x_4112_, 2);
lean_inc_ref(v_target_4114_);
lean_dec(v___x_4112_);
v___x_4115_ = lean_unsigned_to_nat(2u);
lean_inc(v_maxSteps_4113_);
v_config_4116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_config_4116_, 0, v_maxSteps_4113_);
lean_ctor_set(v_config_4116_, 1, v___x_4115_);
v___f_4117_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed), 13, 1);
lean_closure_set(v___f_4117_, 0, v_config_4116_);
v___x_4118_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_4114_);
lean_dec_ref(v_target_4114_);
v___x_4119_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v___x_4118_, v___f_4117_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___boxed(lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(lean_object* v_cls_4141_, lean_object* v_msg_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v___x_4155_; 
v___x_4155_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_cls_4141_, v_msg_4142_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
return v___x_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___boxed(lean_object* v_cls_4156_, lean_object* v_msg_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(v_cls_4156_, v_msg_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec(v___y_4160_);
lean_dec(v___y_4159_);
lean_dec_ref(v___y_4158_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(lean_object* v_upperBound_4171_, lean_object* v___x_4172_, lean_object* v_config_4173_, lean_object* v_inst_4174_, lean_object* v_R_4175_, lean_object* v_a_4176_, lean_object* v_b_4177_, lean_object* v_c_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
lean_object* v___x_4191_; 
v___x_4191_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_upperBound_4171_, v___x_4172_, v_config_4173_, v_a_4176_, v_b_4177_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_4192_ = _args[0];
lean_object* v___x_4193_ = _args[1];
lean_object* v_config_4194_ = _args[2];
lean_object* v_inst_4195_ = _args[3];
lean_object* v_R_4196_ = _args[4];
lean_object* v_a_4197_ = _args[5];
lean_object* v_b_4198_ = _args[6];
lean_object* v_c_4199_ = _args[7];
lean_object* v___y_4200_ = _args[8];
lean_object* v___y_4201_ = _args[9];
lean_object* v___y_4202_ = _args[10];
lean_object* v___y_4203_ = _args[11];
lean_object* v___y_4204_ = _args[12];
lean_object* v___y_4205_ = _args[13];
lean_object* v___y_4206_ = _args[14];
lean_object* v___y_4207_ = _args[15];
lean_object* v___y_4208_ = _args[16];
lean_object* v___y_4209_ = _args[17];
lean_object* v___y_4210_ = _args[18];
lean_object* v___y_4211_ = _args[19];
_start:
{
lean_object* v_res_4212_; 
v_res_4212_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(v_upperBound_4192_, v___x_4193_, v_config_4194_, v_inst_4195_, v_R_4196_, v_a_4197_, v_b_4198_, v_c_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4207_);
lean_dec(v___y_4206_);
lean_dec_ref(v___y_4205_);
lean_dec(v___y_4204_);
lean_dec_ref(v___y_4203_);
lean_dec(v___y_4202_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec_ref(v___x_4193_);
lean_dec(v_upperBound_4192_);
return v_res_4212_;
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
