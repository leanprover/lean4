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
lean_object* v___x_490_; lean_object* v_env_491_; lean_object* v___x_492_; lean_object* v_toCold_493_; lean_object* v_mctx_494_; lean_object* v_lctx_495_; lean_object* v_options_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_490_ = lean_st_ref_get(v___y_488_);
v_env_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc_ref(v_env_491_);
lean_dec(v___x_490_);
v___x_492_ = lean_st_ref_get(v___y_486_);
v_toCold_493_ = lean_ctor_get(v___y_487_, 0);
v_mctx_494_ = lean_ctor_get(v___x_492_, 0);
lean_inc_ref(v_mctx_494_);
lean_dec(v___x_492_);
v_lctx_495_ = lean_ctor_get(v___y_485_, 2);
v_options_496_ = lean_ctor_get(v_toCold_493_, 2);
lean_inc_ref(v_options_496_);
lean_inc_ref(v_lctx_495_);
v___x_497_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_497_, 0, v_env_491_);
lean_ctor_set(v___x_497_, 1, v_mctx_494_);
lean_ctor_set(v___x_497_, 2, v_lctx_495_);
lean_ctor_set(v___x_497_, 3, v_options_496_);
v___x_498_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v_msgData_484_);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1___boxed(lean_object* v_msgData_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msgData_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(lean_object* v_msg_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_ref_513_; lean_object* v___x_514_; lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_523_; 
v_ref_513_ = lean_ctor_get(v___y_510_, 2);
v___x_514_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_523_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
lean_inc(v_ref_513_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v_ref_513_);
lean_ctor_set(v___x_519_, 1, v_a_515_);
if (v_isShared_518_ == 0)
{
lean_ctor_set_tag(v___x_517_, 1);
lean_ctor_set(v___x_517_, 0, v___x_519_);
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg___boxed(lean_object* v_msg_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__0(lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
if (lean_obj_tag(v_a_531_) == 0)
{
lean_object* v___x_533_; 
v___x_533_ = l_List_reverse___redArg(v_a_532_);
return v___x_533_;
}
else
{
lean_object* v_head_534_; lean_object* v_tail_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_544_; 
v_head_534_ = lean_ctor_get(v_a_531_, 0);
v_tail_535_ = lean_ctor_get(v_a_531_, 1);
v_isSharedCheck_544_ = !lean_is_exclusive(v_a_531_);
if (v_isSharedCheck_544_ == 0)
{
v___x_537_ = v_a_531_;
v_isShared_538_ = v_isSharedCheck_544_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_tail_535_);
lean_inc(v_head_534_);
lean_dec(v_a_531_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_544_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_539_ = l_Lean_MessageData_ofExpr(v_head_534_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 1, v_a_532_);
lean_ctor_set(v___x_537_, 0, v___x_539_);
v___x_541_ = v___x_537_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_a_532_);
v___x_541_ = v_reuseFailAlloc_543_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
v_a_531_ = v_tail_535_;
v_a_532_ = v___x_541_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__0));
v___x_547_ = l_Lean_stringToMessageData(v___x_546_);
return v___x_547_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__2));
v___x_550_ = l_Lean_stringToMessageData(v___x_549_);
return v___x_550_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__4));
v___x_553_ = l_Lean_stringToMessageData(v___x_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(lean_object* v_idx_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_varToExpr_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v_varToExpr_563_ = lean_ctor_get(v_a_555_, 2);
v___x_564_ = lean_array_get_size(v_varToExpr_563_);
v___x_565_ = lean_nat_dec_lt(v_idx_554_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
lean_inc_ref(v_varToExpr_563_);
lean_dec_ref(v_a_555_);
v___x_566_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1);
v___x_567_ = l_Nat_reprFast(v_idx_554_);
v___x_568_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
v___x_569_ = l_Lean_MessageData_ofFormat(v___x_568_);
v___x_570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_566_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3);
v___x_572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = l_Nat_reprFast(v___x_564_);
v___x_574_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
v___x_575_ = l_Lean_MessageData_ofFormat(v___x_574_);
v___x_576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_572_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v___x_577_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5);
v___x_578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_576_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = lean_array_to_list(v_varToExpr_563_);
v___x_580_ = lean_box(0);
v___x_581_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__0(v___x_579_, v___x_580_);
v___x_582_ = l_Lean_MessageData_ofList(v___x_581_);
v___x_583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_578_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v___x_583_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
return v___x_584_;
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = lean_array_fget(v_varToExpr_563_, v_idx_554_);
lean_dec(v_idx_554_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v_a_555_);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___boxed(lean_object* v_idx_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(v_idx_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(lean_object* v_00_u03b1_598_, lean_object* v_msg_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_599_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___boxed(lean_object* v_00_u03b1_609_, lean_object* v_msg_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(v_00_u03b1_609_, v_msg_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec_ref(v___y_611_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(lean_object* v_c_620_){
_start:
{
lean_object* v___y_622_; 
if (lean_obj_tag(v_c_620_) == 0)
{
lean_object* v___x_626_; 
v___x_626_ = lean_unsigned_to_nat(0u);
v___y_622_ = v___x_626_;
goto v___jp_621_;
}
else
{
lean_object* v_val_627_; 
v_val_627_ = lean_ctor_get(v_c_620_, 0);
v___y_622_ = v_val_627_;
goto v___jp_621_;
}
v___jp_621_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = lean_unsigned_to_nat(1u);
v___x_624_ = lean_nat_add(v___y_622_, v___x_623_);
v___x_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0___boxed(lean_object* v_c_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v_c_628_);
lean_dec(v_c_628_);
return v_res_629_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_box(0);
v___x_631_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v___x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(lean_object* v_a_632_, lean_object* v_x_633_){
_start:
{
if (lean_obj_tag(v_x_633_) == 0)
{
lean_object* v___x_634_; lean_object* v_val_635_; lean_object* v___x_636_; 
v___x_634_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0, &l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0);
v_val_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_val_635_);
v___x_636_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_636_, 0, v_a_632_);
lean_ctor_set(v___x_636_, 1, v_val_635_);
lean_ctor_set(v___x_636_, 2, v_x_633_);
return v___x_636_;
}
else
{
lean_object* v_key_637_; lean_object* v_value_638_; lean_object* v_tail_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_654_; 
v_key_637_ = lean_ctor_get(v_x_633_, 0);
v_value_638_ = lean_ctor_get(v_x_633_, 1);
v_tail_639_ = lean_ctor_get(v_x_633_, 2);
v_isSharedCheck_654_ = !lean_is_exclusive(v_x_633_);
if (v_isSharedCheck_654_ == 0)
{
v___x_641_ = v_x_633_;
v_isShared_642_ = v_isSharedCheck_654_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_tail_639_);
lean_inc(v_value_638_);
lean_inc(v_key_637_);
lean_dec(v_x_633_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_654_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
uint8_t v___x_643_; 
v___x_643_ = lean_nat_dec_eq(v_key_637_, v_a_632_);
if (v___x_643_ == 0)
{
lean_object* v_tail_644_; lean_object* v___x_646_; 
v_tail_644_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(v_a_632_, v_tail_639_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 2, v_tail_644_);
v___x_646_ = v___x_641_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_key_637_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_value_638_);
lean_ctor_set(v_reuseFailAlloc_647_, 2, v_tail_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v_val_650_; lean_object* v___x_652_; 
lean_dec(v_key_637_);
v___x_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_648_, 0, v_value_638_);
v___x_649_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v___x_648_);
lean_dec_ref_known(v___x_648_, 1);
v_val_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_val_650_);
lean_dec(v___x_649_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v_val_650_);
lean_ctor_set(v___x_641_, 0, v_a_632_);
v___x_652_ = v___x_641_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_632_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_val_650_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v_tail_639_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
if (lean_obj_tag(v_x_656_) == 0)
{
return v_x_655_;
}
else
{
lean_object* v_key_657_; lean_object* v_value_658_; lean_object* v_tail_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_682_; 
v_key_657_ = lean_ctor_get(v_x_656_, 0);
v_value_658_ = lean_ctor_get(v_x_656_, 1);
v_tail_659_ = lean_ctor_get(v_x_656_, 2);
v_isSharedCheck_682_ = !lean_is_exclusive(v_x_656_);
if (v_isSharedCheck_682_ == 0)
{
v___x_661_ = v_x_656_;
v_isShared_662_ = v_isSharedCheck_682_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_tail_659_);
lean_inc(v_value_658_);
lean_inc(v_key_657_);
lean_dec(v_x_656_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_682_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; uint64_t v___x_664_; uint64_t v___x_665_; uint64_t v___x_666_; uint64_t v_fold_667_; uint64_t v___x_668_; uint64_t v___x_669_; uint64_t v___x_670_; size_t v___x_671_; size_t v___x_672_; size_t v___x_673_; size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_663_ = lean_array_get_size(v_x_655_);
v___x_664_ = lean_uint64_of_nat(v_key_657_);
v___x_665_ = 32ULL;
v___x_666_ = lean_uint64_shift_right(v___x_664_, v___x_665_);
v_fold_667_ = lean_uint64_xor(v___x_664_, v___x_666_);
v___x_668_ = 16ULL;
v___x_669_ = lean_uint64_shift_right(v_fold_667_, v___x_668_);
v___x_670_ = lean_uint64_xor(v_fold_667_, v___x_669_);
v___x_671_ = lean_uint64_to_usize(v___x_670_);
v___x_672_ = lean_usize_of_nat(v___x_663_);
v___x_673_ = ((size_t)1ULL);
v___x_674_ = lean_usize_sub(v___x_672_, v___x_673_);
v___x_675_ = lean_usize_land(v___x_671_, v___x_674_);
v___x_676_ = lean_array_uget_borrowed(v_x_655_, v___x_675_);
lean_inc(v___x_676_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 2, v___x_676_);
v___x_678_ = v___x_661_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_key_657_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_value_658_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v___x_676_);
v___x_678_ = v_reuseFailAlloc_681_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; 
v___x_679_ = lean_array_uset(v_x_655_, v___x_675_, v___x_678_);
v_x_655_ = v___x_679_;
v_x_656_ = v_tail_659_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(lean_object* v_i_683_, lean_object* v_source_684_, lean_object* v_target_685_){
_start:
{
lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = lean_array_get_size(v_source_684_);
v___x_687_ = lean_nat_dec_lt(v_i_683_, v___x_686_);
if (v___x_687_ == 0)
{
lean_dec_ref(v_source_684_);
lean_dec(v_i_683_);
return v_target_685_;
}
else
{
lean_object* v_es_688_; lean_object* v___x_689_; lean_object* v_source_690_; lean_object* v_target_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_es_688_ = lean_array_fget(v_source_684_, v_i_683_);
v___x_689_ = lean_box(0);
v_source_690_ = lean_array_fset(v_source_684_, v_i_683_, v___x_689_);
v_target_691_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(v_target_685_, v_es_688_);
v___x_692_ = lean_unsigned_to_nat(1u);
v___x_693_ = lean_nat_add(v_i_683_, v___x_692_);
lean_dec(v_i_683_);
v_i_683_ = v___x_693_;
v_source_684_ = v_source_690_;
v_target_685_ = v_target_691_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(lean_object* v_data_695_){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v_nbuckets_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_696_ = lean_array_get_size(v_data_695_);
v___x_697_ = lean_unsigned_to_nat(2u);
v_nbuckets_698_ = lean_nat_mul(v___x_696_, v___x_697_);
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = lean_box(0);
v___x_701_ = lean_mk_array(v_nbuckets_698_, v___x_700_);
v___x_702_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(v___x_699_, v_data_695_, v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(lean_object* v_a_703_, lean_object* v_x_704_){
_start:
{
if (lean_obj_tag(v_x_704_) == 0)
{
uint8_t v___x_705_; 
v___x_705_ = 0;
return v___x_705_;
}
else
{
lean_object* v_key_706_; lean_object* v_tail_707_; uint8_t v___x_708_; 
v_key_706_ = lean_ctor_get(v_x_704_, 0);
v_tail_707_ = lean_ctor_get(v_x_704_, 2);
v___x_708_ = lean_nat_dec_eq(v_key_706_, v_a_703_);
if (v___x_708_ == 0)
{
v_x_704_ = v_tail_707_;
goto _start;
}
else
{
return v___x_708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_710_, lean_object* v_x_711_){
_start:
{
uint8_t v_res_712_; lean_object* v_r_713_; 
v_res_712_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_710_, v_x_711_);
lean_dec(v_x_711_);
lean_dec(v_a_710_);
v_r_713_ = lean_box(v_res_712_);
return v_r_713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(lean_object* v_m_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_size_716_; lean_object* v_buckets_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_765_; 
v_size_716_ = lean_ctor_get(v_m_714_, 0);
v_buckets_717_ = lean_ctor_get(v_m_714_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v_m_714_);
if (v_isSharedCheck_765_ == 0)
{
v___x_719_ = v_m_714_;
v_isShared_720_ = v_isSharedCheck_765_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_buckets_717_);
lean_inc(v_size_716_);
lean_dec(v_m_714_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_765_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; uint64_t v___x_722_; uint64_t v___x_723_; uint64_t v___x_724_; uint64_t v_fold_725_; uint64_t v___x_726_; uint64_t v___x_727_; uint64_t v___x_728_; size_t v___x_729_; size_t v___x_730_; size_t v___x_731_; size_t v___x_732_; size_t v___x_733_; lean_object* v_bkt_734_; uint8_t v___x_735_; 
v___x_721_ = lean_array_get_size(v_buckets_717_);
v___x_722_ = lean_uint64_of_nat(v_a_715_);
v___x_723_ = 32ULL;
v___x_724_ = lean_uint64_shift_right(v___x_722_, v___x_723_);
v_fold_725_ = lean_uint64_xor(v___x_722_, v___x_724_);
v___x_726_ = 16ULL;
v___x_727_ = lean_uint64_shift_right(v_fold_725_, v___x_726_);
v___x_728_ = lean_uint64_xor(v_fold_725_, v___x_727_);
v___x_729_ = lean_uint64_to_usize(v___x_728_);
v___x_730_ = lean_usize_of_nat(v___x_721_);
v___x_731_ = ((size_t)1ULL);
v___x_732_ = lean_usize_sub(v___x_730_, v___x_731_);
v___x_733_ = lean_usize_land(v___x_729_, v___x_732_);
v_bkt_734_ = lean_array_uget_borrowed(v_buckets_717_, v___x_733_);
v___x_735_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_715_, v_bkt_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v_size_x27_737_; lean_object* v___x_738_; lean_object* v_buckets_x27_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_736_ = lean_unsigned_to_nat(1u);
v_size_x27_737_ = lean_nat_add(v_size_716_, v___x_736_);
lean_dec(v_size_716_);
lean_inc(v_bkt_734_);
v___x_738_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_738_, 0, v_a_715_);
lean_ctor_set(v___x_738_, 1, v___x_736_);
lean_ctor_set(v___x_738_, 2, v_bkt_734_);
v_buckets_x27_739_ = lean_array_uset(v_buckets_717_, v___x_733_, v___x_738_);
v___x_740_ = lean_unsigned_to_nat(4u);
v___x_741_ = lean_nat_mul(v_size_x27_737_, v___x_740_);
v___x_742_ = lean_unsigned_to_nat(3u);
v___x_743_ = lean_nat_div(v___x_741_, v___x_742_);
lean_dec(v___x_741_);
v___x_744_ = lean_array_get_size(v_buckets_x27_739_);
v___x_745_ = lean_nat_dec_le(v___x_743_, v___x_744_);
lean_dec(v___x_743_);
if (v___x_745_ == 0)
{
lean_object* v_val_746_; lean_object* v___x_748_; 
v_val_746_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_739_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 1, v_val_746_);
lean_ctor_set(v___x_719_, 0, v_size_x27_737_);
v___x_748_ = v___x_719_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_size_x27_737_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_val_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
else
{
lean_object* v___x_751_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 1, v_buckets_x27_739_);
lean_ctor_set(v___x_719_, 0, v_size_x27_737_);
v___x_751_ = v___x_719_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_size_x27_737_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_buckets_x27_739_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
else
{
lean_object* v___x_753_; lean_object* v_buckets_x27_754_; lean_object* v_bkt_x27_755_; lean_object* v___y_757_; uint8_t v___x_762_; 
lean_inc(v_bkt_734_);
v___x_753_ = lean_box(0);
v_buckets_x27_754_ = lean_array_uset(v_buckets_717_, v___x_733_, v___x_753_);
lean_inc(v_a_715_);
v_bkt_x27_755_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(v_a_715_, v_bkt_734_);
v___x_762_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_715_, v_bkt_x27_755_);
lean_dec(v_a_715_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_nat_sub(v_size_716_, v___x_763_);
lean_dec(v_size_716_);
v___y_757_ = v___x_764_;
goto v___jp_756_;
}
else
{
v___y_757_ = v_size_716_;
goto v___jp_756_;
}
v___jp_756_:
{
lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_758_ = lean_array_uset(v_buckets_x27_754_, v___x_733_, v_bkt_x27_755_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 1, v___x_758_);
lean_ctor_set(v___x_719_, 0, v___y_757_);
v___x_760_ = v___x_719_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___y_757_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(lean_object* v_coeff_766_, lean_object* v_e_767_, lean_object* v_a_768_){
_start:
{
lean_object* v___x_770_; lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_788_; 
v___x_770_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_767_, v_a_768_);
v_a_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_788_ == 0)
{
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_788_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_788_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_fst_775_; lean_object* v_snd_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_787_; 
v_fst_775_ = lean_ctor_get(v_a_771_, 0);
v_snd_776_ = lean_ctor_get(v_a_771_, 1);
v_isSharedCheck_787_ = !lean_is_exclusive(v_a_771_);
if (v_isSharedCheck_787_ == 0)
{
v___x_778_ = v_a_771_;
v_isShared_779_ = v_isSharedCheck_787_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_snd_776_);
lean_inc(v_fst_775_);
lean_dec(v_a_771_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_787_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_780_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(v_coeff_766_, v_fst_775_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_780_);
v___x_782_ = v___x_778_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_snd_776_);
v___x_782_ = v_reuseFailAlloc_786_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_784_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_782_);
v___x_784_ = v___x_773_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___boxed(lean_object* v_coeff_789_, lean_object* v_e_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_789_, v_e_790_, v_a_791_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(lean_object* v_coeff_794_, lean_object* v_e_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_794_, v_e_795_, v_a_796_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___boxed(lean_object* v_coeff_805_, lean_object* v_e_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(v_coeff_805_, v_e_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
return v_res_815_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(lean_object* v_00_u03b2_816_, lean_object* v_a_817_, lean_object* v_x_818_){
_start:
{
uint8_t v___x_819_; 
v___x_819_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_817_, v_x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_820_, lean_object* v_a_821_, lean_object* v_x_822_){
_start:
{
uint8_t v_res_823_; lean_object* v_r_824_; 
v_res_823_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(v_00_u03b2_820_, v_a_821_, v_x_822_);
lean_dec(v_x_822_);
lean_dec(v_a_821_);
v_r_824_ = lean_box(v_res_823_);
return v_r_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1(lean_object* v_00_u03b2_825_, lean_object* v_data_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_data_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_828_, lean_object* v_i_829_, lean_object* v_source_830_, lean_object* v_target_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(v_i_829_, v_source_830_, v_target_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_833_, lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_834_, v_x_835_);
return v___x_836_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_837_; double v___x_838_; 
v___x_837_ = lean_unsigned_to_nat(0u);
v___x_838_ = lean_float_of_nat(v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(lean_object* v_cls_842_, lean_object* v_msg_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_ref_850_; lean_object* v___x_851_; lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_897_; 
v_ref_850_ = lean_ctor_get(v___y_847_, 2);
v___x_851_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_843_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_897_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_897_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_897_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v_traceState_857_; lean_object* v_env_858_; lean_object* v_nextMacroScope_859_; lean_object* v_ngen_860_; lean_object* v_auxDeclNGen_861_; lean_object* v_cache_862_; lean_object* v_messages_863_; lean_object* v_infoState_864_; lean_object* v_snapshotTasks_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_896_; 
v___x_856_ = lean_st_ref_take(v___y_848_);
v_traceState_857_ = lean_ctor_get(v___x_856_, 4);
v_env_858_ = lean_ctor_get(v___x_856_, 0);
v_nextMacroScope_859_ = lean_ctor_get(v___x_856_, 1);
v_ngen_860_ = lean_ctor_get(v___x_856_, 2);
v_auxDeclNGen_861_ = lean_ctor_get(v___x_856_, 3);
v_cache_862_ = lean_ctor_get(v___x_856_, 5);
v_messages_863_ = lean_ctor_get(v___x_856_, 6);
v_infoState_864_ = lean_ctor_get(v___x_856_, 7);
v_snapshotTasks_865_ = lean_ctor_get(v___x_856_, 8);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_896_ == 0)
{
v___x_867_ = v___x_856_;
v_isShared_868_ = v_isSharedCheck_896_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_snapshotTasks_865_);
lean_inc(v_infoState_864_);
lean_inc(v_messages_863_);
lean_inc(v_cache_862_);
lean_inc(v_traceState_857_);
lean_inc(v_auxDeclNGen_861_);
lean_inc(v_ngen_860_);
lean_inc(v_nextMacroScope_859_);
lean_inc(v_env_858_);
lean_dec(v___x_856_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_896_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
uint64_t v_tid_869_; lean_object* v_traces_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_895_; 
v_tid_869_ = lean_ctor_get_uint64(v_traceState_857_, sizeof(void*)*1);
v_traces_870_ = lean_ctor_get(v_traceState_857_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v_traceState_857_);
if (v_isSharedCheck_895_ == 0)
{
v___x_872_ = v_traceState_857_;
v_isShared_873_ = v_isSharedCheck_895_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_traces_870_);
lean_dec(v_traceState_857_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_895_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; double v___x_875_; uint8_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_874_ = lean_box(0);
v___x_875_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_876_ = 0;
v___x_877_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_878_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_878_, 0, v_cls_842_);
lean_ctor_set(v___x_878_, 1, v___x_874_);
lean_ctor_set(v___x_878_, 2, v___x_877_);
lean_ctor_set_float(v___x_878_, sizeof(void*)*3, v___x_875_);
lean_ctor_set_float(v___x_878_, sizeof(void*)*3 + 8, v___x_875_);
lean_ctor_set_uint8(v___x_878_, sizeof(void*)*3 + 16, v___x_876_);
v___x_879_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_880_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_880_, 0, v___x_878_);
lean_ctor_set(v___x_880_, 1, v_a_852_);
lean_ctor_set(v___x_880_, 2, v___x_879_);
lean_inc(v_ref_850_);
v___x_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_881_, 0, v_ref_850_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = l_Lean_PersistentArray_push___redArg(v_traces_870_, v___x_881_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_882_);
v___x_884_ = v___x_872_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_882_);
lean_ctor_set_uint64(v_reuseFailAlloc_894_, sizeof(void*)*1, v_tid_869_);
v___x_884_ = v_reuseFailAlloc_894_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 4, v___x_884_);
v___x_886_ = v___x_867_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_env_858_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_nextMacroScope_859_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v_ngen_860_);
lean_ctor_set(v_reuseFailAlloc_893_, 3, v_auxDeclNGen_861_);
lean_ctor_set(v_reuseFailAlloc_893_, 4, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_893_, 5, v_cache_862_);
lean_ctor_set(v_reuseFailAlloc_893_, 6, v_messages_863_);
lean_ctor_set(v_reuseFailAlloc_893_, 7, v_infoState_864_);
lean_ctor_set(v_reuseFailAlloc_893_, 8, v_snapshotTasks_865_);
v___x_886_ = v_reuseFailAlloc_893_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_887_ = lean_st_ref_put(v___y_848_, v___x_886_);
v___x_888_ = lean_box(0);
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___y_844_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_889_);
v___x_891_ = v___x_854_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___boxed(lean_object* v_cls_898_, lean_object* v_msg_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_898_, v_msg_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_906_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6(void){
_start:
{
lean_object* v_cls_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v_cls_917_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_918_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_919_ = l_Lean_Name_append(v___x_918_, v_cls_917_);
return v___x_919_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__7));
v___x_922_ = l_Lean_stringToMessageData(v___x_921_);
return v___x_922_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__9));
v___x_925_ = l_Lean_stringToMessageData(v___x_924_);
return v___x_925_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__11));
v___x_928_ = l_Lean_stringToMessageData(v___x_927_);
return v___x_928_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__13));
v___x_931_ = l_Lean_stringToMessageData(v___x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(lean_object* v_op_932_, lean_object* v_coeff_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
if (lean_obj_tag(v_a_934_) == 5)
{
lean_object* v_fn_943_; 
v_fn_943_ = lean_ctor_get(v_a_934_, 0);
if (lean_obj_tag(v_fn_943_) == 5)
{
lean_object* v_arg_944_; lean_object* v_fn_945_; lean_object* v_arg_946_; uint8_t v___x_947_; 
v_arg_944_ = lean_ctor_get(v_a_934_, 1);
v_fn_945_ = lean_ctor_get(v_fn_943_, 0);
v_arg_946_ = lean_ctor_get(v_fn_943_, 1);
lean_inc_ref(v_fn_945_);
v___x_947_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(v_fn_945_);
if (v___x_947_ == 0)
{
lean_object* v_toCold_948_; lean_object* v_options_949_; uint8_t v_hasTrace_950_; 
v_toCold_948_ = lean_ctor_get(v_a_940_, 0);
v_options_949_ = lean_ctor_get(v_toCold_948_, 2);
v_hasTrace_950_ = lean_ctor_get_uint8(v_options_949_, sizeof(void*)*1);
if (v_hasTrace_950_ == 0)
{
lean_object* v___x_951_; 
lean_dec_ref(v_op_932_);
v___x_951_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_933_, v_a_934_, v_a_935_);
return v___x_951_;
}
else
{
lean_object* v_inheritedTraceOptions_952_; lean_object* v_cls_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
v_inheritedTraceOptions_952_ = lean_ctor_get(v_toCold_948_, 11);
v_cls_953_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_954_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_955_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_952_, v_options_949_, v___x_954_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
lean_dec_ref(v_op_932_);
v___x_956_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_933_, v_a_934_, v_a_935_);
return v___x_956_;
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_957_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8);
lean_inc_ref(v_fn_945_);
v___x_958_ = l_Lean_MessageData_ofExpr(v_fn_945_);
v___x_959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10);
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
lean_inc_ref(v_arg_946_);
v___x_962_ = l_Lean_MessageData_ofExpr(v_arg_946_);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_961_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v___x_960_);
lean_inc_ref(v_arg_944_);
v___x_965_ = l_Lean_MessageData_ofExpr(v_arg_944_);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_932_);
v___x_970_ = l_Lean_MessageData_ofExpr(v___x_969_);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_968_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14);
v___x_973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_971_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_953_, v___x_973_, v_a_935_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v_snd_976_; lean_object* v___x_977_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_975_);
lean_dec_ref_known(v___x_974_, 1);
v_snd_976_ = lean_ctor_get(v_a_975_, 1);
lean_inc(v_snd_976_);
lean_dec(v_a_975_);
v___x_977_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_933_, v_a_934_, v_snd_976_);
return v___x_977_;
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec_ref_known(v_a_934_, 2);
lean_dec_ref(v_coeff_933_);
v_a_978_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_974_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_974_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
}
else
{
lean_object* v___x_986_; 
lean_inc_ref(v_arg_946_);
lean_inc_ref(v_arg_944_);
lean_dec_ref_known(v_a_934_, 2);
lean_inc_ref(v_op_932_);
v___x_986_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_932_, v_coeff_933_, v_arg_946_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v_fst_988_; lean_object* v_snd_989_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_986_, 1);
v_fst_988_ = lean_ctor_get(v_a_987_, 0);
lean_inc(v_fst_988_);
v_snd_989_ = lean_ctor_get(v_a_987_, 1);
lean_inc(v_snd_989_);
lean_dec(v_a_987_);
v_coeff_933_ = v_fst_988_;
v_a_934_ = v_arg_944_;
v_a_935_ = v_snd_989_;
goto _start;
}
else
{
lean_dec_ref(v_arg_944_);
lean_dec_ref(v_op_932_);
return v___x_986_;
}
}
}
else
{
lean_object* v___x_991_; 
lean_dec_ref(v_op_932_);
v___x_991_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_933_, v_a_934_, v_a_935_);
return v___x_991_;
}
}
else
{
lean_object* v___x_992_; 
lean_dec_ref(v_op_932_);
v___x_992_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_933_, v_a_934_, v_a_935_);
return v___x_992_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___boxed(lean_object* v_op_993_, lean_object* v_coeff_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_993_, v_coeff_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
lean_dec(v_a_1002_);
lean_dec_ref(v_a_1001_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(lean_object* v_cls_1005_, lean_object* v_msg_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_1005_, v_msg_1006_, v___y_1007_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___boxed(lean_object* v_cls_1016_, lean_object* v_msg_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(v_cls_1016_, v_msg_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
return v_res_1026_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = lean_box(0);
v___x_1028_ = lean_unsigned_to_nat(16u);
v___x_1029_ = lean_mk_array(v___x_1028_, v___x_1027_);
return v___x_1029_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1030_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1031_ = lean_unsigned_to_nat(0u);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set(v___x_1032_, 1, v___x_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(lean_object* v_op_1033_, lean_object* v_e_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1044_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_1033_, v___x_1043_, v_e_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___boxed(lean_object* v_op_1045_, lean_object* v_e_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_op_1045_, v_e_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(lean_object* v_a_1056_, lean_object* v_x_1057_){
_start:
{
if (lean_obj_tag(v_x_1057_) == 0)
{
lean_object* v___x_1058_; 
v___x_1058_ = lean_box(0);
return v___x_1058_;
}
else
{
lean_object* v_key_1059_; lean_object* v_value_1060_; lean_object* v_tail_1061_; uint8_t v___x_1062_; 
v_key_1059_ = lean_ctor_get(v_x_1057_, 0);
v_value_1060_ = lean_ctor_get(v_x_1057_, 1);
v_tail_1061_ = lean_ctor_get(v_x_1057_, 2);
v___x_1062_ = lean_nat_dec_eq(v_key_1059_, v_a_1056_);
if (v___x_1062_ == 0)
{
v_x_1057_ = v_tail_1061_;
goto _start;
}
else
{
lean_object* v___x_1064_; 
lean_inc(v_value_1060_);
v___x_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1064_, 0, v_value_1060_);
return v___x_1064_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg___boxed(lean_object* v_a_1065_, lean_object* v_x_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1065_, v_x_1066_);
lean_dec(v_x_1066_);
lean_dec(v_a_1065_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(lean_object* v_m_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v_buckets_1070_; lean_object* v___x_1071_; uint64_t v___x_1072_; uint64_t v___x_1073_; uint64_t v___x_1074_; uint64_t v_fold_1075_; uint64_t v___x_1076_; uint64_t v___x_1077_; uint64_t v___x_1078_; size_t v___x_1079_; size_t v___x_1080_; size_t v___x_1081_; size_t v___x_1082_; size_t v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v_buckets_1070_ = lean_ctor_get(v_m_1068_, 1);
v___x_1071_ = lean_array_get_size(v_buckets_1070_);
v___x_1072_ = lean_uint64_of_nat(v_a_1069_);
v___x_1073_ = 32ULL;
v___x_1074_ = lean_uint64_shift_right(v___x_1072_, v___x_1073_);
v_fold_1075_ = lean_uint64_xor(v___x_1072_, v___x_1074_);
v___x_1076_ = 16ULL;
v___x_1077_ = lean_uint64_shift_right(v_fold_1075_, v___x_1076_);
v___x_1078_ = lean_uint64_xor(v_fold_1075_, v___x_1077_);
v___x_1079_ = lean_uint64_to_usize(v___x_1078_);
v___x_1080_ = lean_usize_of_nat(v___x_1071_);
v___x_1081_ = ((size_t)1ULL);
v___x_1082_ = lean_usize_sub(v___x_1080_, v___x_1081_);
v___x_1083_ = lean_usize_land(v___x_1079_, v___x_1082_);
v___x_1084_ = lean_array_uget_borrowed(v_buckets_1070_, v___x_1083_);
v___x_1085_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1069_, v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg___boxed(lean_object* v_m_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1086_, v_a_1087_);
lean_dec(v_a_1087_);
lean_dec_ref(v_m_1086_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(lean_object* v_a_1089_, lean_object* v_b_1090_, lean_object* v_x_1091_){
_start:
{
if (lean_obj_tag(v_x_1091_) == 0)
{
lean_dec(v_b_1090_);
lean_dec(v_a_1089_);
return v_x_1091_;
}
else
{
lean_object* v_key_1092_; lean_object* v_value_1093_; lean_object* v_tail_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1106_; 
v_key_1092_ = lean_ctor_get(v_x_1091_, 0);
v_value_1093_ = lean_ctor_get(v_x_1091_, 1);
v_tail_1094_ = lean_ctor_get(v_x_1091_, 2);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_x_1091_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1096_ = v_x_1091_;
v_isShared_1097_ = v_isSharedCheck_1106_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_tail_1094_);
lean_inc(v_value_1093_);
lean_inc(v_key_1092_);
lean_dec(v_x_1091_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1106_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
uint8_t v___x_1098_; 
v___x_1098_ = lean_nat_dec_eq(v_key_1092_, v_a_1089_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1099_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1089_, v_b_1090_, v_tail_1094_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 2, v___x_1099_);
v___x_1101_ = v___x_1096_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_key_1092_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_value_1093_);
lean_ctor_set(v_reuseFailAlloc_1102_, 2, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
else
{
lean_object* v___x_1104_; 
lean_dec(v_value_1093_);
lean_dec(v_key_1092_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 1, v_b_1090_);
lean_ctor_set(v___x_1096_, 0, v_a_1089_);
v___x_1104_ = v___x_1096_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1089_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_b_1090_);
lean_ctor_set(v_reuseFailAlloc_1105_, 2, v_tail_1094_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(lean_object* v_m_1107_, lean_object* v_a_1108_, lean_object* v_b_1109_){
_start:
{
lean_object* v_size_1110_; lean_object* v_buckets_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1154_; 
v_size_1110_ = lean_ctor_get(v_m_1107_, 0);
v_buckets_1111_ = lean_ctor_get(v_m_1107_, 1);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_m_1107_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1113_ = v_m_1107_;
v_isShared_1114_ = v_isSharedCheck_1154_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_buckets_1111_);
lean_inc(v_size_1110_);
lean_dec(v_m_1107_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1154_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; uint64_t v___x_1116_; uint64_t v___x_1117_; uint64_t v___x_1118_; uint64_t v_fold_1119_; uint64_t v___x_1120_; uint64_t v___x_1121_; uint64_t v___x_1122_; size_t v___x_1123_; size_t v___x_1124_; size_t v___x_1125_; size_t v___x_1126_; size_t v___x_1127_; lean_object* v_bkt_1128_; uint8_t v___x_1129_; 
v___x_1115_ = lean_array_get_size(v_buckets_1111_);
v___x_1116_ = lean_uint64_of_nat(v_a_1108_);
v___x_1117_ = 32ULL;
v___x_1118_ = lean_uint64_shift_right(v___x_1116_, v___x_1117_);
v_fold_1119_ = lean_uint64_xor(v___x_1116_, v___x_1118_);
v___x_1120_ = 16ULL;
v___x_1121_ = lean_uint64_shift_right(v_fold_1119_, v___x_1120_);
v___x_1122_ = lean_uint64_xor(v_fold_1119_, v___x_1121_);
v___x_1123_ = lean_uint64_to_usize(v___x_1122_);
v___x_1124_ = lean_usize_of_nat(v___x_1115_);
v___x_1125_ = ((size_t)1ULL);
v___x_1126_ = lean_usize_sub(v___x_1124_, v___x_1125_);
v___x_1127_ = lean_usize_land(v___x_1123_, v___x_1126_);
v_bkt_1128_ = lean_array_uget_borrowed(v_buckets_1111_, v___x_1127_);
v___x_1129_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1108_, v_bkt_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v_size_x27_1131_; lean_object* v___x_1132_; lean_object* v_buckets_x27_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1130_ = lean_unsigned_to_nat(1u);
v_size_x27_1131_ = lean_nat_add(v_size_1110_, v___x_1130_);
lean_dec(v_size_1110_);
lean_inc(v_bkt_1128_);
v___x_1132_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1132_, 0, v_a_1108_);
lean_ctor_set(v___x_1132_, 1, v_b_1109_);
lean_ctor_set(v___x_1132_, 2, v_bkt_1128_);
v_buckets_x27_1133_ = lean_array_uset(v_buckets_1111_, v___x_1127_, v___x_1132_);
v___x_1134_ = lean_unsigned_to_nat(4u);
v___x_1135_ = lean_nat_mul(v_size_x27_1131_, v___x_1134_);
v___x_1136_ = lean_unsigned_to_nat(3u);
v___x_1137_ = lean_nat_div(v___x_1135_, v___x_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_array_get_size(v_buckets_x27_1133_);
v___x_1139_ = lean_nat_dec_le(v___x_1137_, v___x_1138_);
lean_dec(v___x_1137_);
if (v___x_1139_ == 0)
{
lean_object* v_val_1140_; lean_object* v___x_1142_; 
v_val_1140_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_1133_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 1, v_val_1140_);
lean_ctor_set(v___x_1113_, 0, v_size_x27_1131_);
v___x_1142_ = v___x_1113_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_size_x27_1131_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_val_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
else
{
lean_object* v___x_1145_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 1, v_buckets_x27_1133_);
lean_ctor_set(v___x_1113_, 0, v_size_x27_1131_);
v___x_1145_ = v___x_1113_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_size_x27_1131_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_buckets_x27_1133_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
else
{
lean_object* v___x_1147_; lean_object* v_buckets_x27_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
lean_inc(v_bkt_1128_);
v___x_1147_ = lean_box(0);
v_buckets_x27_1148_ = lean_array_uset(v_buckets_1111_, v___x_1127_, v___x_1147_);
v___x_1149_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1108_, v_b_1109_, v_bkt_1128_);
v___x_1150_ = lean_array_uset(v_buckets_x27_1148_, v___x_1127_, v___x_1149_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 1, v___x_1150_);
v___x_1152_ = v___x_1113_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_size_1110_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(lean_object* v_snd_1155_, lean_object* v_x_1156_, lean_object* v_x_1157_){
_start:
{
if (lean_obj_tag(v_x_1157_) == 0)
{
return v_x_1156_;
}
else
{
lean_object* v_key_1158_; lean_object* v_value_1159_; lean_object* v_tail_1160_; lean_object* v___y_1162_; lean_object* v___x_1165_; 
v_key_1158_ = lean_ctor_get(v_x_1157_, 0);
lean_inc(v_key_1158_);
v_value_1159_ = lean_ctor_get(v_x_1157_, 1);
lean_inc(v_value_1159_);
v_tail_1160_ = lean_ctor_get(v_x_1157_, 2);
lean_inc(v_tail_1160_);
lean_dec_ref_known(v_x_1157_, 3);
v___x_1165_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_snd_1155_, v_key_1158_);
if (lean_obj_tag(v___x_1165_) == 1)
{
lean_object* v_val_1166_; uint8_t v___x_1167_; 
v_val_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_val_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v___x_1167_ = lean_nat_dec_le(v_value_1159_, v_val_1166_);
if (v___x_1167_ == 0)
{
lean_dec(v_value_1159_);
v___y_1162_ = v_val_1166_;
goto v___jp_1161_;
}
else
{
lean_dec(v_val_1166_);
v___y_1162_ = v_value_1159_;
goto v___jp_1161_;
}
}
else
{
lean_dec(v___x_1165_);
lean_dec(v_value_1159_);
lean_dec(v_key_1158_);
v_x_1157_ = v_tail_1160_;
goto _start;
}
v___jp_1161_:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(v_x_1156_, v_key_1158_, v___y_1162_);
v_x_1156_ = v___x_1163_;
v_x_1157_ = v_tail_1160_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5___boxed(lean_object* v_snd_1169_, lean_object* v_x_1170_, lean_object* v_x_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(v_snd_1169_, v_x_1170_, v_x_1171_);
lean_dec_ref(v_snd_1169_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(lean_object* v_snd_1173_, lean_object* v_as_1174_, size_t v_i_1175_, size_t v_stop_1176_, lean_object* v_b_1177_){
_start:
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_usize_dec_eq(v_i_1175_, v_stop_1176_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; 
v___x_1179_ = lean_array_uget_borrowed(v_as_1174_, v_i_1175_);
lean_inc(v___x_1179_);
v___x_1180_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(v_snd_1173_, v_b_1177_, v___x_1179_);
v___x_1181_ = ((size_t)1ULL);
v___x_1182_ = lean_usize_add(v_i_1175_, v___x_1181_);
v_i_1175_ = v___x_1182_;
v_b_1177_ = v___x_1180_;
goto _start;
}
else
{
return v_b_1177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6___boxed(lean_object* v_snd_1184_, lean_object* v_as_1185_, lean_object* v_i_1186_, lean_object* v_stop_1187_, lean_object* v_b_1188_){
_start:
{
size_t v_i_boxed_1189_; size_t v_stop_boxed_1190_; lean_object* v_res_1191_; 
v_i_boxed_1189_ = lean_unbox_usize(v_i_1186_);
lean_dec(v_i_1186_);
v_stop_boxed_1190_ = lean_unbox_usize(v_stop_1187_);
lean_dec(v_stop_1187_);
v_res_1191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1184_, v_as_1185_, v_i_boxed_1189_, v_stop_boxed_1190_, v_b_1188_);
lean_dec_ref(v_as_1185_);
lean_dec_ref(v_snd_1184_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(lean_object* v_commonCnt_1192_, lean_object* v_a_1193_, lean_object* v_x_1194_){
_start:
{
if (lean_obj_tag(v_x_1194_) == 0)
{
lean_dec(v_a_1193_);
return v_x_1194_;
}
else
{
lean_object* v_key_1195_; lean_object* v_value_1196_; lean_object* v_tail_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1210_; 
v_key_1195_ = lean_ctor_get(v_x_1194_, 0);
v_value_1196_ = lean_ctor_get(v_x_1194_, 1);
v_tail_1197_ = lean_ctor_get(v_x_1194_, 2);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_x_1194_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1199_ = v_x_1194_;
v_isShared_1200_ = v_isSharedCheck_1210_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_tail_1197_);
lean_inc(v_value_1196_);
lean_inc(v_key_1195_);
lean_dec(v_x_1194_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1210_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
uint8_t v___x_1201_; 
v___x_1201_ = lean_nat_dec_eq(v_key_1195_, v_a_1193_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1202_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1192_, v_a_1193_, v_tail_1197_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 2, v___x_1202_);
v___x_1204_ = v___x_1199_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_key_1195_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_value_1196_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
lean_dec(v_key_1195_);
v___x_1206_ = lean_nat_sub(v_value_1196_, v_commonCnt_1192_);
lean_dec(v_value_1196_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 1, v___x_1206_);
lean_ctor_set(v___x_1199_, 0, v_a_1193_);
v___x_1208_ = v___x_1199_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1193_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v_tail_1197_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0___boxed(lean_object* v_commonCnt_1211_, lean_object* v_a_1212_, lean_object* v_x_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1211_, v_a_1212_, v_x_1213_);
lean_dec(v_commonCnt_1211_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(lean_object* v_commonCnt_1215_, lean_object* v_m_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v_size_1218_; lean_object* v_buckets_1219_; lean_object* v___x_1220_; uint64_t v___x_1221_; uint64_t v___x_1222_; uint64_t v___x_1223_; uint64_t v_fold_1224_; uint64_t v___x_1225_; uint64_t v___x_1226_; uint64_t v___x_1227_; size_t v___x_1228_; size_t v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; size_t v___x_1232_; lean_object* v_bucket_1233_; uint8_t v___x_1234_; 
v_size_1218_ = lean_ctor_get(v_m_1216_, 0);
v_buckets_1219_ = lean_ctor_get(v_m_1216_, 1);
v___x_1220_ = lean_array_get_size(v_buckets_1219_);
v___x_1221_ = lean_uint64_of_nat(v_a_1217_);
v___x_1222_ = 32ULL;
v___x_1223_ = lean_uint64_shift_right(v___x_1221_, v___x_1222_);
v_fold_1224_ = lean_uint64_xor(v___x_1221_, v___x_1223_);
v___x_1225_ = 16ULL;
v___x_1226_ = lean_uint64_shift_right(v_fold_1224_, v___x_1225_);
v___x_1227_ = lean_uint64_xor(v_fold_1224_, v___x_1226_);
v___x_1228_ = lean_uint64_to_usize(v___x_1227_);
v___x_1229_ = lean_usize_of_nat(v___x_1220_);
v___x_1230_ = ((size_t)1ULL);
v___x_1231_ = lean_usize_sub(v___x_1229_, v___x_1230_);
v___x_1232_ = lean_usize_land(v___x_1228_, v___x_1231_);
v_bucket_1233_ = lean_array_uget_borrowed(v_buckets_1219_, v___x_1232_);
v___x_1234_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1217_, v_bucket_1233_);
if (v___x_1234_ == 0)
{
lean_dec(v_a_1217_);
return v_m_1216_;
}
else
{
lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1245_; 
lean_inc(v_bucket_1233_);
lean_inc_ref(v_buckets_1219_);
lean_inc(v_size_1218_);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_m_1216_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; lean_object* v_unused_1247_; 
v_unused_1246_ = lean_ctor_get(v_m_1216_, 1);
lean_dec(v_unused_1246_);
v_unused_1247_ = lean_ctor_get(v_m_1216_, 0);
lean_dec(v_unused_1247_);
v___x_1236_ = v_m_1216_;
v_isShared_1237_ = v_isSharedCheck_1245_;
goto v_resetjp_1235_;
}
else
{
lean_dec(v_m_1216_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1245_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; lean_object* v_buckets_1239_; lean_object* v_bucket_1240_; lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1238_ = lean_box(0);
v_buckets_1239_ = lean_array_uset(v_buckets_1219_, v___x_1232_, v___x_1238_);
v_bucket_1240_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1215_, v_a_1217_, v_bucket_1233_);
v___x_1241_ = lean_array_uset(v_buckets_1239_, v___x_1232_, v_bucket_1240_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 1, v___x_1241_);
v___x_1243_ = v___x_1236_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_size_1218_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0___boxed(lean_object* v_commonCnt_1248_, lean_object* v_m_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_commonCnt_1248_, v_m_1249_, v_a_1250_);
lean_dec(v_commonCnt_1248_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(lean_object* v_x_1252_, lean_object* v_x_1253_){
_start:
{
if (lean_obj_tag(v_x_1253_) == 0)
{
return v_x_1252_;
}
else
{
lean_object* v_key_1254_; lean_object* v_value_1255_; lean_object* v_tail_1256_; lean_object* v___x_1257_; 
v_key_1254_ = lean_ctor_get(v_x_1253_, 0);
lean_inc(v_key_1254_);
v_value_1255_ = lean_ctor_get(v_x_1253_, 1);
lean_inc(v_value_1255_);
v_tail_1256_ = lean_ctor_get(v_x_1253_, 2);
lean_inc(v_tail_1256_);
lean_dec_ref_known(v_x_1253_, 3);
v___x_1257_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_value_1255_, v_x_1252_, v_key_1254_);
lean_dec(v_value_1255_);
v_x_1252_ = v___x_1257_;
v_x_1253_ = v_tail_1256_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(lean_object* v_x_1259_, lean_object* v_x_1260_){
_start:
{
if (lean_obj_tag(v_x_1260_) == 0)
{
return v_x_1259_;
}
else
{
lean_object* v_key_1261_; lean_object* v_value_1262_; lean_object* v_tail_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v_key_1261_ = lean_ctor_get(v_x_1260_, 0);
lean_inc(v_key_1261_);
v_value_1262_ = lean_ctor_get(v_x_1260_, 1);
lean_inc(v_value_1262_);
v_tail_1263_ = lean_ctor_get(v_x_1260_, 2);
lean_inc(v_tail_1263_);
lean_dec_ref_known(v_x_1260_, 3);
v___x_1264_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_value_1262_, v_x_1259_, v_key_1261_);
lean_dec(v_value_1262_);
v___x_1265_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(v___x_1264_, v_tail_1263_);
return v___x_1265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(lean_object* v_as_1266_, size_t v_i_1267_, size_t v_stop_1268_, lean_object* v_b_1269_){
_start:
{
uint8_t v___x_1270_; 
v___x_1270_ = lean_usize_dec_eq(v_i_1267_, v_stop_1268_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; size_t v___x_1273_; size_t v___x_1274_; 
v___x_1271_ = lean_array_uget_borrowed(v_as_1266_, v_i_1267_);
lean_inc(v___x_1271_);
v___x_1272_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(v_b_1269_, v___x_1271_);
v___x_1273_ = ((size_t)1ULL);
v___x_1274_ = lean_usize_add(v_i_1267_, v___x_1273_);
v_i_1267_ = v___x_1274_;
v_b_1269_ = v___x_1272_;
goto _start;
}
else
{
return v_b_1269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2___boxed(lean_object* v_as_1276_, lean_object* v_i_1277_, lean_object* v_stop_1278_, lean_object* v_b_1279_){
_start:
{
size_t v_i_boxed_1280_; size_t v_stop_boxed_1281_; lean_object* v_res_1282_; 
v_i_boxed_1280_ = lean_unbox_usize(v_i_1277_);
lean_dec(v_i_1277_);
v_stop_boxed_1281_ = lean_unbox_usize(v_stop_1278_);
lean_dec(v_stop_1278_);
v_res_1282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_as_1276_, v_i_boxed_1280_, v_stop_boxed_1281_, v_b_1279_);
lean_dec_ref(v_as_1276_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(lean_object* v_x_1283_, lean_object* v_y_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v___y_1288_; lean_object* v_fst_1289_; lean_object* v_snd_1290_; lean_object* v_size_1294_; lean_object* v_buckets_1295_; lean_object* v_size_1296_; lean_object* v_buckets_1297_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v_buckets_1306_; lean_object* v___y_1307_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v_buckets_1318_; lean_object* v_fst_1326_; lean_object* v_buckets_1327_; lean_object* v_snd_1328_; uint8_t v___x_1338_; 
v_size_1294_ = lean_ctor_get(v_y_1284_, 0);
lean_inc(v_size_1294_);
v_buckets_1295_ = lean_ctor_get(v_y_1284_, 1);
v_size_1296_ = lean_ctor_get(v_x_1283_, 0);
lean_inc(v_size_1296_);
v_buckets_1297_ = lean_ctor_get(v_x_1283_, 1);
v___x_1338_ = lean_nat_dec_lt(v_size_1294_, v_size_1296_);
if (v___x_1338_ == 0)
{
lean_inc_ref(v_buckets_1297_);
v_fst_1326_ = v_x_1283_;
v_buckets_1327_ = v_buckets_1297_;
v_snd_1328_ = v_y_1284_;
goto v___jp_1325_;
}
else
{
lean_inc_ref(v_buckets_1295_);
v_fst_1326_ = v_y_1284_;
v_buckets_1327_ = v_buckets_1295_;
v_snd_1328_ = v_x_1283_;
goto v___jp_1325_;
}
v___jp_1287_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1291_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1291_, 0, v___y_1288_);
lean_ctor_set(v___x_1291_, 1, v_fst_1289_);
lean_ctor_set(v___x_1291_, 2, v_snd_1290_);
v___x_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
lean_ctor_set(v___x_1292_, 1, v_a_1285_);
v___x_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
return v___x_1293_;
}
v___jp_1298_:
{
uint8_t v___x_1302_; 
v___x_1302_ = lean_nat_dec_lt(v_size_1294_, v_size_1296_);
lean_dec(v_size_1296_);
lean_dec(v_size_1294_);
if (v___x_1302_ == 0)
{
v___y_1288_ = v___y_1300_;
v_fst_1289_ = v___y_1299_;
v_snd_1290_ = v___y_1301_;
goto v___jp_1287_;
}
else
{
v___y_1288_ = v___y_1300_;
v_fst_1289_ = v___y_1301_;
v_snd_1290_ = v___y_1299_;
goto v___jp_1287_;
}
}
v___jp_1303_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = lean_array_get_size(v_buckets_1306_);
v___x_1310_ = lean_nat_dec_lt(v___x_1308_, v___x_1309_);
if (v___x_1310_ == 0)
{
lean_dec_ref(v_buckets_1306_);
v___y_1299_ = v___y_1307_;
v___y_1300_ = v___y_1305_;
v___y_1301_ = v___y_1304_;
goto v___jp_1298_;
}
else
{
size_t v___x_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = ((size_t)0ULL);
v___x_1312_ = lean_usize_of_nat(v___x_1309_);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1306_, v___x_1311_, v___x_1312_, v___y_1304_);
lean_dec_ref(v_buckets_1306_);
v___y_1299_ = v___y_1307_;
v___y_1300_ = v___y_1305_;
v___y_1301_ = v___x_1313_;
goto v___jp_1298_;
}
}
v___jp_1314_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1319_ = lean_unsigned_to_nat(0u);
v___x_1320_ = lean_array_get_size(v_buckets_1318_);
v___x_1321_ = lean_nat_dec_lt(v___x_1319_, v___x_1320_);
if (v___x_1321_ == 0)
{
v___y_1304_ = v___y_1315_;
v___y_1305_ = v___y_1317_;
v_buckets_1306_ = v_buckets_1318_;
v___y_1307_ = v___y_1316_;
goto v___jp_1303_;
}
else
{
size_t v___x_1322_; size_t v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = ((size_t)0ULL);
v___x_1323_ = lean_usize_of_nat(v___x_1320_);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1318_, v___x_1322_, v___x_1323_, v___y_1316_);
v___y_1304_ = v___y_1315_;
v___y_1305_ = v___y_1317_;
v_buckets_1306_ = v_buckets_1318_;
v___y_1307_ = v___x_1324_;
goto v___jp_1303_;
}
}
v___jp_1325_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1329_ = lean_unsigned_to_nat(0u);
v___x_1330_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1331_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1332_ = lean_array_get_size(v_buckets_1327_);
v___x_1333_ = lean_nat_dec_lt(v___x_1329_, v___x_1332_);
if (v___x_1333_ == 0)
{
lean_dec_ref(v_buckets_1327_);
v___y_1315_ = v_snd_1328_;
v___y_1316_ = v_fst_1326_;
v___y_1317_ = v___x_1331_;
v_buckets_1318_ = v___x_1330_;
goto v___jp_1314_;
}
else
{
size_t v___x_1334_; size_t v___x_1335_; lean_object* v___x_1336_; lean_object* v_buckets_1337_; 
v___x_1334_ = ((size_t)0ULL);
v___x_1335_ = lean_usize_of_nat(v___x_1332_);
v___x_1336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1328_, v_buckets_1327_, v___x_1334_, v___x_1335_, v___x_1331_);
lean_dec_ref(v_buckets_1327_);
v_buckets_1337_ = lean_ctor_get(v___x_1336_, 1);
lean_inc_ref(v_buckets_1337_);
v___y_1315_ = v_snd_1328_;
v___y_1316_ = v_fst_1326_;
v___y_1317_ = v___x_1336_;
v_buckets_1318_ = v_buckets_1337_;
goto v___jp_1314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg___boxed(lean_object* v_x_1339_, lean_object* v_y_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1339_, v_y_1340_, v_a_1341_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(lean_object* v_x_1344_, lean_object* v_y_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1344_, v_y_1345_, v_a_1346_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___boxed(lean_object* v_x_1355_, lean_object* v_y_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(v_x_1355_, v_y_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3(lean_object* v_00_u03b2_1366_, lean_object* v_m_1367_, lean_object* v_a_1368_, lean_object* v_b_1369_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(v_m_1367_, v_a_1368_, v_b_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4(lean_object* v_00_u03b2_1371_, lean_object* v_m_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1372_, v_a_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___boxed(lean_object* v_00_u03b2_1375_, lean_object* v_m_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4(v_00_u03b2_1375_, v_m_1376_, v_a_1377_);
lean_dec(v_a_1377_);
lean_dec_ref(v_m_1376_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5(lean_object* v_00_u03b2_1379_, lean_object* v_a_1380_, lean_object* v_b_1381_, lean_object* v_x_1382_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1380_, v_b_1381_, v_x_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7(lean_object* v_00_u03b2_1384_, lean_object* v_a_1385_, lean_object* v_x_1386_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1385_, v_x_1386_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1388_, lean_object* v_a_1389_, lean_object* v_x_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7(v_00_u03b2_1388_, v_a_1389_, v_x_1390_);
lean_dec(v_x_1390_);
lean_dec(v_a_1389_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(lean_object* v_x_1392_, lean_object* v_x_1393_){
_start:
{
if (lean_obj_tag(v_x_1393_) == 0)
{
return v_x_1392_;
}
else
{
lean_object* v_key_1394_; lean_object* v_value_1395_; lean_object* v_tail_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v_key_1394_ = lean_ctor_get(v_x_1393_, 0);
v_value_1395_ = lean_ctor_get(v_x_1393_, 1);
v_tail_1396_ = lean_ctor_get(v_x_1393_, 2);
lean_inc(v_value_1395_);
lean_inc(v_key_1394_);
v___x_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1397_, 0, v_key_1394_);
lean_ctor_set(v___x_1397_, 1, v_value_1395_);
v___x_1398_ = lean_array_push(v_x_1392_, v___x_1397_);
v_x_1392_ = v___x_1398_;
v_x_1393_ = v_tail_1396_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___boxed(lean_object* v_x_1400_, lean_object* v_x_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(v_x_1400_, v_x_1401_);
lean_dec(v_x_1401_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(lean_object* v_as_1403_, size_t v_i_1404_, size_t v_stop_1405_, lean_object* v_b_1406_){
_start:
{
uint8_t v___x_1407_; 
v___x_1407_ = lean_usize_dec_eq(v_i_1404_, v_stop_1405_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; size_t v___x_1410_; size_t v___x_1411_; 
v___x_1408_ = lean_array_uget_borrowed(v_as_1403_, v_i_1404_);
v___x_1409_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(v_b_1406_, v___x_1408_);
v___x_1410_ = ((size_t)1ULL);
v___x_1411_ = lean_usize_add(v_i_1404_, v___x_1410_);
v_i_1404_ = v___x_1411_;
v_b_1406_ = v___x_1409_;
goto _start;
}
else
{
return v_b_1406_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4___boxed(lean_object* v_as_1413_, lean_object* v_i_1414_, lean_object* v_stop_1415_, lean_object* v_b_1416_){
_start:
{
size_t v_i_boxed_1417_; size_t v_stop_boxed_1418_; lean_object* v_res_1419_; 
v_i_boxed_1417_ = lean_unbox_usize(v_i_1414_);
lean_dec(v_i_1414_);
v_stop_boxed_1418_ = lean_unbox_usize(v_stop_1415_);
lean_dec(v_stop_1415_);
v_res_1419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_as_1413_, v_i_boxed_1417_, v_stop_boxed_1418_, v_b_1416_);
lean_dec_ref(v_as_1413_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(lean_object* v_upperBound_1420_, lean_object* v___x_1421_, lean_object* v_op_1422_, lean_object* v_a_1423_, lean_object* v_b_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v___y_1428_; uint8_t v___x_1432_; 
v___x_1432_ = lean_nat_dec_lt(v_a_1423_, v_upperBound_1420_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_dec(v_a_1423_);
lean_dec_ref(v_op_1422_);
lean_dec_ref(v___x_1421_);
v___x_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1433_, 0, v_b_1424_);
lean_ctor_set(v___x_1433_, 1, v___y_1425_);
v___x_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
return v___x_1434_;
}
else
{
if (lean_obj_tag(v_b_1424_) == 0)
{
lean_object* v___x_1435_; 
lean_inc_ref(v___x_1421_);
v___x_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1421_);
v___y_1428_ = v___x_1435_;
goto v___jp_1427_;
}
else
{
lean_object* v_val_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1445_; 
v_val_1436_ = lean_ctor_get(v_b_1424_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_b_1424_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1438_ = v_b_1424_;
v_isShared_1439_ = v_isSharedCheck_1445_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_val_1436_);
lean_dec(v_b_1424_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1445_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1443_; 
lean_inc_ref(v_op_1422_);
v___x_1440_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_1422_);
lean_inc_ref(v___x_1421_);
v___x_1441_ = l_Lean_mkAppB(v___x_1440_, v_val_1436_, v___x_1421_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1441_);
v___x_1443_ = v___x_1438_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
v___y_1428_ = v___x_1443_;
goto v___jp_1427_;
}
}
}
}
v___jp_1427_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = lean_unsigned_to_nat(1u);
v___x_1430_ = lean_nat_add(v_a_1423_, v___x_1429_);
lean_dec(v_a_1423_);
v_a_1423_ = v___x_1430_;
v_b_1424_ = v___y_1428_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg___boxed(lean_object* v_upperBound_1446_, lean_object* v___x_1447_, lean_object* v_op_1448_, lean_object* v_a_1449_, lean_object* v_b_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1446_, v___x_1447_, v_op_1448_, v_a_1449_, v_b_1450_, v___y_1451_);
lean_dec(v_upperBound_1446_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(lean_object* v_op_1454_, lean_object* v_as_1455_, size_t v_sz_1456_, size_t v_i_1457_, lean_object* v_b_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
uint8_t v___x_1467_; 
v___x_1467_ = lean_usize_dec_lt(v_i_1457_, v_sz_1456_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec_ref(v_op_1454_);
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v_b_1458_);
lean_ctor_set(v___x_1468_, 1, v___y_1459_);
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
return v___x_1469_;
}
else
{
lean_object* v_a_1470_; lean_object* v_fst_1471_; lean_object* v_snd_1472_; lean_object* v_varToExpr_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v_a_1470_ = lean_array_uget_borrowed(v_as_1455_, v_i_1457_);
v_fst_1471_ = lean_ctor_get(v_a_1470_, 0);
v_snd_1472_ = lean_ctor_get(v_a_1470_, 1);
v_varToExpr_1473_ = lean_ctor_get(v___y_1459_, 2);
v___x_1474_ = l_Lean_instInhabitedExpr;
v___x_1475_ = lean_unsigned_to_nat(0u);
v___x_1476_ = lean_array_get(v___x_1474_, v_varToExpr_1473_, v_fst_1471_);
lean_inc_ref(v_op_1454_);
v___x_1477_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_snd_1472_, v___x_1476_, v_op_1454_, v___x_1475_, v_b_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v_fst_1479_; lean_object* v_snd_1480_; size_t v___x_1481_; size_t v___x_1482_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
v_fst_1479_ = lean_ctor_get(v_a_1478_, 0);
lean_inc(v_fst_1479_);
v_snd_1480_ = lean_ctor_get(v_a_1478_, 1);
lean_inc(v_snd_1480_);
lean_dec(v_a_1478_);
v___x_1481_ = ((size_t)1ULL);
v___x_1482_ = lean_usize_add(v_i_1457_, v___x_1481_);
v_i_1457_ = v___x_1482_;
v_b_1458_ = v_fst_1479_;
v___y_1459_ = v_snd_1480_;
goto _start;
}
else
{
lean_dec_ref(v_op_1454_);
return v___x_1477_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1___boxed(lean_object* v_op_1484_, lean_object* v_as_1485_, lean_object* v_sz_1486_, lean_object* v_i_1487_, lean_object* v_b_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
size_t v_sz_boxed_1497_; size_t v_i_boxed_1498_; lean_object* v_res_1499_; 
v_sz_boxed_1497_ = lean_unbox_usize(v_sz_1486_);
lean_dec(v_sz_1486_);
v_i_boxed_1498_ = lean_unbox_usize(v_i_1487_);
lean_dec(v_i_1487_);
v_res_1499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1484_, v_as_1485_, v_sz_boxed_1497_, v_i_boxed_1498_, v_b_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec_ref(v_as_1485_);
return v_res_1499_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(lean_object* v_x1_1500_, lean_object* v_x2_1501_){
_start:
{
lean_object* v_fst_1502_; lean_object* v_fst_1503_; uint8_t v___x_1504_; 
v_fst_1502_ = lean_ctor_get(v_x1_1500_, 0);
v_fst_1503_ = lean_ctor_get(v_x2_1501_, 0);
v___x_1504_ = lean_nat_dec_lt(v_fst_1502_, v_fst_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed(lean_object* v_x1_1505_, lean_object* v_x2_1506_){
_start:
{
uint8_t v_res_1507_; lean_object* v_r_1508_; 
v_res_1507_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v_x1_1505_, v_x2_1506_);
lean_dec_ref(v_x2_1506_);
lean_dec_ref(v_x1_1505_);
v_r_1508_ = lean_box(v_res_1507_);
return v_r_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(lean_object* v_hi_1509_, lean_object* v_pivot_1510_, lean_object* v_as_1511_, lean_object* v_i_1512_, lean_object* v_k_1513_){
_start:
{
uint8_t v___x_1514_; 
v___x_1514_ = lean_nat_dec_lt(v_k_1513_, v_hi_1509_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_dec(v_k_1513_);
v___x_1515_ = lean_array_fswap(v_as_1511_, v_i_1512_, v_hi_1509_);
v___x_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1516_, 0, v_i_1512_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
return v___x_1516_;
}
else
{
lean_object* v___x_1517_; lean_object* v_fst_1518_; lean_object* v_fst_1519_; uint8_t v___x_1520_; 
v___x_1517_ = lean_array_fget_borrowed(v_as_1511_, v_k_1513_);
v_fst_1518_ = lean_ctor_get(v___x_1517_, 0);
v_fst_1519_ = lean_ctor_get(v_pivot_1510_, 0);
v___x_1520_ = lean_nat_dec_lt(v_fst_1518_, v_fst_1519_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = lean_unsigned_to_nat(1u);
v___x_1522_ = lean_nat_add(v_k_1513_, v___x_1521_);
lean_dec(v_k_1513_);
v_k_1513_ = v___x_1522_;
goto _start;
}
else
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1524_ = lean_array_fswap(v_as_1511_, v_i_1512_, v_k_1513_);
v___x_1525_ = lean_unsigned_to_nat(1u);
v___x_1526_ = lean_nat_add(v_i_1512_, v___x_1525_);
lean_dec(v_i_1512_);
v___x_1527_ = lean_nat_add(v_k_1513_, v___x_1525_);
lean_dec(v_k_1513_);
v_as_1511_ = v___x_1524_;
v_i_1512_ = v___x_1526_;
v_k_1513_ = v___x_1527_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg___boxed(lean_object* v_hi_1529_, lean_object* v_pivot_1530_, lean_object* v_as_1531_, lean_object* v_i_1532_, lean_object* v_k_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1529_, v_pivot_1530_, v_as_1531_, v_i_1532_, v_k_1533_);
lean_dec_ref(v_pivot_1530_);
lean_dec(v_hi_1529_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(lean_object* v_n_1535_, lean_object* v_as_1536_, lean_object* v_lo_1537_, lean_object* v_hi_1538_){
_start:
{
lean_object* v___y_1540_; uint8_t v___x_1550_; 
v___x_1550_ = lean_nat_dec_lt(v_lo_1537_, v_hi_1538_);
if (v___x_1550_ == 0)
{
lean_dec(v_lo_1537_);
return v_as_1536_;
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v_mid_1553_; lean_object* v___y_1555_; lean_object* v___y_1561_; lean_object* v___x_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1551_ = lean_nat_add(v_lo_1537_, v_hi_1538_);
v___x_1552_ = lean_unsigned_to_nat(1u);
v_mid_1553_ = lean_nat_shiftr(v___x_1551_, v___x_1552_);
lean_dec(v___x_1551_);
v___x_1566_ = lean_array_fget_borrowed(v_as_1536_, v_mid_1553_);
v___x_1567_ = lean_array_fget_borrowed(v_as_1536_, v_lo_1537_);
v___x_1568_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1566_, v___x_1567_);
if (v___x_1568_ == 0)
{
v___y_1561_ = v_as_1536_;
goto v___jp_1560_;
}
else
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_array_fswap(v_as_1536_, v_lo_1537_, v_mid_1553_);
v___y_1561_ = v___x_1569_;
goto v___jp_1560_;
}
v___jp_1554_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1556_ = lean_array_fget_borrowed(v___y_1555_, v_mid_1553_);
v___x_1557_ = lean_array_fget_borrowed(v___y_1555_, v_hi_1538_);
v___x_1558_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1556_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_dec(v_mid_1553_);
v___y_1540_ = v___y_1555_;
goto v___jp_1539_;
}
else
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_array_fswap(v___y_1555_, v_mid_1553_, v_hi_1538_);
lean_dec(v_mid_1553_);
v___y_1540_ = v___x_1559_;
goto v___jp_1539_;
}
}
v___jp_1560_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1562_ = lean_array_fget_borrowed(v___y_1561_, v_hi_1538_);
v___x_1563_ = lean_array_fget_borrowed(v___y_1561_, v_lo_1537_);
v___x_1564_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1562_, v___x_1563_);
if (v___x_1564_ == 0)
{
v___y_1555_ = v___y_1561_;
goto v___jp_1554_;
}
else
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_array_fswap(v___y_1561_, v_lo_1537_, v_hi_1538_);
v___y_1555_ = v___x_1565_;
goto v___jp_1554_;
}
}
}
v___jp_1539_:
{
lean_object* v_pivot_1541_; lean_object* v___x_1542_; lean_object* v_fst_1543_; lean_object* v_snd_1544_; uint8_t v___x_1545_; 
v_pivot_1541_ = lean_array_fget(v___y_1540_, v_hi_1538_);
lean_inc_n(v_lo_1537_, 2);
v___x_1542_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1538_, v_pivot_1541_, v___y_1540_, v_lo_1537_, v_lo_1537_);
lean_dec(v_pivot_1541_);
v_fst_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_fst_1543_);
v_snd_1544_ = lean_ctor_get(v___x_1542_, 1);
lean_inc(v_snd_1544_);
lean_dec_ref(v___x_1542_);
v___x_1545_ = lean_nat_dec_le(v_hi_1538_, v_fst_1543_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1546_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1535_, v_snd_1544_, v_lo_1537_, v_fst_1543_);
v___x_1547_ = lean_unsigned_to_nat(1u);
v___x_1548_ = lean_nat_add(v_fst_1543_, v___x_1547_);
lean_dec(v_fst_1543_);
v_as_1536_ = v___x_1546_;
v_lo_1537_ = v___x_1548_;
goto _start;
}
else
{
lean_dec(v_fst_1543_);
lean_dec(v_lo_1537_);
return v_snd_1544_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___boxed(lean_object* v_n_1570_, lean_object* v_as_1571_, lean_object* v_lo_1572_, lean_object* v_hi_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1570_, v_as_1571_, v_lo_1572_, v_hi_1573_);
lean_dec(v_hi_1573_);
lean_dec(v_n_1570_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(lean_object* v_coeff_1575_, lean_object* v_op_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v___y_1586_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1604_; lean_object* v_size_1611_; lean_object* v_buckets_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
v_size_1611_ = lean_ctor_get(v_coeff_1575_, 0);
v_buckets_1612_ = lean_ctor_get(v_coeff_1575_, 1);
v___x_1613_ = lean_mk_empty_array_with_capacity(v_size_1611_);
v___x_1614_ = lean_unsigned_to_nat(0u);
v___x_1615_ = lean_array_get_size(v_buckets_1612_);
v___x_1616_ = lean_nat_dec_lt(v___x_1614_, v___x_1615_);
if (v___x_1616_ == 0)
{
v___y_1604_ = v___x_1613_;
goto v___jp_1603_;
}
else
{
size_t v___x_1617_; size_t v___x_1618_; lean_object* v___x_1619_; 
v___x_1617_ = ((size_t)0ULL);
v___x_1618_ = lean_usize_of_nat(v___x_1615_);
v___x_1619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_buckets_1612_, v___x_1617_, v___x_1618_, v___x_1613_);
v___y_1604_ = v___x_1619_;
goto v___jp_1603_;
}
v___jp_1585_:
{
lean_object* v_acc_1587_; size_t v_sz_1588_; size_t v___x_1589_; lean_object* v___x_1590_; 
v_acc_1587_ = lean_box(0);
v_sz_1588_ = lean_array_size(v___y_1586_);
v___x_1589_ = ((size_t)0ULL);
v___x_1590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1576_, v___y_1586_, v_sz_1588_, v___x_1589_, v_acc_1587_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
lean_dec_ref(v___y_1586_);
return v___x_1590_;
}
v___jp_1591_:
{
lean_object* v___x_1596_; 
v___x_1596_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v___y_1593_, v___y_1592_, v___y_1594_, v___y_1595_);
lean_dec(v___y_1595_);
lean_dec(v___y_1593_);
v___y_1586_ = v___x_1596_;
goto v___jp_1585_;
}
v___jp_1597_:
{
uint8_t v___x_1602_; 
v___x_1602_ = lean_nat_dec_le(v___y_1601_, v___y_1599_);
if (v___x_1602_ == 0)
{
lean_dec(v___y_1599_);
lean_inc(v___y_1601_);
v___y_1592_ = v___y_1598_;
v___y_1593_ = v___y_1600_;
v___y_1594_ = v___y_1601_;
v___y_1595_ = v___y_1601_;
goto v___jp_1591_;
}
else
{
v___y_1592_ = v___y_1598_;
v___y_1593_ = v___y_1600_;
v___y_1594_ = v___y_1601_;
v___y_1595_ = v___y_1599_;
goto v___jp_1591_;
}
}
v___jp_1603_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1605_ = lean_array_get_size(v___y_1604_);
v___x_1606_ = lean_unsigned_to_nat(0u);
v___x_1607_ = lean_nat_dec_eq(v___x_1605_, v___x_1606_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1608_ = lean_unsigned_to_nat(1u);
v___x_1609_ = lean_nat_sub(v___x_1605_, v___x_1608_);
v___x_1610_ = lean_nat_dec_le(v___x_1606_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_inc(v___x_1609_);
v___y_1598_ = v___y_1604_;
v___y_1599_ = v___x_1609_;
v___y_1600_ = v___x_1605_;
v___y_1601_ = v___x_1609_;
goto v___jp_1597_;
}
else
{
v___y_1598_ = v___y_1604_;
v___y_1599_ = v___x_1609_;
v___y_1600_ = v___x_1605_;
v___y_1601_ = v___x_1606_;
goto v___jp_1597_;
}
}
else
{
v___y_1586_ = v___y_1604_;
goto v___jp_1585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr___boxed(lean_object* v_coeff_1620_, lean_object* v_op_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_coeff_1620_, v_op_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
lean_dec_ref(v_coeff_1620_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(lean_object* v_upperBound_1631_, lean_object* v___x_1632_, lean_object* v_op_1633_, lean_object* v_inst_1634_, lean_object* v_R_1635_, lean_object* v_a_1636_, lean_object* v_b_1637_, lean_object* v_c_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1631_, v___x_1632_, v_op_1633_, v_a_1636_, v_b_1637_, v___y_1639_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___boxed(lean_object* v_upperBound_1648_, lean_object* v___x_1649_, lean_object* v_op_1650_, lean_object* v_inst_1651_, lean_object* v_R_1652_, lean_object* v_a_1653_, lean_object* v_b_1654_, lean_object* v_c_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(v_upperBound_1648_, v___x_1649_, v_op_1650_, v_inst_1651_, v_R_1652_, v_a_1653_, v_b_1654_, v_c_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v_upperBound_1648_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(lean_object* v_n_1665_, lean_object* v_as_1666_, lean_object* v_lo_1667_, lean_object* v_hi_1668_, lean_object* v_w_1669_, lean_object* v_hlo_1670_, lean_object* v_hhi_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1665_, v_as_1666_, v_lo_1667_, v_hi_1668_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___boxed(lean_object* v_n_1673_, lean_object* v_as_1674_, lean_object* v_lo_1675_, lean_object* v_hi_1676_, lean_object* v_w_1677_, lean_object* v_hlo_1678_, lean_object* v_hhi_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(v_n_1673_, v_as_1674_, v_lo_1675_, v_hi_1676_, v_w_1677_, v_hlo_1678_, v_hhi_1679_);
lean_dec(v_hi_1676_);
lean_dec(v_n_1673_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(lean_object* v_n_1681_, lean_object* v_lo_1682_, lean_object* v_hi_1683_, lean_object* v_hhi_1684_, lean_object* v_pivot_1685_, lean_object* v_as_1686_, lean_object* v_i_1687_, lean_object* v_k_1688_, lean_object* v_ilo_1689_, lean_object* v_ik_1690_, lean_object* v_w_1691_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1683_, v_pivot_1685_, v_as_1686_, v_i_1687_, v_k_1688_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___boxed(lean_object* v_n_1693_, lean_object* v_lo_1694_, lean_object* v_hi_1695_, lean_object* v_hhi_1696_, lean_object* v_pivot_1697_, lean_object* v_as_1698_, lean_object* v_i_1699_, lean_object* v_k_1700_, lean_object* v_ilo_1701_, lean_object* v_ik_1702_, lean_object* v_w_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(v_n_1693_, v_lo_1694_, v_hi_1695_, v_hhi_1696_, v_pivot_1697_, v_as_1698_, v_i_1699_, v_k_1700_, v_ilo_1701_, v_ik_1702_, v_w_1703_);
lean_dec_ref(v_pivot_1697_);
lean_dec(v_hi_1695_);
lean_dec(v_lo_1694_);
lean_dec(v_n_1693_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(lean_object* v_e_1705_, lean_object* v___y_1706_){
_start:
{
uint8_t v___x_1708_; 
v___x_1708_ = l_Lean_Expr_hasMVar(v_e_1705_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1709_, 0, v_e_1705_);
return v___x_1709_;
}
else
{
lean_object* v___x_1710_; lean_object* v_mctx_1711_; lean_object* v___x_1712_; lean_object* v_fst_1713_; lean_object* v_snd_1714_; lean_object* v___x_1715_; lean_object* v_cache_1716_; lean_object* v_zetaDeltaFVarIds_1717_; lean_object* v_postponed_1718_; lean_object* v_diag_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1728_; 
v___x_1710_ = lean_st_ref_get(v___y_1706_);
v_mctx_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc_ref(v_mctx_1711_);
lean_dec(v___x_1710_);
v___x_1712_ = l_Lean_instantiateMVarsCore(v_mctx_1711_, v_e_1705_);
v_fst_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_fst_1713_);
v_snd_1714_ = lean_ctor_get(v___x_1712_, 1);
lean_inc(v_snd_1714_);
lean_dec_ref(v___x_1712_);
v___x_1715_ = lean_st_ref_take(v___y_1706_);
v_cache_1716_ = lean_ctor_get(v___x_1715_, 1);
v_zetaDeltaFVarIds_1717_ = lean_ctor_get(v___x_1715_, 2);
v_postponed_1718_ = lean_ctor_get(v___x_1715_, 3);
v_diag_1719_ = lean_ctor_get(v___x_1715_, 4);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1728_ == 0)
{
lean_object* v_unused_1729_; 
v_unused_1729_ = lean_ctor_get(v___x_1715_, 0);
lean_dec(v_unused_1729_);
v___x_1721_ = v___x_1715_;
v_isShared_1722_ = v_isSharedCheck_1728_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_diag_1719_);
lean_inc(v_postponed_1718_);
lean_inc(v_zetaDeltaFVarIds_1717_);
lean_inc(v_cache_1716_);
lean_dec(v___x_1715_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1728_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v_snd_1714_);
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_snd_1714_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_cache_1716_);
lean_ctor_set(v_reuseFailAlloc_1727_, 2, v_zetaDeltaFVarIds_1717_);
lean_ctor_set(v_reuseFailAlloc_1727_, 3, v_postponed_1718_);
lean_ctor_set(v_reuseFailAlloc_1727_, 4, v_diag_1719_);
v___x_1724_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = lean_st_ref_put(v___y_1706_, v___x_1724_);
v___x_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1726_, 0, v_fst_1713_);
return v___x_1726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg___boxed(lean_object* v_e_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1730_, v___y_1731_);
lean_dec(v___y_1731_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(lean_object* v_e_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1734_, v___y_1736_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___boxed(lean_object* v_e_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(v_e_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(lean_object* v_x_1748_, lean_object* v_y_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_Meta_mkEq(v_x_1748_, v_y_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1778_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1778_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1778_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
lean_ctor_set_tag(v___x_1758_, 1);
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
uint8_t v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1762_ = 0;
v___x_1763_ = lean_box(0);
v___x_1764_ = l_Lean_Meta_mkFreshExprMVar(v___x_1761_, v___x_1762_, v___x_1763_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v___x_1766_ = l_Lean_Expr_mvarId_x21(v_a_1765_);
v___x_1767_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v___x_1766_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v___x_1768_; 
lean_dec_ref_known(v___x_1767_, 1);
v___x_1768_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_a_1765_, v_a_1751_);
return v___x_1768_;
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec(v_a_1765_);
v_a_1769_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1767_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1767_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
else
{
return v___x_1764_;
}
}
}
}
else
{
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC___boxed(lean_object* v_x_1779_, lean_object* v_y_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v_x_1779_, v_y_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
return v_res_1786_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1787_ = lean_unsigned_to_nat(32u);
v___x_1788_ = lean_mk_empty_array_with_capacity(v___x_1787_);
v___x_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
return v___x_1789_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1790_ = ((size_t)5ULL);
v___x_1791_ = lean_unsigned_to_nat(0u);
v___x_1792_ = lean_unsigned_to_nat(32u);
v___x_1793_ = lean_mk_empty_array_with_capacity(v___x_1792_);
v___x_1794_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0);
v___x_1795_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
lean_ctor_set(v___x_1795_, 1, v___x_1793_);
lean_ctor_set(v___x_1795_, 2, v___x_1791_);
lean_ctor_set(v___x_1795_, 3, v___x_1791_);
lean_ctor_set_usize(v___x_1795_, 4, v___x_1790_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(lean_object* v___y_1796_){
_start:
{
lean_object* v___x_1798_; lean_object* v_traceState_1799_; lean_object* v_traces_1800_; lean_object* v___x_1801_; lean_object* v_traceState_1802_; lean_object* v_env_1803_; lean_object* v_nextMacroScope_1804_; lean_object* v_ngen_1805_; lean_object* v_auxDeclNGen_1806_; lean_object* v_cache_1807_; lean_object* v_messages_1808_; lean_object* v_infoState_1809_; lean_object* v_snapshotTasks_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1829_; 
v___x_1798_ = lean_st_ref_get(v___y_1796_);
v_traceState_1799_ = lean_ctor_get(v___x_1798_, 4);
lean_inc_ref(v_traceState_1799_);
lean_dec(v___x_1798_);
v_traces_1800_ = lean_ctor_get(v_traceState_1799_, 0);
lean_inc_ref(v_traces_1800_);
lean_dec_ref(v_traceState_1799_);
v___x_1801_ = lean_st_ref_take(v___y_1796_);
v_traceState_1802_ = lean_ctor_get(v___x_1801_, 4);
v_env_1803_ = lean_ctor_get(v___x_1801_, 0);
v_nextMacroScope_1804_ = lean_ctor_get(v___x_1801_, 1);
v_ngen_1805_ = lean_ctor_get(v___x_1801_, 2);
v_auxDeclNGen_1806_ = lean_ctor_get(v___x_1801_, 3);
v_cache_1807_ = lean_ctor_get(v___x_1801_, 5);
v_messages_1808_ = lean_ctor_get(v___x_1801_, 6);
v_infoState_1809_ = lean_ctor_get(v___x_1801_, 7);
v_snapshotTasks_1810_ = lean_ctor_get(v___x_1801_, 8);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1812_ = v___x_1801_;
v_isShared_1813_ = v_isSharedCheck_1829_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_snapshotTasks_1810_);
lean_inc(v_infoState_1809_);
lean_inc(v_messages_1808_);
lean_inc(v_cache_1807_);
lean_inc(v_traceState_1802_);
lean_inc(v_auxDeclNGen_1806_);
lean_inc(v_ngen_1805_);
lean_inc(v_nextMacroScope_1804_);
lean_inc(v_env_1803_);
lean_dec(v___x_1801_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1829_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
uint64_t v_tid_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1827_; 
v_tid_1814_ = lean_ctor_get_uint64(v_traceState_1802_, sizeof(void*)*1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_traceState_1802_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; 
v_unused_1828_ = lean_ctor_get(v_traceState_1802_, 0);
lean_dec(v_unused_1828_);
v___x_1816_ = v_traceState_1802_;
v_isShared_1817_ = v_isSharedCheck_1827_;
goto v_resetjp_1815_;
}
else
{
lean_dec(v_traceState_1802_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1827_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; lean_object* v___x_1820_; 
v___x_1818_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1818_);
v___x_1820_ = v___x_1816_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1818_);
lean_ctor_set_uint64(v_reuseFailAlloc_1826_, sizeof(void*)*1, v_tid_1814_);
v___x_1820_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1822_; 
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 4, v___x_1820_);
v___x_1822_ = v___x_1812_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_env_1803_);
lean_ctor_set(v_reuseFailAlloc_1825_, 1, v_nextMacroScope_1804_);
lean_ctor_set(v_reuseFailAlloc_1825_, 2, v_ngen_1805_);
lean_ctor_set(v_reuseFailAlloc_1825_, 3, v_auxDeclNGen_1806_);
lean_ctor_set(v_reuseFailAlloc_1825_, 4, v___x_1820_);
lean_ctor_set(v_reuseFailAlloc_1825_, 5, v_cache_1807_);
lean_ctor_set(v_reuseFailAlloc_1825_, 6, v_messages_1808_);
lean_ctor_set(v_reuseFailAlloc_1825_, 7, v_infoState_1809_);
lean_ctor_set(v_reuseFailAlloc_1825_, 8, v_snapshotTasks_1810_);
v___x_1822_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = lean_st_ref_put(v___y_1796_, v___x_1822_);
v___x_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1824_, 0, v_traces_1800_);
return v___x_1824_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___boxed(lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1830_);
lean_dec(v___y_1830_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1841_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
return v_res_1854_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(lean_object* v_opts_1855_, lean_object* v_opt_1856_){
_start:
{
lean_object* v_name_1857_; lean_object* v_defValue_1858_; lean_object* v_map_1859_; lean_object* v___x_1860_; 
v_name_1857_ = lean_ctor_get(v_opt_1856_, 0);
v_defValue_1858_ = lean_ctor_get(v_opt_1856_, 1);
v_map_1859_ = lean_ctor_get(v_opts_1855_, 0);
v___x_1860_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1859_, v_name_1857_);
if (lean_obj_tag(v___x_1860_) == 0)
{
uint8_t v___x_1861_; 
v___x_1861_ = lean_unbox(v_defValue_1858_);
return v___x_1861_;
}
else
{
lean_object* v_val_1862_; 
v_val_1862_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_val_1862_);
lean_dec_ref_known(v___x_1860_, 1);
if (lean_obj_tag(v_val_1862_) == 1)
{
uint8_t v_v_1863_; 
v_v_1863_ = lean_ctor_get_uint8(v_val_1862_, 0);
lean_dec_ref_known(v_val_1862_, 0);
return v_v_1863_;
}
else
{
uint8_t v___x_1864_; 
lean_dec(v_val_1862_);
v___x_1864_ = lean_unbox(v_defValue_1858_);
return v___x_1864_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object* v_opts_1865_, lean_object* v_opt_1866_){
_start:
{
uint8_t v_res_1867_; lean_object* v_r_1868_; 
v_res_1867_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_1865_, v_opt_1866_);
lean_dec_ref(v_opt_1866_);
lean_dec_ref(v_opts_1865_);
v_r_1868_ = lean_box(v_res_1867_);
return v_r_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(lean_object* v_cls_1869_, lean_object* v_____do__lift_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_toCold_1881_; lean_object* v_options_1882_; uint8_t v_hasTrace_1883_; 
v_toCold_1881_ = lean_ctor_get(v___y_1878_, 0);
v_options_1882_ = lean_ctor_get(v_toCold_1881_, 2);
v_hasTrace_1883_ = lean_ctor_get_uint8(v_options_1882_, sizeof(void*)*1);
if (v_hasTrace_1883_ == 0)
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_dec(v_cls_1869_);
v___x_1884_ = lean_box(v_hasTrace_1883_);
v___x_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
return v___x_1885_;
}
else
{
lean_object* v___x_1886_; lean_object* v___x_1887_; uint8_t v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1886_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_1887_ = l_Lean_Name_append(v___x_1886_, v_cls_1869_);
v___x_1888_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_1870_, v_options_1882_, v___x_1887_);
lean_dec(v___x_1887_);
v___x_1889_ = lean_box(v___x_1888_);
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
return v___x_1890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0___boxed(lean_object* v_cls_1891_, lean_object* v_____do__lift_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_1891_, v_____do__lift_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v_____do__lift_1892_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1(lean_object* v___x_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_mkAppB(v___x_1904_, v___y_1905_, v___y_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(lean_object* v_val_1908_, lean_object* v_lhs_1909_, lean_object* v_rhs_1910_, lean_object* v_P_1911_, uint8_t v___x_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v___x_1921_; 
lean_inc_ref(v_lhs_1909_);
lean_inc_ref(v_val_1908_);
v___x_1921_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1908_, v_lhs_1909_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v_fst_1923_; lean_object* v_snd_1924_; lean_object* v___x_1925_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
v_fst_1923_ = lean_ctor_get(v_a_1922_, 0);
lean_inc(v_fst_1923_);
v_snd_1924_ = lean_ctor_get(v_a_1922_, 1);
lean_inc(v_snd_1924_);
lean_dec(v_a_1922_);
lean_inc_ref(v_rhs_1910_);
lean_inc_ref(v_val_1908_);
v___x_1925_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1908_, v_rhs_1910_, v_snd_1924_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v_fst_1927_; lean_object* v_snd_1928_; lean_object* v___x_1929_; lean_object* v_a_1930_; lean_object* v_fst_1931_; lean_object* v_snd_1932_; lean_object* v_common_1933_; lean_object* v_x_1934_; lean_object* v_y_1935_; lean_object* v___x_1936_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___x_1925_, 1);
v_fst_1927_ = lean_ctor_get(v_a_1926_, 0);
lean_inc(v_fst_1927_);
v_snd_1928_ = lean_ctor_get(v_a_1926_, 1);
lean_inc(v_snd_1928_);
lean_dec(v_a_1926_);
v___x_1929_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_1923_, v_fst_1927_, v_snd_1928_);
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref(v___x_1929_);
v_fst_1931_ = lean_ctor_get(v_a_1930_, 0);
lean_inc(v_fst_1931_);
v_snd_1932_ = lean_ctor_get(v_a_1930_, 1);
lean_inc(v_snd_1932_);
lean_dec(v_a_1930_);
v_common_1933_ = lean_ctor_get(v_fst_1931_, 0);
lean_inc_ref(v_common_1933_);
v_x_1934_ = lean_ctor_get(v_fst_1931_, 1);
lean_inc_ref(v_x_1934_);
v_y_1935_ = lean_ctor_get(v_fst_1931_, 2);
lean_inc_ref(v_y_1935_);
lean_dec(v_fst_1931_);
lean_inc_ref(v_val_1908_);
v___x_1936_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_1933_, v_val_1908_, v_snd_1932_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
lean_dec_ref(v_common_1933_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v_fst_1938_; lean_object* v_snd_1939_; lean_object* v___x_1940_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref_known(v___x_1936_, 1);
v_fst_1938_ = lean_ctor_get(v_a_1937_, 0);
lean_inc(v_fst_1938_);
v_snd_1939_ = lean_ctor_get(v_a_1937_, 1);
lean_inc(v_snd_1939_);
lean_dec(v_a_1937_);
lean_inc_ref(v_val_1908_);
v___x_1940_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_1934_, v_val_1908_, v_snd_1939_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
lean_dec_ref(v_x_1934_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v_fst_1942_; lean_object* v_snd_1943_; lean_object* v___x_1944_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1940_, 1);
v_fst_1942_ = lean_ctor_get(v_a_1941_, 0);
lean_inc(v_fst_1942_);
v_snd_1943_ = lean_ctor_get(v_a_1941_, 1);
lean_inc(v_snd_1943_);
lean_dec(v_a_1941_);
lean_inc_ref(v_val_1908_);
v___x_1944_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_1935_, v_val_1908_, v_snd_1943_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
lean_dec_ref(v_y_1935_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_2009_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_1947_ = v___x_1944_;
v_isShared_1948_ = v_isSharedCheck_2009_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1944_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_2009_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v_fst_1949_; lean_object* v_snd_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_2008_; 
v_fst_1949_ = lean_ctor_get(v_a_1945_, 0);
v_snd_1950_ = lean_ctor_get(v_a_1945_, 1);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_a_1945_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_1952_ = v_a_1945_;
v_isShared_1953_ = v_isSharedCheck_2008_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_snd_1950_);
lean_inc(v_fst_1949_);
lean_dec(v_a_1945_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_2008_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___x_1998_; lean_object* v___f_1999_; lean_object* v___y_2001_; lean_object* v___x_2005_; 
lean_inc_ref(v_val_1908_);
v___x_1998_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_1908_);
v___f_1999_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_1999_, 0, v___x_1998_);
lean_inc(v_fst_1938_);
lean_inc_ref(v___f_1999_);
v___x_2005_ = l_Option_merge___redArg(v___f_1999_, v_fst_1938_, v_fst_1942_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v___x_2006_; 
lean_inc_ref(v_val_1908_);
v___x_2006_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1908_);
v___y_2001_ = v___x_2006_;
goto v___jp_2000_;
}
else
{
lean_object* v_val_2007_; 
v_val_2007_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_val_2007_);
lean_dec_ref_known(v___x_2005_, 1);
v___y_2001_ = v_val_2007_;
goto v___jp_2000_;
}
v___jp_1954_:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
lean_inc_ref(v_P_1911_);
v___x_1957_ = l_Lean_mkAppB(v_P_1911_, v_lhs_1909_, v_rhs_1910_);
v___x_1958_ = l_Lean_mkAppB(v_P_1911_, v___y_1955_, v___y_1956_);
v___x_1959_ = lean_expr_eqv(v___x_1957_, v___x_1958_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; 
lean_del_object(v___x_1947_);
lean_inc_ref(v___x_1958_);
v___x_1960_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_1957_, v___x_1958_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1962_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref_known(v___x_1960_, 1);
v___x_1962_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1958_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1974_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1965_ = v___x_1962_;
v_isShared_1966_ = v_isSharedCheck_1974_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1974_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1967_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1967_, 0, v_a_1963_);
lean_ctor_set(v___x_1967_, 1, v_a_1961_);
lean_ctor_set_uint8(v___x_1967_, sizeof(void*)*2, v___x_1959_);
lean_ctor_set_uint8(v___x_1967_, sizeof(void*)*2 + 1, v___x_1959_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v___x_1967_);
v___x_1969_ = v___x_1952_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1967_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_snd_1950_);
v___x_1969_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1971_; 
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v___x_1969_);
v___x_1971_ = v___x_1965_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_dec(v_a_1961_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
v_a_1975_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1962_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1962_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec_ref(v___x_1958_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
v_a_1983_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1960_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1960_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
else
{
lean_object* v___x_1991_; lean_object* v___x_1993_; 
lean_dec_ref(v___x_1958_);
lean_dec_ref(v___x_1957_);
v___x_1991_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1991_, 0, v___x_1912_);
lean_ctor_set_uint8(v___x_1991_, 1, v___x_1912_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v___x_1991_);
v___x_1993_ = v___x_1952_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1991_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v_snd_1950_);
v___x_1993_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1995_; 
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1993_);
v___x_1995_ = v___x_1947_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
v___jp_2000_:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Option_merge___redArg(v___f_1999_, v_fst_1938_, v_fst_1949_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v___x_2003_; 
v___x_2003_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1908_);
v___y_1955_ = v___y_2001_;
v___y_1956_ = v___x_2003_;
goto v___jp_1954_;
}
else
{
lean_object* v_val_2004_; 
lean_dec_ref(v_val_1908_);
v_val_2004_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_val_2004_);
lean_dec_ref_known(v___x_2002_, 1);
v___y_1955_ = v___y_2001_;
v___y_1956_ = v_val_2004_;
goto v___jp_1954_;
}
}
}
}
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
lean_dec(v_fst_1942_);
lean_dec(v_fst_1938_);
lean_dec_ref(v_P_1911_);
lean_dec_ref(v_rhs_1910_);
lean_dec_ref(v_lhs_1909_);
lean_dec_ref(v_val_1908_);
v_a_2010_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_1944_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_1944_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec(v_fst_1938_);
lean_dec_ref(v_y_1935_);
lean_dec_ref(v_P_1911_);
lean_dec_ref(v_rhs_1910_);
lean_dec_ref(v_lhs_1909_);
lean_dec_ref(v_val_1908_);
v_a_2018_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_1940_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_1940_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec_ref(v_y_1935_);
lean_dec_ref(v_x_1934_);
lean_dec_ref(v_P_1911_);
lean_dec_ref(v_rhs_1910_);
lean_dec_ref(v_lhs_1909_);
lean_dec_ref(v_val_1908_);
v_a_2026_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_1936_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_1936_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec(v_fst_1923_);
lean_dec_ref(v_P_1911_);
lean_dec_ref(v_rhs_1910_);
lean_dec_ref(v_lhs_1909_);
lean_dec_ref(v_val_1908_);
v_a_2034_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_1925_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_1925_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec_ref(v_P_1911_);
lean_dec_ref(v_rhs_1910_);
lean_dec_ref(v_lhs_1909_);
lean_dec_ref(v_val_1908_);
v_a_2042_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_1921_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_1921_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object* v_val_2050_, lean_object* v_lhs_2051_, lean_object* v_rhs_2052_, lean_object* v_P_2053_, lean_object* v___x_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
uint8_t v___x_187283__boxed_2063_; lean_object* v_res_2064_; 
v___x_187283__boxed_2063_ = lean_unbox(v___x_2054_);
v_res_2064_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(v_val_2050_, v_lhs_2051_, v_rhs_2052_, v_P_2053_, v___x_187283__boxed_2063_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
return v_res_2064_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2066_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_2067_ = l_Lean_stringToMessageData(v___x_2066_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(lean_object* v_x_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1);
v___x_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object* v_x_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(v_x_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
lean_dec(v___y_2082_);
lean_dec_ref(v_x_2081_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object* v_cls_2093_, lean_object* v_msg_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v_ref_2100_; lean_object* v___x_2101_; lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2146_; 
v_ref_2100_ = lean_ctor_get(v___y_2097_, 2);
v___x_2101_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2104_ = v___x_2101_;
v_isShared_2105_ = v_isSharedCheck_2146_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2101_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2146_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v_traceState_2107_; lean_object* v_env_2108_; lean_object* v_nextMacroScope_2109_; lean_object* v_ngen_2110_; lean_object* v_auxDeclNGen_2111_; lean_object* v_cache_2112_; lean_object* v_messages_2113_; lean_object* v_infoState_2114_; lean_object* v_snapshotTasks_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2145_; 
v___x_2106_ = lean_st_ref_take(v___y_2098_);
v_traceState_2107_ = lean_ctor_get(v___x_2106_, 4);
v_env_2108_ = lean_ctor_get(v___x_2106_, 0);
v_nextMacroScope_2109_ = lean_ctor_get(v___x_2106_, 1);
v_ngen_2110_ = lean_ctor_get(v___x_2106_, 2);
v_auxDeclNGen_2111_ = lean_ctor_get(v___x_2106_, 3);
v_cache_2112_ = lean_ctor_get(v___x_2106_, 5);
v_messages_2113_ = lean_ctor_get(v___x_2106_, 6);
v_infoState_2114_ = lean_ctor_get(v___x_2106_, 7);
v_snapshotTasks_2115_ = lean_ctor_get(v___x_2106_, 8);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2117_ = v___x_2106_;
v_isShared_2118_ = v_isSharedCheck_2145_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_snapshotTasks_2115_);
lean_inc(v_infoState_2114_);
lean_inc(v_messages_2113_);
lean_inc(v_cache_2112_);
lean_inc(v_traceState_2107_);
lean_inc(v_auxDeclNGen_2111_);
lean_inc(v_ngen_2110_);
lean_inc(v_nextMacroScope_2109_);
lean_inc(v_env_2108_);
lean_dec(v___x_2106_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2145_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
uint64_t v_tid_2119_; lean_object* v_traces_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2144_; 
v_tid_2119_ = lean_ctor_get_uint64(v_traceState_2107_, sizeof(void*)*1);
v_traces_2120_ = lean_ctor_get(v_traceState_2107_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_traceState_2107_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2122_ = v_traceState_2107_;
v_isShared_2123_ = v_isSharedCheck_2144_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_traces_2120_);
lean_dec(v_traceState_2107_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2144_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; double v___x_2125_; uint8_t v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2124_ = lean_box(0);
v___x_2125_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_2126_ = 0;
v___x_2127_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_2128_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2128_, 0, v_cls_2093_);
lean_ctor_set(v___x_2128_, 1, v___x_2124_);
lean_ctor_set(v___x_2128_, 2, v___x_2127_);
lean_ctor_set_float(v___x_2128_, sizeof(void*)*3, v___x_2125_);
lean_ctor_set_float(v___x_2128_, sizeof(void*)*3 + 8, v___x_2125_);
lean_ctor_set_uint8(v___x_2128_, sizeof(void*)*3 + 16, v___x_2126_);
v___x_2129_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_2130_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2128_);
lean_ctor_set(v___x_2130_, 1, v_a_2102_);
lean_ctor_set(v___x_2130_, 2, v___x_2129_);
lean_inc(v_ref_2100_);
v___x_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2131_, 0, v_ref_2100_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
v___x_2132_ = l_Lean_PersistentArray_push___redArg(v_traces_2120_, v___x_2131_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2132_);
v___x_2134_ = v___x_2122_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2132_);
lean_ctor_set_uint64(v_reuseFailAlloc_2143_, sizeof(void*)*1, v_tid_2119_);
v___x_2134_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2136_; 
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 4, v___x_2134_);
v___x_2136_ = v___x_2117_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_env_2108_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_nextMacroScope_2109_);
lean_ctor_set(v_reuseFailAlloc_2142_, 2, v_ngen_2110_);
lean_ctor_set(v_reuseFailAlloc_2142_, 3, v_auxDeclNGen_2111_);
lean_ctor_set(v_reuseFailAlloc_2142_, 4, v___x_2134_);
lean_ctor_set(v_reuseFailAlloc_2142_, 5, v_cache_2112_);
lean_ctor_set(v_reuseFailAlloc_2142_, 6, v_messages_2113_);
lean_ctor_set(v_reuseFailAlloc_2142_, 7, v_infoState_2114_);
lean_ctor_set(v_reuseFailAlloc_2142_, 8, v_snapshotTasks_2115_);
v___x_2136_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2137_ = lean_st_ref_put(v___y_2098_, v___x_2136_);
v___x_2138_ = lean_box(0);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v___x_2138_);
v___x_2140_ = v___x_2104_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object* v_cls_2147_, lean_object* v_msg_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2147_, v_msg_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
return v_res_2154_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2157_ = l_Lean_stringToMessageData(v___x_2156_);
return v___x_2157_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3(void){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2));
v___x_2160_ = l_Lean_stringToMessageData(v___x_2159_);
return v___x_2160_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4));
v___x_2163_ = l_Lean_stringToMessageData(v___x_2162_);
return v___x_2163_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = lean_box(0);
v___x_2165_ = lean_unsigned_to_nat(16u);
v___x_2166_ = lean_mk_array(v___x_2165_, v___x_2164_);
return v___x_2166_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6);
v___x_2168_ = lean_unsigned_to_nat(0u);
v___x_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
lean_ctor_set(v___x_2169_, 1, v___x_2167_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9));
v___x_2174_ = l_Lean_stringToMessageData(v___x_2173_);
return v___x_2174_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11));
v___x_2177_ = l_Lean_stringToMessageData(v___x_2176_);
return v___x_2177_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14(void){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13));
v___x_2180_ = l_Lean_stringToMessageData(v___x_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(lean_object* v_lhs_2181_, lean_object* v_rhs_2182_, uint8_t v___x_2183_, lean_object* v___f_2184_, lean_object* v_cls_2185_, lean_object* v_P_2186_, lean_object* v_____r_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v___x_2207_; 
lean_inc_ref(v_lhs_2181_);
v___x_2207_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2181_);
if (lean_obj_tag(v___x_2207_) == 1)
{
lean_object* v_val_2208_; lean_object* v___x_2209_; 
v_val_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_val_2208_);
lean_dec_ref_known(v___x_2207_, 1);
lean_inc_ref(v_rhs_2182_);
v___x_2209_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2182_);
if (lean_obj_tag(v___x_2209_) == 1)
{
lean_object* v_val_2210_; uint8_t v___x_2250_; 
v_val_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_val_2210_);
lean_dec_ref_known(v___x_2209_, 1);
v___x_2250_ = lean_expr_eqv(v_val_2208_, v_val_2210_);
if (v___x_2250_ == 0)
{
lean_dec_ref(v_P_2186_);
goto v___jp_2211_;
}
else
{
if (v___x_2183_ == 0)
{
lean_object* v_toCold_2251_; lean_object* v_options_2252_; lean_object* v_inheritedTraceOptions_2253_; uint8_t v_hasTrace_2254_; lean_object* v___x_2255_; lean_object* v___f_2256_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; 
lean_dec(v_val_2210_);
lean_dec_ref(v___f_2184_);
v_toCold_2251_ = lean_ctor_get(v___y_2195_, 0);
v_options_2252_ = lean_ctor_get(v_toCold_2251_, 2);
v_inheritedTraceOptions_2253_ = lean_ctor_get(v_toCold_2251_, 11);
v_hasTrace_2254_ = lean_ctor_get_uint8(v_options_2252_, sizeof(void*)*1);
v___x_2255_ = lean_box(v___x_2183_);
lean_inc(v_val_2208_);
v___f_2256_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 13, 5);
lean_closure_set(v___f_2256_, 0, v_val_2208_);
lean_closure_set(v___f_2256_, 1, v_lhs_2181_);
lean_closure_set(v___f_2256_, 2, v_rhs_2182_);
lean_closure_set(v___f_2256_, 3, v_P_2186_);
lean_closure_set(v___f_2256_, 4, v___x_2255_);
if (v_hasTrace_2254_ == 0)
{
lean_dec(v_cls_2185_);
v___y_2258_ = v___y_2191_;
v___y_2259_ = v___y_2192_;
v___y_2260_ = v___y_2193_;
v___y_2261_ = v___y_2194_;
v___y_2262_ = v___y_2195_;
v___y_2263_ = v___y_2196_;
goto v___jp_2257_;
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2269_; uint8_t v___x_2270_; 
v___x_2268_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2185_);
v___x_2269_ = l_Lean_Name_append(v___x_2268_, v_cls_2185_);
v___x_2270_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2253_, v_options_2252_, v___x_2269_);
lean_dec(v___x_2269_);
if (v___x_2270_ == 0)
{
lean_dec(v_cls_2185_);
v___y_2258_ = v___y_2191_;
v___y_2259_ = v___y_2192_;
v___y_2260_ = v___y_2193_;
v___y_2261_ = v___y_2194_;
v___y_2262_ = v___y_2195_;
v___y_2263_ = v___y_2196_;
goto v___jp_2257_;
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2271_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10);
lean_inc(v_val_2208_);
v___x_2272_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2208_);
v___x_2273_ = l_Lean_MessageData_ofExpr(v___x_2272_);
v___x_2274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2271_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
v___x_2275_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12);
v___x_2276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2274_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2185_, v___x_2276_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_dec_ref_known(v___x_2277_, 1);
v___y_2258_ = v___y_2191_;
v___y_2259_ = v___y_2192_;
v___y_2260_ = v___y_2193_;
v___y_2261_ = v___y_2194_;
v___y_2262_ = v___y_2195_;
v___y_2263_ = v___y_2196_;
goto v___jp_2257_;
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref(v___f_2256_);
lean_dec(v_val_2208_);
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2277_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2277_);
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
}
v___jp_2257_:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2264_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7);
v___x_2265_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8));
v___x_2266_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2266_, 0, v_val_2208_);
lean_ctor_set(v___x_2266_, 1, v___x_2264_);
lean_ctor_set(v___x_2266_, 2, v___x_2265_);
v___x_2267_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___f_2256_, v___x_2266_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
return v___x_2267_;
}
}
else
{
lean_dec_ref(v_P_2186_);
goto v___jp_2211_;
}
}
v___jp_2211_:
{
lean_object* v_toCold_2212_; lean_object* v_inheritedTraceOptions_2213_; lean_object* v___x_2214_; 
v_toCold_2212_ = lean_ctor_get(v___y_2195_, 0);
v_inheritedTraceOptions_2213_ = lean_ctor_get(v_toCold_2212_, 11);
lean_inc(v___y_2196_);
lean_inc_ref(v___y_2195_);
lean_inc(v___y_2194_);
lean_inc_ref(v___y_2193_);
lean_inc(v___y_2192_);
lean_inc_ref(v___y_2191_);
lean_inc(v___y_2190_);
lean_inc_ref(v___y_2189_);
lean_inc(v___y_2188_);
lean_inc_ref(v_inheritedTraceOptions_2213_);
v___x_2214_ = lean_apply_11(v___f_2184_, v_inheritedTraceOptions_2213_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, lean_box(0));
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; uint8_t v___x_2216_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref_known(v___x_2214_, 1);
v___x_2216_ = lean_unbox(v_a_2215_);
lean_dec(v_a_2215_);
if (v___x_2216_ == 0)
{
lean_dec(v_val_2210_);
lean_dec(v_val_2208_);
lean_dec(v_cls_2185_);
lean_dec_ref(v_rhs_2182_);
lean_dec_ref(v_lhs_2181_);
goto v___jp_2198_;
}
else
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2217_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1);
v___x_2218_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2208_);
v___x_2219_ = l_Lean_MessageData_ofExpr(v___x_2218_);
v___x_2220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2217_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
v___x_2221_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3);
v___x_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2220_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = l_Lean_indentExpr(v_lhs_2181_);
v___x_2224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2222_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
v___x_2225_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5);
v___x_2226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2224_);
lean_ctor_set(v___x_2226_, 1, v___x_2225_);
v___x_2227_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2210_);
v___x_2228_ = l_Lean_MessageData_ofExpr(v___x_2227_);
v___x_2229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2226_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
v___x_2230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
lean_ctor_set(v___x_2230_, 1, v___x_2221_);
v___x_2231_ = l_Lean_indentExpr(v_rhs_2182_);
v___x_2232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2230_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
v___x_2233_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2185_, v___x_2232_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_dec_ref_known(v___x_2233_, 1);
goto v___jp_2198_;
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2233_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2233_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
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
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_dec(v_val_2210_);
lean_dec(v_val_2208_);
lean_dec(v_cls_2185_);
lean_dec_ref(v_rhs_2182_);
lean_dec_ref(v_lhs_2181_);
v_a_2242_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2214_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2214_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
}
else
{
lean_object* v_toCold_2286_; lean_object* v_inheritedTraceOptions_2287_; lean_object* v___x_2288_; 
lean_dec(v___x_2209_);
lean_dec(v_val_2208_);
lean_dec_ref(v_P_2186_);
lean_dec_ref(v_lhs_2181_);
v_toCold_2286_ = lean_ctor_get(v___y_2195_, 0);
v_inheritedTraceOptions_2287_ = lean_ctor_get(v_toCold_2286_, 11);
lean_inc(v___y_2196_);
lean_inc_ref(v___y_2195_);
lean_inc(v___y_2194_);
lean_inc_ref(v___y_2193_);
lean_inc(v___y_2192_);
lean_inc_ref(v___y_2191_);
lean_inc(v___y_2190_);
lean_inc_ref(v___y_2189_);
lean_inc(v___y_2188_);
lean_inc_ref(v_inheritedTraceOptions_2287_);
v___x_2288_ = lean_apply_11(v___f_2184_, v_inheritedTraceOptions_2287_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, lean_box(0));
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; uint8_t v___x_2290_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2289_);
lean_dec_ref_known(v___x_2288_, 1);
v___x_2290_ = lean_unbox(v_a_2289_);
lean_dec(v_a_2289_);
if (v___x_2290_ == 0)
{
lean_dec(v_cls_2185_);
lean_dec_ref(v_rhs_2182_);
goto v___jp_2201_;
}
else
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2291_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_2292_ = l_Lean_indentExpr(v_rhs_2182_);
v___x_2293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2185_, v___x_2293_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_dec_ref_known(v___x_2294_, 1);
goto v___jp_2201_;
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
lean_dec(v_cls_2185_);
lean_dec_ref(v_rhs_2182_);
v_a_2303_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2288_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2288_);
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
lean_object* v_toCold_2311_; lean_object* v_inheritedTraceOptions_2312_; lean_object* v___x_2313_; 
lean_dec(v___x_2207_);
lean_dec_ref(v_P_2186_);
lean_dec_ref(v_rhs_2182_);
v_toCold_2311_ = lean_ctor_get(v___y_2195_, 0);
v_inheritedTraceOptions_2312_ = lean_ctor_get(v_toCold_2311_, 11);
lean_inc(v___y_2196_);
lean_inc_ref(v___y_2195_);
lean_inc(v___y_2194_);
lean_inc_ref(v___y_2193_);
lean_inc(v___y_2192_);
lean_inc_ref(v___y_2191_);
lean_inc(v___y_2190_);
lean_inc_ref(v___y_2189_);
lean_inc(v___y_2188_);
lean_inc_ref(v_inheritedTraceOptions_2312_);
v___x_2313_ = lean_apply_11(v___f_2184_, v_inheritedTraceOptions_2312_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, lean_box(0));
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; uint8_t v___x_2315_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref_known(v___x_2313_, 1);
v___x_2315_ = lean_unbox(v_a_2314_);
lean_dec(v_a_2314_);
if (v___x_2315_ == 0)
{
lean_dec(v_cls_2185_);
lean_dec_ref(v_lhs_2181_);
goto v___jp_2204_;
}
else
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2316_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_2317_ = l_Lean_indentExpr(v_lhs_2181_);
v___x_2318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2316_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v___x_2319_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2185_, v___x_2318_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_dec_ref_known(v___x_2319_, 1);
goto v___jp_2204_;
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2319_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2319_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec(v_cls_2185_);
lean_dec_ref(v_lhs_2181_);
v_a_2328_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2313_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2313_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
v___jp_2198_:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2199_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2199_, 0, v___x_2183_);
lean_ctor_set_uint8(v___x_2199_, 1, v___x_2183_);
v___x_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
return v___x_2200_;
}
v___jp_2201_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2202_, 0, v___x_2183_);
lean_ctor_set_uint8(v___x_2202_, 1, v___x_2183_);
v___x_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
return v___x_2203_;
}
v___jp_2204_:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2205_, 0, v___x_2183_);
lean_ctor_set_uint8(v___x_2205_, 1, v___x_2183_);
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
return v___x_2206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___boxed(lean_object** _args){
lean_object* v_lhs_2336_ = _args[0];
lean_object* v_rhs_2337_ = _args[1];
lean_object* v___x_2338_ = _args[2];
lean_object* v___f_2339_ = _args[3];
lean_object* v_cls_2340_ = _args[4];
lean_object* v_P_2341_ = _args[5];
lean_object* v_____r_2342_ = _args[6];
lean_object* v___y_2343_ = _args[7];
lean_object* v___y_2344_ = _args[8];
lean_object* v___y_2345_ = _args[9];
lean_object* v___y_2346_ = _args[10];
lean_object* v___y_2347_ = _args[11];
lean_object* v___y_2348_ = _args[12];
lean_object* v___y_2349_ = _args[13];
lean_object* v___y_2350_ = _args[14];
lean_object* v___y_2351_ = _args[15];
lean_object* v___y_2352_ = _args[16];
_start:
{
uint8_t v___x_187767__boxed_2353_; lean_object* v_res_2354_; 
v___x_187767__boxed_2353_ = lean_unbox(v___x_2338_);
v_res_2354_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2336_, v_rhs_2337_, v___x_187767__boxed_2353_, v___f_2339_, v_cls_2340_, v_P_2341_, v_____r_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(lean_object* v_val_2355_, lean_object* v_lhs_2356_, lean_object* v_rhs_2357_, lean_object* v_P_2358_, uint8_t v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v___x_2368_; 
lean_inc_ref(v_lhs_2356_);
lean_inc_ref(v_val_2355_);
v___x_2368_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_2355_, v_lhs_2356_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v_fst_2370_; lean_object* v_snd_2371_; lean_object* v___x_2372_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2369_);
lean_dec_ref_known(v___x_2368_, 1);
v_fst_2370_ = lean_ctor_get(v_a_2369_, 0);
lean_inc(v_fst_2370_);
v_snd_2371_ = lean_ctor_get(v_a_2369_, 1);
lean_inc(v_snd_2371_);
lean_dec(v_a_2369_);
lean_inc_ref(v_rhs_2357_);
lean_inc_ref(v_val_2355_);
v___x_2372_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_2355_, v_rhs_2357_, v_snd_2371_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v_fst_2374_; lean_object* v_snd_2375_; lean_object* v___x_2376_; lean_object* v_a_2377_; lean_object* v_fst_2378_; lean_object* v_snd_2379_; lean_object* v_common_2380_; lean_object* v_x_2381_; lean_object* v_y_2382_; lean_object* v___x_2383_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref_known(v___x_2372_, 1);
v_fst_2374_ = lean_ctor_get(v_a_2373_, 0);
lean_inc(v_fst_2374_);
v_snd_2375_ = lean_ctor_get(v_a_2373_, 1);
lean_inc(v_snd_2375_);
lean_dec(v_a_2373_);
v___x_2376_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_2370_, v_fst_2374_, v_snd_2375_);
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
lean_dec_ref(v___x_2376_);
v_fst_2378_ = lean_ctor_get(v_a_2377_, 0);
lean_inc(v_fst_2378_);
v_snd_2379_ = lean_ctor_get(v_a_2377_, 1);
lean_inc(v_snd_2379_);
lean_dec(v_a_2377_);
v_common_2380_ = lean_ctor_get(v_fst_2378_, 0);
lean_inc_ref(v_common_2380_);
v_x_2381_ = lean_ctor_get(v_fst_2378_, 1);
lean_inc_ref(v_x_2381_);
v_y_2382_ = lean_ctor_get(v_fst_2378_, 2);
lean_inc_ref(v_y_2382_);
lean_dec(v_fst_2378_);
lean_inc_ref(v_val_2355_);
v___x_2383_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_2380_, v_val_2355_, v_snd_2379_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
lean_dec_ref(v_common_2380_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; lean_object* v_fst_2385_; lean_object* v_snd_2386_; lean_object* v___x_2387_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref_known(v___x_2383_, 1);
v_fst_2385_ = lean_ctor_get(v_a_2384_, 0);
lean_inc(v_fst_2385_);
v_snd_2386_ = lean_ctor_get(v_a_2384_, 1);
lean_inc(v_snd_2386_);
lean_dec(v_a_2384_);
lean_inc_ref(v_val_2355_);
v___x_2387_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_2381_, v_val_2355_, v_snd_2386_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
lean_dec_ref(v_x_2381_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v_fst_2389_; lean_object* v_snd_2390_; lean_object* v___x_2391_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2387_, 1);
v_fst_2389_ = lean_ctor_get(v_a_2388_, 0);
lean_inc(v_fst_2389_);
v_snd_2390_ = lean_ctor_get(v_a_2388_, 1);
lean_inc(v_snd_2390_);
lean_dec(v_a_2388_);
lean_inc_ref(v_val_2355_);
v___x_2391_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_2382_, v_val_2355_, v_snd_2390_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
lean_dec_ref(v_y_2382_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2456_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2394_ = v___x_2391_;
v_isShared_2395_ = v_isSharedCheck_2456_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2391_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2456_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v_fst_2396_; lean_object* v_snd_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2455_; 
v_fst_2396_ = lean_ctor_get(v_a_2392_, 0);
v_snd_2397_ = lean_ctor_get(v_a_2392_, 1);
v_isSharedCheck_2455_ = !lean_is_exclusive(v_a_2392_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2399_ = v_a_2392_;
v_isShared_2400_ = v_isSharedCheck_2455_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_snd_2397_);
lean_inc(v_fst_2396_);
lean_dec(v_a_2392_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2455_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___x_2445_; lean_object* v___f_2446_; lean_object* v___y_2448_; lean_object* v___x_2452_; 
lean_inc_ref(v_val_2355_);
v___x_2445_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2355_);
v___f_2446_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_2446_, 0, v___x_2445_);
lean_inc(v_fst_2385_);
lean_inc_ref(v___f_2446_);
v___x_2452_ = l_Option_merge___redArg(v___f_2446_, v_fst_2385_, v_fst_2389_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v___x_2453_; 
lean_inc_ref(v_val_2355_);
v___x_2453_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_2355_);
v___y_2448_ = v___x_2453_;
goto v___jp_2447_;
}
else
{
lean_object* v_val_2454_; 
v_val_2454_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_val_2454_);
lean_dec_ref_known(v___x_2452_, 1);
v___y_2448_ = v_val_2454_;
goto v___jp_2447_;
}
v___jp_2401_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; 
lean_inc_ref(v_P_2358_);
v___x_2404_ = l_Lean_mkAppB(v_P_2358_, v_lhs_2356_, v_rhs_2357_);
v___x_2405_ = l_Lean_mkAppB(v_P_2358_, v___y_2402_, v___y_2403_);
v___x_2406_ = lean_expr_eqv(v___x_2404_, v___x_2405_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; 
lean_del_object(v___x_2394_);
lean_inc_ref(v___x_2405_);
v___x_2407_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_2404_, v___x_2405_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2409_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2407_, 1);
v___x_2409_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2405_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2421_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2412_ = v___x_2409_;
v_isShared_2413_ = v_isSharedCheck_2421_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2409_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2421_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v___x_2416_; 
v___x_2414_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2414_, 0, v_a_2410_);
lean_ctor_set(v___x_2414_, 1, v_a_2408_);
lean_ctor_set_uint8(v___x_2414_, sizeof(void*)*2, v___x_2406_);
lean_ctor_set_uint8(v___x_2414_, sizeof(void*)*2 + 1, v___x_2406_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v___x_2414_);
v___x_2416_ = v___x_2399_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_snd_2397_);
v___x_2416_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2418_; 
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2416_);
v___x_2418_ = v___x_2412_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2416_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
lean_dec(v_a_2408_);
lean_del_object(v___x_2399_);
lean_dec(v_snd_2397_);
v_a_2422_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2409_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2409_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec_ref(v___x_2405_);
lean_del_object(v___x_2399_);
lean_dec(v_snd_2397_);
v_a_2430_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2407_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2407_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
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
else
{
lean_object* v___x_2438_; lean_object* v___x_2440_; 
lean_dec_ref(v___x_2405_);
lean_dec_ref(v___x_2404_);
v___x_2438_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2438_, 0, v___y_2359_);
lean_ctor_set_uint8(v___x_2438_, 1, v___y_2359_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v___x_2438_);
v___x_2440_ = v___x_2399_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2438_);
lean_ctor_set(v_reuseFailAlloc_2444_, 1, v_snd_2397_);
v___x_2440_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
lean_object* v___x_2442_; 
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 0, v___x_2440_);
v___x_2442_ = v___x_2394_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2440_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
v___jp_2447_:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Option_merge___redArg(v___f_2446_, v_fst_2385_, v_fst_2396_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_2355_);
v___y_2402_ = v___y_2448_;
v___y_2403_ = v___x_2450_;
goto v___jp_2401_;
}
else
{
lean_object* v_val_2451_; 
lean_dec_ref(v_val_2355_);
v_val_2451_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_val_2451_);
lean_dec_ref_known(v___x_2449_, 1);
v___y_2402_ = v___y_2448_;
v___y_2403_ = v_val_2451_;
goto v___jp_2401_;
}
}
}
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_dec(v_fst_2389_);
lean_dec(v_fst_2385_);
lean_dec_ref(v_P_2358_);
lean_dec_ref(v_rhs_2357_);
lean_dec_ref(v_lhs_2356_);
lean_dec_ref(v_val_2355_);
v_a_2457_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2391_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2391_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec(v_fst_2385_);
lean_dec_ref(v_y_2382_);
lean_dec_ref(v_P_2358_);
lean_dec_ref(v_rhs_2357_);
lean_dec_ref(v_lhs_2356_);
lean_dec_ref(v_val_2355_);
v_a_2465_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2387_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2387_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec_ref(v_y_2382_);
lean_dec_ref(v_x_2381_);
lean_dec_ref(v_P_2358_);
lean_dec_ref(v_rhs_2357_);
lean_dec_ref(v_lhs_2356_);
lean_dec_ref(v_val_2355_);
v_a_2473_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2383_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2383_);
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
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec(v_fst_2370_);
lean_dec_ref(v_P_2358_);
lean_dec_ref(v_rhs_2357_);
lean_dec_ref(v_lhs_2356_);
lean_dec_ref(v_val_2355_);
v_a_2481_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2372_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2372_);
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
else
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
lean_dec_ref(v_P_2358_);
lean_dec_ref(v_rhs_2357_);
lean_dec_ref(v_lhs_2356_);
lean_dec_ref(v_val_2355_);
v_a_2489_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2368_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2368_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed(lean_object* v_val_2497_, lean_object* v_lhs_2498_, lean_object* v_rhs_2499_, lean_object* v_P_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
uint8_t v___y_188096__boxed_2510_; lean_object* v_res_2511_; 
v___y_188096__boxed_2510_ = lean_unbox(v___y_2501_);
v_res_2511_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(v_val_2497_, v_lhs_2498_, v_rhs_2499_, v_P_2500_, v___y_188096__boxed_2510_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(lean_object* v_lhs_2512_, lean_object* v_rhs_2513_, lean_object* v_P_2514_, lean_object* v_cls_2515_, uint8_t v___x_2516_, lean_object* v___f_2517_, uint8_t v___x_2518_, lean_object* v_____r_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v___x_2536_; 
lean_inc_ref(v_lhs_2512_);
v___x_2536_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2512_);
if (lean_obj_tag(v___x_2536_) == 1)
{
lean_object* v_val_2537_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; uint8_t v___y_2551_; lean_object* v___x_2576_; 
v_val_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_val_2537_);
lean_dec_ref_known(v___x_2536_, 1);
lean_inc_ref(v_rhs_2513_);
v___x_2576_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2513_);
if (lean_obj_tag(v___x_2576_) == 1)
{
lean_object* v_val_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2625_; 
v_val_2577_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2579_ = v___x_2576_;
v_isShared_2580_ = v_isSharedCheck_2625_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_val_2577_);
lean_dec(v___x_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2625_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
uint8_t v___x_2581_; 
v___x_2581_ = lean_expr_eqv(v_val_2537_, v_val_2577_);
if (v___x_2581_ == 0)
{
if (v___x_2516_ == 0)
{
lean_del_object(v___x_2579_);
lean_dec(v_val_2577_);
lean_dec_ref(v___f_2517_);
v___y_2551_ = v___x_2516_;
goto v___jp_2550_;
}
else
{
lean_object* v_toCold_2587_; lean_object* v_inheritedTraceOptions_2588_; lean_object* v___x_2589_; 
lean_dec_ref(v_P_2514_);
v_toCold_2587_ = lean_ctor_get(v___y_2527_, 0);
v_inheritedTraceOptions_2588_ = lean_ctor_get(v_toCold_2587_, 11);
lean_inc(v___y_2528_);
lean_inc_ref(v___y_2527_);
lean_inc(v___y_2526_);
lean_inc_ref(v___y_2525_);
lean_inc(v___y_2524_);
lean_inc_ref(v___y_2523_);
lean_inc(v___y_2522_);
lean_inc_ref(v___y_2521_);
lean_inc(v___y_2520_);
lean_inc_ref(v_inheritedTraceOptions_2588_);
v___x_2589_ = lean_apply_11(v___f_2517_, v_inheritedTraceOptions_2588_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, lean_box(0));
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; uint8_t v___x_2591_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref_known(v___x_2589_, 1);
v___x_2591_ = lean_unbox(v_a_2590_);
lean_dec(v_a_2590_);
if (v___x_2591_ == 0)
{
lean_dec(v_val_2577_);
lean_dec(v_val_2537_);
lean_dec(v_cls_2515_);
lean_dec_ref(v_rhs_2513_);
lean_dec_ref(v_lhs_2512_);
goto v___jp_2582_;
}
else
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2592_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1);
v___x_2593_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2537_);
v___x_2594_ = l_Lean_MessageData_ofExpr(v___x_2593_);
v___x_2595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2592_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
v___x_2596_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3);
v___x_2597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2595_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v___x_2598_ = l_Lean_indentExpr(v_lhs_2512_);
v___x_2599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2597_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5);
v___x_2601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2599_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
v___x_2602_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2577_);
v___x_2603_ = l_Lean_MessageData_ofExpr(v___x_2602_);
v___x_2604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2601_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
lean_ctor_set(v___x_2605_, 1, v___x_2596_);
v___x_2606_ = l_Lean_indentExpr(v_rhs_2513_);
v___x_2607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2605_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2515_, v___x_2607_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_dec_ref_known(v___x_2608_, 1);
goto v___jp_2582_;
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_del_object(v___x_2579_);
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2608_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2608_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_del_object(v___x_2579_);
lean_dec(v_val_2577_);
lean_dec(v_val_2537_);
lean_dec(v_cls_2515_);
lean_dec_ref(v_rhs_2513_);
lean_dec_ref(v_lhs_2512_);
v_a_2617_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2589_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2589_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
else
{
lean_del_object(v___x_2579_);
lean_dec(v_val_2577_);
lean_dec_ref(v___f_2517_);
v___y_2551_ = v___x_2518_;
goto v___jp_2550_;
}
v___jp_2582_:
{
lean_object* v___x_2583_; lean_object* v___x_2585_; 
v___x_2583_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2583_, 0, v___x_2581_);
lean_ctor_set_uint8(v___x_2583_, 1, v___x_2581_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set_tag(v___x_2579_, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2583_);
v___x_2585_ = v___x_2579_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
else
{
lean_object* v_toCold_2626_; lean_object* v_inheritedTraceOptions_2627_; lean_object* v___x_2628_; 
lean_dec(v___x_2576_);
lean_dec(v_val_2537_);
lean_dec_ref(v_P_2514_);
lean_dec_ref(v_lhs_2512_);
v_toCold_2626_ = lean_ctor_get(v___y_2527_, 0);
v_inheritedTraceOptions_2627_ = lean_ctor_get(v_toCold_2626_, 11);
lean_inc(v___y_2528_);
lean_inc_ref(v___y_2527_);
lean_inc(v___y_2526_);
lean_inc_ref(v___y_2525_);
lean_inc(v___y_2524_);
lean_inc_ref(v___y_2523_);
lean_inc(v___y_2522_);
lean_inc_ref(v___y_2521_);
lean_inc(v___y_2520_);
lean_inc_ref(v_inheritedTraceOptions_2627_);
v___x_2628_ = lean_apply_11(v___f_2517_, v_inheritedTraceOptions_2627_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, lean_box(0));
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; uint8_t v___x_2630_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref_known(v___x_2628_, 1);
v___x_2630_ = lean_unbox(v_a_2629_);
lean_dec(v_a_2629_);
if (v___x_2630_ == 0)
{
lean_dec(v_cls_2515_);
lean_dec_ref(v_rhs_2513_);
goto v___jp_2530_;
}
else
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2631_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_2632_ = l_Lean_indentExpr(v_rhs_2513_);
v___x_2633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2631_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
v___x_2634_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2515_, v___x_2633_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_dec_ref_known(v___x_2634_, 1);
goto v___jp_2530_;
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2634_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2634_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec(v_cls_2515_);
lean_dec_ref(v_rhs_2513_);
v_a_2643_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2628_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2628_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
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
v___jp_2538_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2546_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7);
v___x_2547_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8));
v___x_2548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2548_, 0, v_val_2537_);
lean_ctor_set(v___x_2548_, 1, v___x_2546_);
lean_ctor_set(v___x_2548_, 2, v___x_2547_);
v___x_2549_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___y_2539_, v___x_2548_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
return v___x_2549_;
}
v___jp_2550_:
{
lean_object* v_toCold_2552_; lean_object* v_options_2553_; lean_object* v_inheritedTraceOptions_2554_; uint8_t v_hasTrace_2555_; lean_object* v___x_2556_; lean_object* v___f_2557_; 
v_toCold_2552_ = lean_ctor_get(v___y_2527_, 0);
v_options_2553_ = lean_ctor_get(v_toCold_2552_, 2);
v_inheritedTraceOptions_2554_ = lean_ctor_get(v_toCold_2552_, 11);
v_hasTrace_2555_ = lean_ctor_get_uint8(v_options_2553_, sizeof(void*)*1);
v___x_2556_ = lean_box(v___y_2551_);
lean_inc(v_val_2537_);
v___f_2557_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed), 13, 5);
lean_closure_set(v___f_2557_, 0, v_val_2537_);
lean_closure_set(v___f_2557_, 1, v_lhs_2512_);
lean_closure_set(v___f_2557_, 2, v_rhs_2513_);
lean_closure_set(v___f_2557_, 3, v_P_2514_);
lean_closure_set(v___f_2557_, 4, v___x_2556_);
if (v_hasTrace_2555_ == 0)
{
lean_dec(v_cls_2515_);
v___y_2539_ = v___f_2557_;
v___y_2540_ = v___y_2523_;
v___y_2541_ = v___y_2524_;
v___y_2542_ = v___y_2525_;
v___y_2543_ = v___y_2526_;
v___y_2544_ = v___y_2527_;
v___y_2545_ = v___y_2528_;
goto v___jp_2538_;
}
else
{
lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; 
v___x_2558_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2515_);
v___x_2559_ = l_Lean_Name_append(v___x_2558_, v_cls_2515_);
v___x_2560_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2554_, v_options_2553_, v___x_2559_);
lean_dec(v___x_2559_);
if (v___x_2560_ == 0)
{
lean_dec(v_cls_2515_);
v___y_2539_ = v___f_2557_;
v___y_2540_ = v___y_2523_;
v___y_2541_ = v___y_2524_;
v___y_2542_ = v___y_2525_;
v___y_2543_ = v___y_2526_;
v___y_2544_ = v___y_2527_;
v___y_2545_ = v___y_2528_;
goto v___jp_2538_;
}
else
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2561_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10);
lean_inc(v_val_2537_);
v___x_2562_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2537_);
v___x_2563_ = l_Lean_MessageData_ofExpr(v___x_2562_);
v___x_2564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2561_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
v___x_2565_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12);
v___x_2566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2564_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2515_, v___x_2566_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_dec_ref_known(v___x_2567_, 1);
v___y_2539_ = v___f_2557_;
v___y_2540_ = v___y_2523_;
v___y_2541_ = v___y_2524_;
v___y_2542_ = v___y_2525_;
v___y_2543_ = v___y_2526_;
v___y_2544_ = v___y_2527_;
v___y_2545_ = v___y_2528_;
goto v___jp_2538_;
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_dec_ref(v___f_2557_);
lean_dec(v_val_2537_);
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2567_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2567_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_2651_; lean_object* v_inheritedTraceOptions_2652_; lean_object* v___x_2653_; 
lean_dec(v___x_2536_);
lean_dec_ref(v_P_2514_);
lean_dec_ref(v_rhs_2513_);
v_toCold_2651_ = lean_ctor_get(v___y_2527_, 0);
v_inheritedTraceOptions_2652_ = lean_ctor_get(v_toCold_2651_, 11);
lean_inc(v___y_2528_);
lean_inc_ref(v___y_2527_);
lean_inc(v___y_2526_);
lean_inc_ref(v___y_2525_);
lean_inc(v___y_2524_);
lean_inc_ref(v___y_2523_);
lean_inc(v___y_2522_);
lean_inc_ref(v___y_2521_);
lean_inc(v___y_2520_);
lean_inc_ref(v_inheritedTraceOptions_2652_);
v___x_2653_ = lean_apply_11(v___f_2517_, v_inheritedTraceOptions_2652_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, lean_box(0));
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; uint8_t v___x_2655_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___x_2653_, 1);
v___x_2655_ = lean_unbox(v_a_2654_);
lean_dec(v_a_2654_);
if (v___x_2655_ == 0)
{
lean_dec(v_cls_2515_);
lean_dec_ref(v_lhs_2512_);
goto v___jp_2533_;
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2656_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_2657_ = l_Lean_indentExpr(v_lhs_2512_);
v___x_2658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2656_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
v___x_2659_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2515_, v___x_2658_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_dec_ref_known(v___x_2659_, 1);
goto v___jp_2533_;
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2659_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2659_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec(v_cls_2515_);
lean_dec_ref(v_lhs_2512_);
v_a_2668_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2653_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2653_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
v___jp_2530_:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2531_, 0, v___x_2518_);
lean_ctor_set_uint8(v___x_2531_, 1, v___x_2518_);
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
return v___x_2532_;
}
v___jp_2533_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2534_, 0, v___x_2518_);
lean_ctor_set_uint8(v___x_2534_, 1, v___x_2518_);
v___x_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
return v___x_2535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___boxed(lean_object** _args){
lean_object* v_lhs_2676_ = _args[0];
lean_object* v_rhs_2677_ = _args[1];
lean_object* v_P_2678_ = _args[2];
lean_object* v_cls_2679_ = _args[3];
lean_object* v___x_2680_ = _args[4];
lean_object* v___f_2681_ = _args[5];
lean_object* v___x_2682_ = _args[6];
lean_object* v_____r_2683_ = _args[7];
lean_object* v___y_2684_ = _args[8];
lean_object* v___y_2685_ = _args[9];
lean_object* v___y_2686_ = _args[10];
lean_object* v___y_2687_ = _args[11];
lean_object* v___y_2688_ = _args[12];
lean_object* v___y_2689_ = _args[13];
lean_object* v___y_2690_ = _args[14];
lean_object* v___y_2691_ = _args[15];
lean_object* v___y_2692_ = _args[16];
lean_object* v___y_2693_ = _args[17];
_start:
{
uint8_t v___x_188418__boxed_2694_; uint8_t v___x_188420__boxed_2695_; lean_object* v_res_2696_; 
v___x_188418__boxed_2694_ = lean_unbox(v___x_2680_);
v___x_188420__boxed_2695_ = lean_unbox(v___x_2682_);
v_res_2696_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2676_, v_rhs_2677_, v_P_2678_, v_cls_2679_, v___x_188418__boxed_2694_, v___f_2681_, v___x_188420__boxed_2695_, v_____r_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
return v_res_2696_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(lean_object* v_e_2697_){
_start:
{
if (lean_obj_tag(v_e_2697_) == 0)
{
uint8_t v___x_2698_; 
v___x_2698_ = 2;
return v___x_2698_;
}
else
{
uint8_t v___x_2699_; 
v___x_2699_ = 0;
return v___x_2699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5___boxed(lean_object* v_e_2700_){
_start:
{
uint8_t v_res_2701_; lean_object* v_r_2702_; 
v_res_2701_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_e_2700_);
lean_dec_ref(v_e_2700_);
v_r_2702_ = lean_box(v_res_2701_);
return v_r_2702_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(lean_object* v_x_2703_){
_start:
{
if (lean_obj_tag(v_x_2703_) == 0)
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
v_a_2705_ = lean_ctor_get(v_x_2703_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_x_2703_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v_x_2703_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v_x_2703_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
lean_ctor_set_tag(v___x_2707_, 1);
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
v_a_2713_ = lean_ctor_get(v_x_2703_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_x_2703_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v_x_2703_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v_x_2703_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
lean_ctor_set_tag(v___x_2715_, 0);
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg___boxed(lean_object* v_x_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_2721_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(lean_object* v_opts_2724_, lean_object* v_opt_2725_){
_start:
{
lean_object* v_name_2726_; lean_object* v_defValue_2727_; lean_object* v_map_2728_; lean_object* v___x_2729_; 
v_name_2726_ = lean_ctor_get(v_opt_2725_, 0);
v_defValue_2727_ = lean_ctor_get(v_opt_2725_, 1);
v_map_2728_ = lean_ctor_get(v_opts_2724_, 0);
v___x_2729_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2728_, v_name_2726_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_inc(v_defValue_2727_);
return v_defValue_2727_;
}
else
{
lean_object* v_val_2730_; 
v_val_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_val_2730_);
lean_dec_ref_known(v___x_2729_, 1);
if (lean_obj_tag(v_val_2730_) == 3)
{
lean_object* v_v_2731_; 
v_v_2731_ = lean_ctor_get(v_val_2730_, 0);
lean_inc(v_v_2731_);
lean_dec_ref_known(v_val_2730_, 1);
return v_v_2731_;
}
else
{
lean_dec(v_val_2730_);
lean_inc(v_defValue_2727_);
return v_defValue_2727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6___boxed(lean_object* v_opts_2732_, lean_object* v_opt_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2732_, v_opt_2733_);
lean_dec_ref(v_opt_2733_);
lean_dec_ref(v_opts_2732_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(size_t v_sz_2735_, size_t v_i_2736_, lean_object* v_bs_2737_){
_start:
{
uint8_t v___x_2738_; 
v___x_2738_ = lean_usize_dec_lt(v_i_2736_, v_sz_2735_);
if (v___x_2738_ == 0)
{
return v_bs_2737_;
}
else
{
lean_object* v_v_2739_; lean_object* v_msg_2740_; lean_object* v___x_2741_; lean_object* v_bs_x27_2742_; size_t v___x_2743_; size_t v___x_2744_; lean_object* v___x_2745_; 
v_v_2739_ = lean_array_uget_borrowed(v_bs_2737_, v_i_2736_);
v_msg_2740_ = lean_ctor_get(v_v_2739_, 1);
lean_inc_ref(v_msg_2740_);
v___x_2741_ = lean_unsigned_to_nat(0u);
v_bs_x27_2742_ = lean_array_uset(v_bs_2737_, v_i_2736_, v___x_2741_);
v___x_2743_ = ((size_t)1ULL);
v___x_2744_ = lean_usize_add(v_i_2736_, v___x_2743_);
v___x_2745_ = lean_array_uset(v_bs_x27_2742_, v_i_2736_, v_msg_2740_);
v_i_2736_ = v___x_2744_;
v_bs_2737_ = v___x_2745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2747_, lean_object* v_i_2748_, lean_object* v_bs_2749_){
_start:
{
size_t v_sz_boxed_2750_; size_t v_i_boxed_2751_; lean_object* v_res_2752_; 
v_sz_boxed_2750_ = lean_unbox_usize(v_sz_2747_);
lean_dec(v_sz_2747_);
v_i_boxed_2751_ = lean_unbox_usize(v_i_2748_);
lean_dec(v_i_2748_);
v_res_2752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_boxed_2750_, v_i_boxed_2751_, v_bs_2749_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(lean_object* v_oldTraces_2753_, lean_object* v_data_2754_, lean_object* v_ref_2755_, lean_object* v_msg_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_toCold_2762_; lean_object* v_currRecDepth_2763_; lean_object* v_ref_2764_; uint8_t v_diag_2765_; uint8_t v_suppressElabErrors_2766_; lean_object* v___x_2767_; lean_object* v_traceState_2768_; lean_object* v_traces_2769_; lean_object* v_ref_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; size_t v_sz_2773_; size_t v___x_2774_; lean_object* v___x_2775_; lean_object* v_msg_2776_; lean_object* v___x_2777_; lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2815_; 
v_toCold_2762_ = lean_ctor_get(v___y_2759_, 0);
v_currRecDepth_2763_ = lean_ctor_get(v___y_2759_, 1);
v_ref_2764_ = lean_ctor_get(v___y_2759_, 2);
v_diag_2765_ = lean_ctor_get_uint8(v___y_2759_, sizeof(void*)*3);
v_suppressElabErrors_2766_ = lean_ctor_get_uint8(v___y_2759_, sizeof(void*)*3 + 1);
v___x_2767_ = lean_st_ref_get(v___y_2760_);
v_traceState_2768_ = lean_ctor_get(v___x_2767_, 4);
lean_inc_ref(v_traceState_2768_);
lean_dec(v___x_2767_);
v_traces_2769_ = lean_ctor_get(v_traceState_2768_, 0);
lean_inc_ref(v_traces_2769_);
lean_dec_ref(v_traceState_2768_);
v_ref_2770_ = l_Lean_replaceRef(v_ref_2755_, v_ref_2764_);
lean_inc(v_currRecDepth_2763_);
lean_inc_ref(v_toCold_2762_);
v___x_2771_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2771_, 0, v_toCold_2762_);
lean_ctor_set(v___x_2771_, 1, v_currRecDepth_2763_);
lean_ctor_set(v___x_2771_, 2, v_ref_2770_);
lean_ctor_set_uint8(v___x_2771_, sizeof(void*)*3, v_diag_2765_);
lean_ctor_set_uint8(v___x_2771_, sizeof(void*)*3 + 1, v_suppressElabErrors_2766_);
v___x_2772_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2769_);
lean_dec_ref(v_traces_2769_);
v_sz_2773_ = lean_array_size(v___x_2772_);
v___x_2774_ = ((size_t)0ULL);
v___x_2775_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_2773_, v___x_2774_, v___x_2772_);
v_msg_2776_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2776_, 0, v_data_2754_);
lean_ctor_set(v_msg_2776_, 1, v_msg_2756_);
lean_ctor_set(v_msg_2776_, 2, v___x_2775_);
v___x_2777_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2776_, v___y_2757_, v___y_2758_, v___x_2771_, v___y_2760_);
lean_dec_ref_known(v___x_2771_, 3);
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
v___x_2782_ = lean_st_ref_take(v___y_2760_);
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
lean_ctor_set(v___x_2799_, 0, v_ref_2755_);
lean_ctor_set(v___x_2799_, 1, v_a_2778_);
v___x_2800_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2753_, v___x_2799_);
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
v___x_2805_ = lean_st_ref_put(v___y_2760_, v___x_2804_);
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
v_ref_2881_ = lean_ctor_get(v___y_2846_, 2);
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
uint8_t v___y_2977_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v_toCold_2999_; lean_object* v_options_3000_; lean_object* v_inheritedTraceOptions_3001_; uint8_t v_hasTrace_3002_; lean_object* v_cls_3003_; lean_object* v___f_3004_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; uint8_t v_____do__lift_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; 
v_toCold_2999_ = lean_ctor_get(v_a_2973_, 0);
v_options_3000_ = lean_ctor_get(v_toCold_2999_, 2);
v_inheritedTraceOptions_3001_ = lean_ctor_get(v_toCold_2999_, 11);
v_hasTrace_3002_ = lean_ctor_get_uint8(v_options_3000_, sizeof(void*)*1);
v_cls_3003_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___f_3004_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1));
if (v_hasTrace_3002_ == 0)
{
lean_object* v___x_3132_; lean_object* v_a_3133_; uint8_t v___x_3134_; 
v___x_3132_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3003_, v_inheritedTraceOptions_3001_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_a_3133_);
lean_dec_ref(v___x_3132_);
v___x_3134_ = lean_unbox(v_a_3133_);
lean_dec(v_a_3133_);
v_____do__lift_3109_ = v___x_3134_;
v___y_3110_ = v_a_2966_;
v___y_3111_ = v_a_2967_;
v___y_3112_ = v_a_2968_;
v___y_3113_ = v_a_2969_;
v___y_3114_ = v_a_2970_;
v___y_3115_ = v_a_2971_;
v___y_3116_ = v_a_2972_;
v___y_3117_ = v_a_2973_;
v___y_3118_ = v_a_2974_;
goto v___jp_3108_;
}
else
{
lean_object* v___f_3135_; uint8_t v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v_a_3143_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v_a_3155_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v_a_3173_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v_a_3188_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; 
v___f_3135_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4));
v___x_3136_ = 0;
v___x_3137_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_3138_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3139_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3001_, v_options_3000_, v___x_3138_);
if (v___x_3139_ == 0)
{
lean_object* v___x_3236_; uint8_t v___x_3237_; 
v___x_3236_ = l_Lean_trace_profiler;
v___x_3237_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_3000_, v___x_3236_);
if (v___x_3237_ == 0)
{
lean_object* v___x_3238_; lean_object* v_a_3239_; uint8_t v___x_3240_; 
v___x_3238_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3003_, v_inheritedTraceOptions_3001_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
lean_inc(v_a_3239_);
lean_dec_ref(v___x_3238_);
v___x_3240_ = lean_unbox(v_a_3239_);
lean_dec(v_a_3239_);
v_____do__lift_3109_ = v___x_3240_;
v___y_3110_ = v_a_2966_;
v___y_3111_ = v_a_2967_;
v___y_3112_ = v_a_2968_;
v___y_3113_ = v_a_2969_;
v___y_3114_ = v_a_2970_;
v___y_3115_ = v_a_2971_;
v___y_3116_ = v_a_2972_;
v___y_3117_ = v_a_2973_;
v___y_3118_ = v_a_2974_;
goto v___jp_3108_;
}
else
{
goto v___jp_3203_;
}
}
else
{
goto v___jp_3203_;
}
v___jp_3140_:
{
lean_object* v___x_3144_; double v___x_3145_; double v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3144_ = lean_io_get_num_heartbeats();
v___x_3145_ = lean_float_of_nat(v___y_3141_);
v___x_3146_ = lean_float_of_nat(v___x_3144_);
v___x_3147_ = lean_box_float(v___x_3145_);
v___x_3148_ = lean_box_float(v___x_3146_);
v___x_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3147_);
lean_ctor_set(v___x_3149_, 1, v___x_3148_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v_a_3143_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
v___x_3151_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_3003_, v___x_3136_, v___x_3137_, v_options_3000_, v___x_3139_, v___y_3142_, v___f_3135_, v___x_3150_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_3151_;
}
v___jp_3152_:
{
lean_object* v___x_3156_; 
v___x_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3156_, 0, v_a_3155_);
v___y_3141_ = v___y_3153_;
v___y_3142_ = v___y_3154_;
v_a_3143_ = v___x_3156_;
goto v___jp_3140_;
}
v___jp_3157_:
{
if (lean_obj_tag(v___y_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
v_a_3161_ = lean_ctor_get(v___y_3160_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___y_3160_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___y_3160_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___y_3160_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
lean_ctor_set_tag(v___x_3163_, 1);
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
v___y_3141_ = v___y_3158_;
v___y_3142_ = v___y_3159_;
v_a_3143_ = v___x_3166_;
goto v___jp_3140_;
}
}
}
else
{
lean_object* v_a_3169_; 
v_a_3169_ = lean_ctor_get(v___y_3160_, 0);
lean_inc(v_a_3169_);
lean_dec_ref_known(v___y_3160_, 1);
v___y_3153_ = v___y_3158_;
v___y_3154_ = v___y_3159_;
v_a_3155_ = v_a_3169_;
goto v___jp_3152_;
}
}
v___jp_3170_:
{
lean_object* v___x_3174_; double v___x_3175_; double v___x_3176_; double v___x_3177_; double v___x_3178_; double v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3174_ = lean_io_mono_nanos_now();
v___x_3175_ = lean_float_of_nat(v___y_3171_);
v___x_3176_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5);
v___x_3177_ = lean_float_div(v___x_3175_, v___x_3176_);
v___x_3178_ = lean_float_of_nat(v___x_3174_);
v___x_3179_ = lean_float_div(v___x_3178_, v___x_3176_);
v___x_3180_ = lean_box_float(v___x_3177_);
v___x_3181_ = lean_box_float(v___x_3179_);
v___x_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3180_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3183_, 0, v_a_3173_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_3003_, v___x_3136_, v___x_3137_, v_options_3000_, v___x_3139_, v___y_3172_, v___f_3135_, v___x_3183_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_3184_;
}
v___jp_3185_:
{
lean_object* v___x_3189_; 
v___x_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3189_, 0, v_a_3188_);
v___y_3171_ = v___y_3186_;
v___y_3172_ = v___y_3187_;
v_a_3173_ = v___x_3189_;
goto v___jp_3170_;
}
v___jp_3190_:
{
if (lean_obj_tag(v___y_3193_) == 0)
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
v_a_3194_ = lean_ctor_get(v___y_3193_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___y_3193_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___y_3193_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___y_3193_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
lean_ctor_set_tag(v___x_3196_, 1);
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
v___y_3171_ = v___y_3191_;
v___y_3172_ = v___y_3192_;
v_a_3173_ = v___x_3199_;
goto v___jp_3170_;
}
}
}
else
{
lean_object* v_a_3202_; 
v_a_3202_ = lean_ctor_get(v___y_3193_, 0);
lean_inc(v_a_3202_);
lean_dec_ref_known(v___y_3193_, 1);
v___y_3186_ = v___y_3191_;
v___y_3187_ = v___y_3192_;
v_a_3188_ = v_a_3202_;
goto v___jp_3185_;
}
}
v___jp_3203_:
{
lean_object* v___x_3204_; lean_object* v_a_3205_; lean_object* v___x_3206_; uint8_t v___x_3207_; 
v___x_3204_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v_a_2974_);
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref(v___x_3204_);
v___x_3206_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3207_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_3000_, v___x_3206_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v_a_3210_; uint8_t v___x_3211_; 
v___x_3208_ = lean_io_mono_nanos_now();
v___x_3209_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3003_, v_inheritedTraceOptions_3001_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3210_);
lean_dec_ref(v___x_3209_);
v___x_3211_ = lean_unbox(v_a_3210_);
lean_dec(v_a_3210_);
if (v___x_3211_ == 0)
{
lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3212_ = lean_box(0);
v___x_3213_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2964_, v_rhs_2965_, v___x_3207_, v___f_3004_, v_cls_3003_, v_P_2963_, v___x_3212_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3191_ = v___x_3208_;
v___y_3192_ = v_a_3205_;
v___y_3193_ = v___x_3213_;
goto v___jp_3190_;
}
else
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3214_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_2965_);
lean_inc_ref(v_lhs_2964_);
lean_inc_ref(v_P_2963_);
v___x_3215_ = l_Lean_mkAppB(v_P_2963_, v_lhs_2964_, v_rhs_2965_);
v___x_3216_ = l_Lean_indentExpr(v___x_3215_);
v___x_3217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3214_);
lean_ctor_set(v___x_3217_, 1, v___x_3216_);
v___x_3218_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3003_, v___x_3217_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v___x_3220_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_a_3219_);
lean_dec_ref_known(v___x_3218_, 1);
v___x_3220_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2964_, v_rhs_2965_, v___x_3207_, v___f_3004_, v_cls_3003_, v_P_2963_, v_a_3219_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3191_ = v___x_3208_;
v___y_3192_ = v_a_3205_;
v___y_3193_ = v___x_3220_;
goto v___jp_3190_;
}
else
{
lean_object* v_a_3221_; 
lean_dec_ref(v_rhs_2965_);
lean_dec_ref(v_lhs_2964_);
lean_dec_ref(v_P_2963_);
v_a_3221_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_a_3221_);
lean_dec_ref_known(v___x_3218_, 1);
v___y_3186_ = v___x_3208_;
v___y_3187_ = v_a_3205_;
v_a_3188_ = v_a_3221_;
goto v___jp_3185_;
}
}
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v_a_3224_; uint8_t v___x_3225_; 
v___x_3222_ = lean_io_get_num_heartbeats();
v___x_3223_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3003_, v_inheritedTraceOptions_3001_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_a_3224_);
lean_dec_ref(v___x_3223_);
v___x_3225_ = lean_unbox(v_a_3224_);
lean_dec(v_a_3224_);
if (v___x_3225_ == 0)
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = lean_box(0);
v___x_3227_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2964_, v_rhs_2965_, v_P_2963_, v_cls_3003_, v___x_3207_, v___f_3004_, v___x_3136_, v___x_3226_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3158_ = v___x_3222_;
v___y_3159_ = v_a_3205_;
v___y_3160_ = v___x_3227_;
goto v___jp_3157_;
}
else
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3228_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_2965_);
lean_inc_ref(v_lhs_2964_);
lean_inc_ref(v_P_2963_);
v___x_3229_ = l_Lean_mkAppB(v_P_2963_, v_lhs_2964_, v_rhs_2965_);
v___x_3230_ = l_Lean_indentExpr(v___x_3229_);
v___x_3231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3228_);
lean_ctor_set(v___x_3231_, 1, v___x_3230_);
v___x_3232_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3003_, v___x_3231_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; lean_object* v___x_3234_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3233_);
lean_dec_ref_known(v___x_3232_, 1);
v___x_3234_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2964_, v_rhs_2965_, v_P_2963_, v_cls_3003_, v___x_3207_, v___f_3004_, v___x_3136_, v_a_3233_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3158_ = v___x_3222_;
v___y_3159_ = v_a_3205_;
v___y_3160_ = v___x_3234_;
goto v___jp_3157_;
}
else
{
lean_object* v_a_3235_; 
lean_dec_ref(v_rhs_2965_);
lean_dec_ref(v_lhs_2964_);
lean_dec_ref(v_P_2963_);
v_a_3235_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3235_);
lean_dec_ref_known(v___x_3232_, 1);
v___y_3153_ = v___x_3222_;
v___y_3154_ = v_a_3205_;
v_a_3155_ = v_a_3235_;
goto v___jp_3152_;
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
v___jp_3005_:
{
lean_object* v___x_3015_; 
lean_inc_ref(v_lhs_2964_);
v___x_3015_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2964_);
if (lean_obj_tag(v___x_3015_) == 1)
{
lean_object* v_val_3016_; lean_object* v___x_3017_; 
v_val_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_val_3016_);
lean_dec_ref_known(v___x_3015_, 1);
lean_inc_ref(v_rhs_2965_);
v___x_3017_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2965_);
if (lean_obj_tag(v___x_3017_) == 1)
{
lean_object* v_val_3018_; uint8_t v___x_3019_; 
v_val_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_val_3018_);
lean_dec_ref_known(v___x_3017_, 1);
v___x_3019_ = lean_expr_eqv(v_val_3016_, v_val_3018_);
if (v___x_3019_ == 0)
{
lean_object* v_toCold_3020_; lean_object* v_inheritedTraceOptions_3021_; lean_object* v___x_3022_; lean_object* v_a_3023_; uint8_t v___x_3024_; 
lean_dec_ref(v_P_2963_);
v_toCold_3020_ = lean_ctor_get(v___y_3013_, 0);
v_inheritedTraceOptions_3021_ = lean_ctor_get(v_toCold_3020_, 11);
v___x_3022_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3003_, v_inheritedTraceOptions_3021_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref(v___x_3022_);
v___x_3024_ = lean_unbox(v_a_3023_);
lean_dec(v_a_3023_);
if (v___x_3024_ == 0)
{
lean_dec(v_val_3018_);
lean_dec(v_val_3016_);
lean_dec_ref(v_rhs_2965_);
lean_dec_ref(v_lhs_2964_);
v___y_2977_ = v___x_3019_;
goto v___jp_2976_;
}
else
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3025_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1);
v___x_3026_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3016_);
v___x_3027_ = l_Lean_MessageData_ofExpr(v___x_3026_);
v___x_3028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3025_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
v___x_3029_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3);
v___x_3030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3028_);
lean_ctor_set(v___x_3030_, 1, v___x_3029_);
v___x_3031_ = l_Lean_indentExpr(v_lhs_2964_);
v___x_3032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3030_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5);
v___x_3034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3032_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
v___x_3035_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3018_);
v___x_3036_ = l_Lean_MessageData_ofExpr(v___x_3035_);
v___x_3037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3034_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
v___x_3038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
lean_ctor_set(v___x_3038_, 1, v___x_3029_);
v___x_3039_ = l_Lean_indentExpr(v_rhs_2965_);
v___x_3040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3038_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
v___x_3041_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3003_, v___x_3040_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_dec_ref_known(v___x_3041_, 1);
v___y_2977_ = v___x_3019_;
goto v___jp_2976_;
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3041_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3041_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
}
else
{
lean_object* v_toCold_3050_; lean_object* v_options_3051_; lean_object* v_inheritedTraceOptions_3052_; uint8_t v_hasTrace_3053_; uint8_t v___x_3054_; lean_object* v___x_3055_; lean_object* v___f_3056_; 
lean_dec(v_val_3018_);
v_toCold_3050_ = lean_ctor_get(v___y_3013_, 0);
v_options_3051_ = lean_ctor_get(v_toCold_3050_, 2);
v_inheritedTraceOptions_3052_ = lean_ctor_get(v_toCold_3050_, 11);
v_hasTrace_3053_ = lean_ctor_get_uint8(v_options_3051_, sizeof(void*)*1);
v___x_3054_ = 0;
v___x_3055_ = lean_box(v___x_3054_);
lean_inc(v_val_3016_);
v___f_3056_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 13, 5);
lean_closure_set(v___f_3056_, 0, v_val_3016_);
lean_closure_set(v___f_3056_, 1, v_lhs_2964_);
lean_closure_set(v___f_3056_, 2, v_rhs_2965_);
lean_closure_set(v___f_3056_, 3, v_P_2963_);
lean_closure_set(v___f_3056_, 4, v___x_3055_);
if (v_hasTrace_3053_ == 0)
{
v___y_2987_ = v___f_3056_;
v___y_2988_ = v_val_3016_;
v___y_2989_ = v___y_3009_;
v___y_2990_ = v___y_3010_;
v___y_2991_ = v___y_3011_;
v___y_2992_ = v___y_3012_;
v___y_2993_ = v___y_3013_;
v___y_2994_ = v___y_3014_;
goto v___jp_2986_;
}
else
{
lean_object* v___x_3057_; uint8_t v___x_3058_; 
v___x_3057_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3058_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3052_, v_options_3051_, v___x_3057_);
if (v___x_3058_ == 0)
{
v___y_2987_ = v___f_3056_;
v___y_2988_ = v_val_3016_;
v___y_2989_ = v___y_3009_;
v___y_2990_ = v___y_3010_;
v___y_2991_ = v___y_3011_;
v___y_2992_ = v___y_3012_;
v___y_2993_ = v___y_3013_;
v___y_2994_ = v___y_3014_;
goto v___jp_2986_;
}
else
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3059_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10);
lean_inc(v_val_3016_);
v___x_3060_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3016_);
v___x_3061_ = l_Lean_MessageData_ofExpr(v___x_3060_);
v___x_3062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3059_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
v___x_3063_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12);
v___x_3064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3062_);
lean_ctor_set(v___x_3064_, 1, v___x_3063_);
v___x_3065_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3003_, v___x_3064_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_dec_ref_known(v___x_3065_, 1);
v___y_2987_ = v___f_3056_;
v___y_2988_ = v_val_3016_;
v___y_2989_ = v___y_3009_;
v___y_2990_ = v___y_3010_;
v___y_2991_ = v___y_3011_;
v___y_2992_ = v___y_3012_;
v___y_2993_ = v___y_3013_;
v___y_2994_ = v___y_3014_;
goto v___jp_2986_;
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec_ref(v___f_3056_);
lean_dec(v_val_3016_);
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3065_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3065_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_3074_; lean_object* v_inheritedTraceOptions_3075_; lean_object* v___x_3076_; lean_object* v_a_3077_; uint8_t v___x_3078_; 
lean_dec(v___x_3017_);
lean_dec(v_val_3016_);
lean_dec_ref(v_lhs_2964_);
lean_dec_ref(v_P_2963_);
v_toCold_3074_ = lean_ctor_get(v___y_3013_, 0);
v_inheritedTraceOptions_3075_ = lean_ctor_get(v_toCold_3074_, 11);
v___x_3076_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3003_, v_inheritedTraceOptions_3075_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_a_3077_);
lean_dec_ref(v___x_3076_);
v___x_3078_ = lean_unbox(v_a_3077_);
lean_dec(v_a_3077_);
if (v___x_3078_ == 0)
{
lean_dec_ref(v_rhs_2965_);
goto v___jp_2983_;
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3079_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_3080_ = l_Lean_indentExpr(v_rhs_2965_);
v___x_3081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3079_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
v___x_3082_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3003_, v___x_3081_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_dec_ref_known(v___x_3082_, 1);
goto v___jp_2983_;
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3082_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3082_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3091_; lean_object* v_inheritedTraceOptions_3092_; lean_object* v___x_3093_; lean_object* v_a_3094_; uint8_t v___x_3095_; 
lean_dec(v___x_3015_);
lean_dec_ref(v_rhs_2965_);
lean_dec_ref(v_P_2963_);
v_toCold_3091_ = lean_ctor_get(v___y_3013_, 0);
v_inheritedTraceOptions_3092_ = lean_ctor_get(v_toCold_3091_, 11);
v___x_3093_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3003_, v_inheritedTraceOptions_3092_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_a_3094_);
lean_dec_ref(v___x_3093_);
v___x_3095_ = lean_unbox(v_a_3094_);
lean_dec(v_a_3094_);
if (v___x_3095_ == 0)
{
lean_dec_ref(v_lhs_2964_);
goto v___jp_2980_;
}
else
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3096_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_3097_ = l_Lean_indentExpr(v_lhs_2964_);
v___x_3098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3096_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3003_, v___x_3098_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_dec_ref_known(v___x_3099_, 1);
goto v___jp_2980_;
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3099_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3099_);
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
}
}
v___jp_3108_:
{
if (v_____do__lift_3109_ == 0)
{
v___y_3006_ = v___y_3110_;
v___y_3007_ = v___y_3111_;
v___y_3008_ = v___y_3112_;
v___y_3009_ = v___y_3113_;
v___y_3010_ = v___y_3114_;
v___y_3011_ = v___y_3115_;
v___y_3012_ = v___y_3116_;
v___y_3013_ = v___y_3117_;
v___y_3014_ = v___y_3118_;
goto v___jp_3005_;
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3119_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_2965_);
lean_inc_ref(v_lhs_2964_);
lean_inc_ref(v_P_2963_);
v___x_3120_ = l_Lean_mkAppB(v_P_2963_, v_lhs_2964_, v_rhs_2965_);
v___x_3121_ = l_Lean_indentExpr(v___x_3120_);
v___x_3122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3119_);
lean_ctor_set(v___x_3122_, 1, v___x_3121_);
v___x_3123_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3003_, v___x_3122_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_dec_ref_known(v___x_3123_, 1);
v___y_3006_ = v___y_3110_;
v___y_3007_ = v___y_3111_;
v___y_3008_ = v___y_3112_;
v___y_3009_ = v___y_3113_;
v___y_3010_ = v___y_3114_;
v___y_3011_ = v___y_3115_;
v___y_3012_ = v___y_3116_;
v___y_3013_ = v___y_3117_;
v___y_3014_ = v___y_3118_;
goto v___jp_3005_;
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
lean_dec_ref(v_rhs_2965_);
lean_dec_ref(v_lhs_2964_);
lean_dec_ref(v_P_2963_);
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_3123_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3123_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___boxed(lean_object* v_P_3241_, lean_object* v_lhs_3242_, lean_object* v_rhs_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v_P_3241_, v_lhs_3242_, v_rhs_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
lean_dec(v_a_3252_);
lean_dec_ref(v_a_3251_);
lean_dec(v_a_3250_);
lean_dec_ref(v_a_3249_);
lean_dec(v_a_3248_);
lean_dec_ref(v_a_3247_);
lean_dec(v_a_3246_);
lean_dec_ref(v_a_3245_);
lean_dec(v_a_3244_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(lean_object* v_cls_3255_, lean_object* v_msg_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v___x_3267_; 
v___x_3267_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3255_, v_msg_3256_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object* v_cls_3268_, lean_object* v_msg_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(v_cls_3268_, v_msg_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(lean_object* v_00_u03b1_3281_, lean_object* v_x_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_3282_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___boxed(lean_object* v_00_u03b1_3294_, lean_object* v_x_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(v_00_u03b1_3294_, v_x_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(lean_object* v_oldTraces_3307_, lean_object* v_data_3308_, lean_object* v_ref_3309_, lean_object* v_msg_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v___x_3321_; 
v___x_3321_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_3307_, v_data_3308_, v_ref_3309_, v_msg_3310_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___boxed(lean_object* v_oldTraces_3322_, lean_object* v_data_3323_, lean_object* v_ref_3324_, lean_object* v_msg_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(v_oldTraces_3322_, v_data_3323_, v_ref_3324_, v_msg_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec(v___y_3326_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(lean_object* v_x_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3348_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3348_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0___boxed(lean_object* v_x_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v_res_3361_; 
v_res_3361_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v_x_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(lean_object* v_arg_3367_, lean_object* v_arg_3368_, lean_object* v_arg_3369_, lean_object* v_arg_3370_, lean_object* v_____r_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v___x_3382_; 
lean_inc_ref(v_arg_3367_);
v___x_3382_ = l_Lean_Meta_getDecLevel(v_arg_3367_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref_known(v___x_3382_, 1);
v___x_3384_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2));
v___x_3385_ = lean_box(0);
v___x_3386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3386_, 0, v_a_3383_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
v___x_3387_ = l_Lean_Expr_const___override(v___x_3384_, v___x_3386_);
v___x_3388_ = l_Lean_mkAppB(v___x_3387_, v_arg_3367_, v_arg_3368_);
v___x_3389_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3388_, v_arg_3369_, v_arg_3370_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
return v___x_3389_;
}
else
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
lean_dec_ref(v_arg_3370_);
lean_dec_ref(v_arg_3369_);
lean_dec_ref(v_arg_3368_);
lean_dec_ref(v_arg_3367_);
v_a_3390_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3382_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3382_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3395_; 
if (v_isShared_3393_ == 0)
{
v___x_3395_ = v___x_3392_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3390_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___boxed(lean_object* v_arg_3398_, lean_object* v_arg_3399_, lean_object* v_arg_3400_, lean_object* v_arg_3401_, lean_object* v_____r_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3398_, v_arg_3399_, v_arg_3400_, v_arg_3401_, v_____r_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(lean_object* v_arg_3417_, lean_object* v_arg_3418_, lean_object* v_arg_3419_, lean_object* v_____r_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_){
_start:
{
lean_object* v___x_3431_; 
lean_inc_ref(v_arg_3417_);
v___x_3431_ = l_Lean_Meta_getLevel(v_arg_3417_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3432_);
lean_dec_ref_known(v___x_3431_, 1);
v___x_3433_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1));
v___x_3434_ = lean_box(0);
v___x_3435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3435_, 0, v_a_3432_);
lean_ctor_set(v___x_3435_, 1, v___x_3434_);
v___x_3436_ = l_Lean_Expr_const___override(v___x_3433_, v___x_3435_);
v___x_3437_ = l_Lean_Expr_app___override(v___x_3436_, v_arg_3417_);
v___x_3438_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3437_, v_arg_3418_, v_arg_3419_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
return v___x_3438_;
}
else
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3446_; 
lean_dec_ref(v_arg_3419_);
lean_dec_ref(v_arg_3418_);
lean_dec_ref(v_arg_3417_);
v_a_3439_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3441_ = v___x_3431_;
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3431_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___boxed(lean_object* v_arg_3447_, lean_object* v_arg_3448_, lean_object* v_arg_3449_, lean_object* v_____r_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3447_, v_arg_3448_, v_arg_3449_, v_____r_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
return v_res_3461_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1(void){
_start:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3463_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0));
v___x_3464_ = l_Lean_stringToMessageData(v___x_3463_);
return v___x_3464_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2(void){
_start:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3465_ = l_Lean_checkEmoji;
v___x_3466_ = l_Lean_stringToMessageData(v___x_3465_);
return v___x_3466_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3(void){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3467_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2);
v___x_3468_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1);
v___x_3469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
lean_ctor_set(v___x_3469_, 1, v___x_3467_);
return v___x_3469_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5(void){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3471_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4));
v___x_3472_ = l_Lean_stringToMessageData(v___x_3471_);
return v___x_3472_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6(void){
_start:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3473_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5);
v___x_3474_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3);
v___x_3475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
lean_ctor_set(v___x_3475_, 1, v___x_3473_);
return v___x_3475_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8(void){
_start:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3477_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7));
v___x_3478_ = l_Lean_stringToMessageData(v___x_3477_);
return v___x_3478_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9(void){
_start:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3479_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8);
v___x_3480_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3);
v___x_3481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
lean_ctor_set(v___x_3481_, 1, v___x_3479_);
return v___x_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(lean_object* v_e_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_){
_start:
{
lean_object* v___y_3494_; lean_object* v___x_3526_; 
v___x_3526_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3482_, v_a_3489_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3528_; uint8_t v___x_3529_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3527_);
lean_dec_ref_known(v___x_3526_, 1);
v___x_3528_ = l_Lean_Expr_cleanupAnnotations(v_a_3527_);
v___x_3529_ = l_Lean_Expr_isApp(v___x_3528_);
if (v___x_3529_ == 0)
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
lean_dec_ref(v___x_3528_);
v___x_3530_ = lean_box(0);
v___x_3531_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3530_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
v___y_3494_ = v___x_3531_;
goto v___jp_3493_;
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
v___x_3535_ = lean_box(0);
v___x_3536_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3535_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
v___y_3494_ = v___x_3536_;
goto v___jp_3493_;
}
else
{
lean_object* v_arg_3537_; lean_object* v___x_3538_; uint8_t v___x_3539_; 
v_arg_3537_ = lean_ctor_get(v___x_3533_, 1);
lean_inc_ref(v_arg_3537_);
v___x_3538_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3533_);
v___x_3539_ = l_Lean_Expr_isApp(v___x_3538_);
if (v___x_3539_ == 0)
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
lean_dec_ref(v___x_3538_);
lean_dec_ref(v_arg_3537_);
lean_dec_ref(v_arg_3532_);
v___x_3540_ = lean_box(0);
v___x_3541_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3540_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
v___y_3494_ = v___x_3541_;
goto v___jp_3493_;
}
else
{
lean_object* v_arg_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; uint8_t v___x_3545_; 
v_arg_3542_ = lean_ctor_get(v___x_3538_, 1);
lean_inc_ref(v_arg_3542_);
v___x_3543_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3538_);
v___x_3544_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1));
v___x_3545_ = l_Lean_Expr_isConstOf(v___x_3543_, v___x_3544_);
if (v___x_3545_ == 0)
{
uint8_t v___x_3546_; 
v___x_3546_ = l_Lean_Expr_isApp(v___x_3543_);
if (v___x_3546_ == 0)
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
lean_dec_ref(v___x_3543_);
lean_dec_ref(v_arg_3542_);
lean_dec_ref(v_arg_3537_);
lean_dec_ref(v_arg_3532_);
v___x_3547_ = lean_box(0);
v___x_3548_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3547_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
v___y_3494_ = v___x_3548_;
goto v___jp_3493_;
}
else
{
lean_object* v_arg_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; uint8_t v___x_3552_; 
v_arg_3549_ = lean_ctor_get(v___x_3543_, 1);
lean_inc_ref(v_arg_3549_);
v___x_3550_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3543_);
v___x_3551_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2));
v___x_3552_ = l_Lean_Expr_isConstOf(v___x_3550_, v___x_3551_);
lean_dec_ref(v___x_3550_);
if (v___x_3552_ == 0)
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
lean_dec_ref(v_arg_3549_);
lean_dec_ref(v_arg_3542_);
lean_dec_ref(v_arg_3537_);
lean_dec_ref(v_arg_3532_);
v___x_3553_ = lean_box(0);
v___x_3554_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3553_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
v___y_3494_ = v___x_3554_;
goto v___jp_3493_;
}
else
{
lean_object* v_toCold_3555_; lean_object* v_options_3556_; lean_object* v_inheritedTraceOptions_3557_; uint8_t v_hasTrace_3558_; 
v_toCold_3555_ = lean_ctor_get(v_a_3490_, 0);
v_options_3556_ = lean_ctor_get(v_toCold_3555_, 2);
v_inheritedTraceOptions_3557_ = lean_ctor_get(v_toCold_3555_, 11);
v_hasTrace_3558_ = lean_ctor_get_uint8(v_options_3556_, sizeof(void*)*1);
if (v_hasTrace_3558_ == 0)
{
goto v___jp_3559_;
}
else
{
lean_object* v___x_3562_; lean_object* v___x_3563_; uint8_t v___x_3564_; 
v___x_3562_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3563_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3564_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3557_, v_options_3556_, v___x_3563_);
if (v___x_3564_ == 0)
{
goto v___jp_3559_;
}
else
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6);
v___x_3566_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3562_, v___x_3565_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v_a_3567_; lean_object* v___x_3568_; 
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_a_3567_);
lean_dec_ref_known(v___x_3566_, 1);
v___x_3568_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3549_, v_arg_3542_, v_arg_3537_, v_arg_3532_, v_a_3567_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
v___y_3494_ = v___x_3568_;
goto v___jp_3493_;
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec_ref(v_arg_3549_);
lean_dec_ref(v_arg_3542_);
lean_dec_ref(v_arg_3537_);
lean_dec_ref(v_arg_3532_);
v_a_3569_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3566_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3566_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
}
v___jp_3559_:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = lean_box(0);
v___x_3561_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3549_, v_arg_3542_, v_arg_3537_, v_arg_3532_, v___x_3560_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
v___y_3494_ = v___x_3561_;
goto v___jp_3493_;
}
}
}
}
else
{
lean_object* v_toCold_3577_; lean_object* v_options_3578_; lean_object* v_inheritedTraceOptions_3579_; uint8_t v_hasTrace_3580_; 
lean_dec_ref(v___x_3543_);
v_toCold_3577_ = lean_ctor_get(v_a_3490_, 0);
v_options_3578_ = lean_ctor_get(v_toCold_3577_, 2);
v_inheritedTraceOptions_3579_ = lean_ctor_get(v_toCold_3577_, 11);
v_hasTrace_3580_ = lean_ctor_get_uint8(v_options_3578_, sizeof(void*)*1);
if (v_hasTrace_3580_ == 0)
{
goto v___jp_3581_;
}
else
{
lean_object* v___x_3584_; lean_object* v___x_3585_; uint8_t v___x_3586_; 
v___x_3584_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3585_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3586_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3579_, v_options_3578_, v___x_3585_);
if (v___x_3586_ == 0)
{
goto v___jp_3581_;
}
else
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3587_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9);
v___x_3588_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3584_, v___x_3587_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3590_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref_known(v___x_3588_, 1);
v___x_3590_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3542_, v_arg_3537_, v_arg_3532_, v_a_3589_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
v___y_3494_ = v___x_3590_;
goto v___jp_3493_;
}
else
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
lean_dec_ref(v_arg_3542_);
lean_dec_ref(v_arg_3537_);
lean_dec_ref(v_arg_3532_);
v_a_3591_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3593_ = v___x_3588_;
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3588_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3596_; 
if (v_isShared_3594_ == 0)
{
v___x_3596_ = v___x_3593_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3591_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
}
v___jp_3581_:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; 
v___x_3582_ = lean_box(0);
v___x_3583_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3542_, v_arg_3537_, v_arg_3532_, v___x_3582_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
v___y_3494_ = v___x_3583_;
goto v___jp_3493_;
}
}
}
}
}
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
v_a_3599_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3526_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3526_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
v___jp_3493_:
{
if (lean_obj_tag(v___y_3494_) == 0)
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3525_; 
v_a_3495_ = lean_ctor_get(v___y_3494_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___y_3494_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3497_ = v___y_3494_;
v_isShared_3498_ = v_isSharedCheck_3525_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___y_3494_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3525_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
if (lean_obj_tag(v_a_3495_) == 0)
{
uint8_t v_contextDependent_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3510_; 
v_contextDependent_3499_ = lean_ctor_get_uint8(v_a_3495_, 1);
v_isSharedCheck_3510_ = !lean_is_exclusive(v_a_3495_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3501_ = v_a_3495_;
v_isShared_3502_ = v_isSharedCheck_3510_;
goto v_resetjp_3500_;
}
else
{
lean_dec(v_a_3495_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3510_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
uint8_t v___x_3503_; lean_object* v___x_3505_; 
v___x_3503_ = 1;
if (v_isShared_3502_ == 0)
{
v___x_3505_ = v___x_3501_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_3509_, 1, v_contextDependent_3499_);
v___x_3505_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
lean_object* v___x_3507_; 
lean_ctor_set_uint8(v___x_3505_, 0, v___x_3503_);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v___x_3505_);
v___x_3507_ = v___x_3497_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
else
{
lean_object* v_e_x27_3511_; lean_object* v_proof_3512_; uint8_t v_contextDependent_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3524_; 
v_e_x27_3511_ = lean_ctor_get(v_a_3495_, 0);
v_proof_3512_ = lean_ctor_get(v_a_3495_, 1);
v_contextDependent_3513_ = lean_ctor_get_uint8(v_a_3495_, sizeof(void*)*2 + 1);
v_isSharedCheck_3524_ = !lean_is_exclusive(v_a_3495_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3515_ = v_a_3495_;
v_isShared_3516_ = v_isSharedCheck_3524_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_proof_3512_);
lean_inc(v_e_x27_3511_);
lean_dec(v_a_3495_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3524_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
uint8_t v___x_3517_; lean_object* v___x_3519_; 
v___x_3517_ = 1;
if (v_isShared_3516_ == 0)
{
v___x_3519_ = v___x_3515_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_e_x27_3511_);
lean_ctor_set(v_reuseFailAlloc_3523_, 1, v_proof_3512_);
lean_ctor_set_uint8(v_reuseFailAlloc_3523_, sizeof(void*)*2 + 1, v_contextDependent_3513_);
v___x_3519_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
lean_object* v___x_3521_; 
lean_ctor_set_uint8(v___x_3519_, sizeof(void*)*2, v___x_3517_);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v___x_3519_);
v___x_3521_ = v___x_3497_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v___x_3519_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
}
}
else
{
return v___y_3494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed(lean_object* v_e_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(v_e_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_);
lean_dec(v_a_3616_);
lean_dec_ref(v_a_3615_);
lean_dec(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec(v_a_3612_);
lean_dec_ref(v_a_3611_);
lean_dec(v_a_3610_);
lean_dec_ref(v_a_3609_);
lean_dec(v_a_3608_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(lean_object* v_x_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v___x_3632_; 
lean_inc(v___y_3626_);
lean_inc_ref(v___y_3625_);
lean_inc(v___y_3624_);
lean_inc_ref(v___y_3623_);
lean_inc(v___y_3622_);
lean_inc(v___y_3621_);
lean_inc_ref(v___y_3620_);
v___x_3632_ = lean_apply_12(v_x_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, lean_box(0));
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed(lean_object* v_x_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_){
_start:
{
lean_object* v_res_3646_; 
v_res_3646_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(v_x_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
return v_res_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object* v_mvarId_3647_, lean_object* v_x_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v___f_3661_; lean_object* v___x_3662_; 
lean_inc(v___y_3655_);
lean_inc_ref(v___y_3654_);
lean_inc(v___y_3653_);
lean_inc_ref(v___y_3652_);
lean_inc(v___y_3651_);
lean_inc(v___y_3650_);
lean_inc_ref(v___y_3649_);
v___f_3661_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_3661_, 0, v_x_3648_);
lean_closure_set(v___f_3661_, 1, v___y_3649_);
lean_closure_set(v___f_3661_, 2, v___y_3650_);
lean_closure_set(v___f_3661_, 3, v___y_3651_);
lean_closure_set(v___f_3661_, 4, v___y_3652_);
lean_closure_set(v___f_3661_, 5, v___y_3653_);
lean_closure_set(v___f_3661_, 6, v___y_3654_);
lean_closure_set(v___f_3661_, 7, v___y_3655_);
v___x_3662_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3647_, v___f_3661_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
if (lean_obj_tag(v___x_3662_) == 0)
{
return v___x_3662_;
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3665_ = v___x_3662_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3662_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object* v_mvarId_3671_, lean_object* v_x_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_mvarId_3671_, v_x_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(lean_object* v_00_u03b1_3686_, lean_object* v_mvarId_3687_, lean_object* v_x_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
lean_object* v___x_3701_; 
v___x_3701_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_mvarId_3687_, v_x_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object* v_00_u03b1_3702_, lean_object* v_mvarId_3703_, lean_object* v_x_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(v_00_u03b1_3702_, v_mvarId_3703_, v_x_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
return v_res_3717_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0(lean_object* v_x_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3729_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0___boxed(lean_object* v_x_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0(v_x_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
lean_dec(v___y_3734_);
lean_dec_ref(v___y_3733_);
lean_dec(v___y_3732_);
lean_dec_ref(v_x_3731_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(lean_object* v_snd_3743_, lean_object* v_a_3744_, lean_object* v___x_3745_, lean_object* v_____r_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3759_ = lean_array_push(v_snd_3743_, v_a_3744_);
v___x_3760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3745_);
lean_ctor_set(v___x_3760_, 1, v___x_3759_);
v___x_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3760_);
v___x_3762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3761_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1___boxed(lean_object* v_snd_3763_, lean_object* v_a_3764_, lean_object* v___x_3765_, lean_object* v_____r_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_){
_start:
{
lean_object* v_res_3779_; 
v_res_3779_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(v_snd_3763_, v_a_3764_, v___x_3765_, v_____r_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
lean_dec(v___y_3777_);
lean_dec_ref(v___y_3776_);
lean_dec(v___y_3775_);
lean_dec_ref(v___y_3774_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
lean_dec(v___y_3769_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
return v_res_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object* v_cls_3780_, lean_object* v_msg_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
lean_object* v_ref_3787_; lean_object* v___x_3788_; lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3833_; 
v_ref_3787_ = lean_ctor_get(v___y_3784_, 2);
v___x_3788_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3791_ = v___x_3788_;
v_isShared_3792_ = v_isSharedCheck_3833_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3788_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3833_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3793_; lean_object* v_traceState_3794_; lean_object* v_env_3795_; lean_object* v_nextMacroScope_3796_; lean_object* v_ngen_3797_; lean_object* v_auxDeclNGen_3798_; lean_object* v_cache_3799_; lean_object* v_messages_3800_; lean_object* v_infoState_3801_; lean_object* v_snapshotTasks_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3832_; 
v___x_3793_ = lean_st_ref_take(v___y_3785_);
v_traceState_3794_ = lean_ctor_get(v___x_3793_, 4);
v_env_3795_ = lean_ctor_get(v___x_3793_, 0);
v_nextMacroScope_3796_ = lean_ctor_get(v___x_3793_, 1);
v_ngen_3797_ = lean_ctor_get(v___x_3793_, 2);
v_auxDeclNGen_3798_ = lean_ctor_get(v___x_3793_, 3);
v_cache_3799_ = lean_ctor_get(v___x_3793_, 5);
v_messages_3800_ = lean_ctor_get(v___x_3793_, 6);
v_infoState_3801_ = lean_ctor_get(v___x_3793_, 7);
v_snapshotTasks_3802_ = lean_ctor_get(v___x_3793_, 8);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3804_ = v___x_3793_;
v_isShared_3805_ = v_isSharedCheck_3832_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_snapshotTasks_3802_);
lean_inc(v_infoState_3801_);
lean_inc(v_messages_3800_);
lean_inc(v_cache_3799_);
lean_inc(v_traceState_3794_);
lean_inc(v_auxDeclNGen_3798_);
lean_inc(v_ngen_3797_);
lean_inc(v_nextMacroScope_3796_);
lean_inc(v_env_3795_);
lean_dec(v___x_3793_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3832_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
uint64_t v_tid_3806_; lean_object* v_traces_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3831_; 
v_tid_3806_ = lean_ctor_get_uint64(v_traceState_3794_, sizeof(void*)*1);
v_traces_3807_ = lean_ctor_get(v_traceState_3794_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v_traceState_3794_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3809_ = v_traceState_3794_;
v_isShared_3810_ = v_isSharedCheck_3831_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_traces_3807_);
lean_dec(v_traceState_3794_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3831_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3811_; double v___x_3812_; uint8_t v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3821_; 
v___x_3811_ = lean_box(0);
v___x_3812_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_3813_ = 0;
v___x_3814_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_3815_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3815_, 0, v_cls_3780_);
lean_ctor_set(v___x_3815_, 1, v___x_3811_);
lean_ctor_set(v___x_3815_, 2, v___x_3814_);
lean_ctor_set_float(v___x_3815_, sizeof(void*)*3, v___x_3812_);
lean_ctor_set_float(v___x_3815_, sizeof(void*)*3 + 8, v___x_3812_);
lean_ctor_set_uint8(v___x_3815_, sizeof(void*)*3 + 16, v___x_3813_);
v___x_3816_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_3817_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3815_);
lean_ctor_set(v___x_3817_, 1, v_a_3789_);
lean_ctor_set(v___x_3817_, 2, v___x_3816_);
lean_inc(v_ref_3787_);
v___x_3818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3818_, 0, v_ref_3787_);
lean_ctor_set(v___x_3818_, 1, v___x_3817_);
v___x_3819_ = l_Lean_PersistentArray_push___redArg(v_traces_3807_, v___x_3818_);
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 0, v___x_3819_);
v___x_3821_ = v___x_3809_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3819_);
lean_ctor_set_uint64(v_reuseFailAlloc_3830_, sizeof(void*)*1, v_tid_3806_);
v___x_3821_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
lean_object* v___x_3823_; 
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 4, v___x_3821_);
v___x_3823_ = v___x_3804_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_env_3795_);
lean_ctor_set(v_reuseFailAlloc_3829_, 1, v_nextMacroScope_3796_);
lean_ctor_set(v_reuseFailAlloc_3829_, 2, v_ngen_3797_);
lean_ctor_set(v_reuseFailAlloc_3829_, 3, v_auxDeclNGen_3798_);
lean_ctor_set(v_reuseFailAlloc_3829_, 4, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3829_, 5, v_cache_3799_);
lean_ctor_set(v_reuseFailAlloc_3829_, 6, v_messages_3800_);
lean_ctor_set(v_reuseFailAlloc_3829_, 7, v_infoState_3801_);
lean_ctor_set(v_reuseFailAlloc_3829_, 8, v_snapshotTasks_3802_);
v___x_3823_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3827_; 
v___x_3824_ = lean_st_ref_put(v___y_3785_, v___x_3823_);
v___x_3825_ = lean_box(0);
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 0, v___x_3825_);
v___x_3827_ = v___x_3791_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3825_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object* v_cls_3834_, lean_object* v_msg_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
lean_object* v_res_3841_; 
v_res_3841_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_cls_3834_, v_msg_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(uint8_t v___x_3842_, lean_object* v___f_3843_, lean_object* v_____r_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v___x_3857_; lean_object* v_caches_3858_; lean_object* v_typeAnalysis_3859_; lean_object* v_target_3860_; lean_object* v_hypotheses_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3871_; 
v___x_3857_ = lean_st_ref_take(v___y_3846_);
v_caches_3858_ = lean_ctor_get(v___x_3857_, 0);
v_typeAnalysis_3859_ = lean_ctor_get(v___x_3857_, 1);
v_target_3860_ = lean_ctor_get(v___x_3857_, 2);
v_hypotheses_3861_ = lean_ctor_get(v___x_3857_, 3);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3863_ = v___x_3857_;
v_isShared_3864_ = v_isSharedCheck_3871_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_hypotheses_3861_);
lean_inc(v_target_3860_);
lean_inc(v_typeAnalysis_3859_);
lean_inc(v_caches_3858_);
lean_dec(v___x_3857_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3871_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_caches_3858_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v_typeAnalysis_3859_);
lean_ctor_set(v_reuseFailAlloc_3870_, 2, v_target_3860_);
lean_ctor_set(v_reuseFailAlloc_3870_, 3, v_hypotheses_3861_);
v___x_3866_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
lean_ctor_set_uint8(v___x_3866_, sizeof(void*)*4, v___x_3842_);
v___x_3867_ = lean_st_ref_put(v___y_3846_, v___x_3866_);
v___x_3868_ = lean_box(0);
lean_inc(v___y_3855_);
lean_inc_ref(v___y_3854_);
lean_inc(v___y_3853_);
lean_inc_ref(v___y_3852_);
lean_inc(v___y_3851_);
lean_inc_ref(v___y_3850_);
lean_inc(v___y_3849_);
lean_inc_ref(v___y_3848_);
lean_inc(v___y_3847_);
lean_inc(v___y_3846_);
lean_inc_ref(v___y_3845_);
v___x_3869_ = lean_apply_13(v___f_3843_, v___x_3868_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, lean_box(0));
return v___x_3869_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2___boxed(lean_object* v___x_3872_, lean_object* v___f_3873_, lean_object* v_____r_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_){
_start:
{
uint8_t v___x_10026__boxed_3887_; lean_object* v_res_3888_; 
v___x_10026__boxed_3887_ = lean_unbox(v___x_3872_);
v_res_3888_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_10026__boxed_3887_, v___f_3873_, v_____r_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
lean_dec(v___y_3877_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
return v_res_3888_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3890_; lean_object* v___f_3891_; lean_object* v_methods_3892_; 
v___x_3890_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed), 11, 0);
v___f_3891_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__0));
v_methods_3892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_methods_3892_, 0, v___f_3891_);
lean_ctor_set(v_methods_3892_, 1, v___x_3890_);
return v_methods_3892_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__2));
v___x_3895_ = l_Lean_stringToMessageData(v___x_3894_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object* v_upperBound_3896_, lean_object* v___x_3897_, lean_object* v_config_3898_, lean_object* v_a_3899_, lean_object* v_b_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v___y_3914_; uint8_t v___x_3936_; 
v___x_3936_ = lean_nat_dec_lt(v_a_3899_, v_upperBound_3896_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; 
lean_dec(v_a_3899_);
lean_dec_ref(v_config_3898_);
v___x_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3937_, 0, v_b_3900_);
return v___x_3937_;
}
else
{
uint8_t v___x_3938_; lean_object* v_methods_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3938_ = 1;
v_methods_3939_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1);
v___x_3940_ = lean_array_fget_borrowed(v___x_3897_, v_a_3899_);
lean_inc(v___x_3940_);
lean_inc_ref(v_config_3898_);
v___x_3941_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v___x_3938_, v_methods_3939_, v_config_3898_, v___x_3940_, v___y_3902_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v_a_3942_; lean_object* v_snd_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_4006_; 
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
lean_inc(v_a_3942_);
lean_dec_ref_known(v___x_3941_, 1);
v_snd_3943_ = lean_ctor_get(v_b_3900_, 1);
v_isSharedCheck_4006_ = !lean_is_exclusive(v_b_3900_);
if (v_isSharedCheck_4006_ == 0)
{
lean_object* v_unused_4007_; 
v_unused_4007_ = lean_ctor_get(v_b_3900_, 0);
lean_dec(v_unused_4007_);
v___x_3945_ = v_b_3900_;
v_isShared_3946_ = v_isSharedCheck_4006_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_snd_3943_);
lean_dec(v_b_3900_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_4006_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v_type_3947_; lean_object* v_value_3948_; uint8_t v___x_3949_; 
v_type_3947_ = lean_ctor_get(v_a_3942_, 1);
v_value_3948_ = lean_ctor_get(v_a_3942_, 2);
lean_inc_ref(v_type_3947_);
v___x_3949_ = l_Lean_Expr_isFalse(v_type_3947_);
if (v___x_3949_ == 0)
{
lean_object* v_type_3950_; lean_object* v___x_3951_; lean_object* v___f_3952_; uint8_t v___x_3981_; 
lean_del_object(v___x_3945_);
v_type_3950_ = lean_ctor_get(v___x_3940_, 1);
v___x_3951_ = lean_box(0);
lean_inc(v_a_3942_);
lean_inc(v_snd_3943_);
v___f_3952_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1___boxed), 16, 3);
lean_closure_set(v___f_3952_, 0, v_snd_3943_);
lean_closure_set(v___f_3952_, 1, v_a_3942_);
lean_closure_set(v___f_3952_, 2, v___x_3951_);
v___x_3981_ = lean_expr_eqv(v_type_3950_, v_type_3947_);
if (v___x_3981_ == 0)
{
lean_inc_ref(v_type_3947_);
lean_dec(v_snd_3943_);
lean_dec(v_a_3942_);
goto v___jp_3956_;
}
else
{
if (v___x_3949_ == 0)
{
lean_object* v___x_3982_; lean_object* v___x_3983_; 
lean_dec_ref(v___f_3952_);
v___x_3982_ = lean_box(0);
v___x_3983_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(v_snd_3943_, v_a_3942_, v___x_3951_, v___x_3982_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
v___y_3914_ = v___x_3983_;
goto v___jp_3913_;
}
else
{
lean_inc_ref(v_type_3947_);
lean_dec(v_snd_3943_);
lean_dec(v_a_3942_);
goto v___jp_3956_;
}
}
v___jp_3953_:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3954_ = lean_box(0);
v___x_3955_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_3936_, v___f_3952_, v___x_3954_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
v___y_3914_ = v___x_3955_;
goto v___jp_3913_;
}
v___jp_3956_:
{
lean_object* v_toCold_3957_; lean_object* v_options_3958_; uint8_t v_hasTrace_3959_; 
v_toCold_3957_ = lean_ctor_get(v___y_3910_, 0);
v_options_3958_ = lean_ctor_get(v_toCold_3957_, 2);
v_hasTrace_3959_ = lean_ctor_get_uint8(v_options_3958_, sizeof(void*)*1);
if (v_hasTrace_3959_ == 0)
{
lean_dec_ref(v_type_3947_);
goto v___jp_3953_;
}
else
{
lean_object* v_inheritedTraceOptions_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; uint8_t v___x_3963_; 
v_inheritedTraceOptions_3960_ = lean_ctor_get(v_toCold_3957_, 11);
v___x_3961_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3962_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3963_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3960_, v_options_3958_, v___x_3962_);
if (v___x_3963_ == 0)
{
lean_dec_ref(v_type_3947_);
goto v___jp_3953_;
}
else
{
lean_object* v_type_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v_type_3964_ = lean_ctor_get(v___x_3940_, 1);
lean_inc_ref(v_type_3964_);
v___x_3965_ = l_Lean_MessageData_ofExpr(v_type_3964_);
v___x_3966_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3);
v___x_3967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3965_);
lean_ctor_set(v___x_3967_, 1, v___x_3966_);
v___x_3968_ = l_Lean_MessageData_ofExpr(v_type_3947_);
v___x_3969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3967_);
lean_ctor_set(v___x_3969_, 1, v___x_3968_);
v___x_3970_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v___x_3961_, v___x_3969_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v_a_3971_; lean_object* v___x_3972_; 
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
lean_inc(v_a_3971_);
lean_dec_ref_known(v___x_3970_, 1);
v___x_3972_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_3936_, v___f_3952_, v_a_3971_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
v___y_3914_ = v___x_3972_;
goto v___jp_3913_;
}
else
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
lean_dec_ref(v___f_3952_);
lean_dec(v_a_3899_);
lean_dec_ref(v_config_3898_);
v_a_3973_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3970_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3970_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3984_; 
lean_inc_ref(v_value_3948_);
lean_dec(v_a_3942_);
lean_dec(v_a_3899_);
lean_dec_ref(v_config_3898_);
v___x_3984_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_3948_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3996_; 
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_3996_ == 0)
{
lean_object* v_unused_3997_; 
v_unused_3997_ = lean_ctor_get(v___x_3984_, 0);
lean_dec(v_unused_3997_);
v___x_3986_ = v___x_3984_;
v_isShared_3987_ = v_isSharedCheck_3996_;
goto v_resetjp_3985_;
}
else
{
lean_dec(v___x_3984_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3996_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3991_; 
v___x_3988_ = lean_box(v___x_3936_);
v___x_3989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3988_);
if (v_isShared_3946_ == 0)
{
lean_ctor_set(v___x_3945_, 0, v___x_3989_);
v___x_3991_ = v___x_3945_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v___x_3989_);
lean_ctor_set(v_reuseFailAlloc_3995_, 1, v_snd_3943_);
v___x_3991_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
lean_object* v___x_3993_; 
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 0, v___x_3991_);
v___x_3993_ = v___x_3986_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3991_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
}
else
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4005_; 
lean_del_object(v___x_3945_);
lean_dec(v_snd_3943_);
v_a_3998_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_4000_ = v___x_3984_;
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3984_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4003_; 
if (v_isShared_4001_ == 0)
{
v___x_4003_ = v___x_4000_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_a_3998_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
}
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
lean_dec_ref(v_b_3900_);
lean_dec(v_a_3899_);
lean_dec_ref(v_config_3898_);
v_a_4008_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_3941_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_3941_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4008_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
v___jp_3913_:
{
if (lean_obj_tag(v___y_3914_) == 0)
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3927_; 
v_a_3915_ = lean_ctor_get(v___y_3914_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___y_3914_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3917_ = v___y_3914_;
v_isShared_3918_ = v_isSharedCheck_3927_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___y_3914_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3927_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
if (lean_obj_tag(v_a_3915_) == 0)
{
lean_object* v_a_3919_; lean_object* v___x_3921_; 
lean_dec(v_a_3899_);
lean_dec_ref(v_config_3898_);
v_a_3919_ = lean_ctor_get(v_a_3915_, 0);
lean_inc(v_a_3919_);
lean_dec_ref_known(v_a_3915_, 1);
if (v_isShared_3918_ == 0)
{
lean_ctor_set(v___x_3917_, 0, v_a_3919_);
v___x_3921_ = v___x_3917_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3919_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
lean_del_object(v___x_3917_);
v_a_3923_ = lean_ctor_get(v_a_3915_, 0);
lean_inc(v_a_3923_);
lean_dec_ref_known(v_a_3915_, 1);
v___x_3924_ = lean_unsigned_to_nat(1u);
v___x_3925_ = lean_nat_add(v_a_3899_, v___x_3924_);
lean_dec(v_a_3899_);
v_a_3899_ = v___x_3925_;
v_b_3900_ = v_a_3923_;
goto _start;
}
}
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
lean_dec(v_a_3899_);
lean_dec_ref(v_config_3898_);
v_a_3928_ = lean_ctor_get(v___y_3914_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___y_3914_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___y_3914_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___y_3914_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_4016_ = _args[0];
lean_object* v___x_4017_ = _args[1];
lean_object* v_config_4018_ = _args[2];
lean_object* v_a_4019_ = _args[3];
lean_object* v_b_4020_ = _args[4];
lean_object* v___y_4021_ = _args[5];
lean_object* v___y_4022_ = _args[6];
lean_object* v___y_4023_ = _args[7];
lean_object* v___y_4024_ = _args[8];
lean_object* v___y_4025_ = _args[9];
lean_object* v___y_4026_ = _args[10];
lean_object* v___y_4027_ = _args[11];
lean_object* v___y_4028_ = _args[12];
lean_object* v___y_4029_ = _args[13];
lean_object* v___y_4030_ = _args[14];
lean_object* v___y_4031_ = _args[15];
lean_object* v___y_4032_ = _args[16];
_start:
{
lean_object* v_res_4033_; 
v_res_4033_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_upperBound_4016_, v___x_4017_, v_config_4018_, v_a_4019_, v_b_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
lean_dec_ref(v___x_4017_);
lean_dec(v_upperBound_4016_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(lean_object* v_config_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
lean_object* v___x_4047_; lean_object* v_hypotheses_4048_; lean_object* v___x_4049_; lean_object* v_newHyps_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4047_ = lean_st_ref_get(v___y_4036_);
v_hypotheses_4048_ = lean_ctor_get(v___x_4047_, 3);
lean_inc_ref(v_hypotheses_4048_);
lean_dec(v___x_4047_);
v___x_4049_ = lean_array_get_size(v_hypotheses_4048_);
v_newHyps_4050_ = lean_mk_empty_array_with_capacity(v___x_4049_);
v___x_4051_ = lean_unsigned_to_nat(0u);
v___x_4052_ = lean_box(0);
v___x_4053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4052_);
lean_ctor_set(v___x_4053_, 1, v_newHyps_4050_);
v___x_4054_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v___x_4049_, v_hypotheses_4048_, v_config_4034_, v___x_4051_, v___x_4053_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_);
lean_dec_ref(v_hypotheses_4048_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4084_; 
v_a_4055_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4084_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4084_ == 0)
{
v___x_4057_ = v___x_4054_;
v_isShared_4058_ = v_isSharedCheck_4084_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4054_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4084_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v_fst_4059_; 
v_fst_4059_ = lean_ctor_get(v_a_4055_, 0);
if (lean_obj_tag(v_fst_4059_) == 0)
{
lean_object* v_snd_4060_; lean_object* v___x_4061_; lean_object* v_caches_4062_; lean_object* v_typeAnalysis_4063_; lean_object* v_target_4064_; uint8_t v_didChange_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4078_; 
v_snd_4060_ = lean_ctor_get(v_a_4055_, 1);
lean_inc(v_snd_4060_);
lean_dec(v_a_4055_);
v___x_4061_ = lean_st_ref_take(v___y_4036_);
v_caches_4062_ = lean_ctor_get(v___x_4061_, 0);
v_typeAnalysis_4063_ = lean_ctor_get(v___x_4061_, 1);
v_target_4064_ = lean_ctor_get(v___x_4061_, 2);
v_didChange_4065_ = lean_ctor_get_uint8(v___x_4061_, sizeof(void*)*4);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4078_ == 0)
{
lean_object* v_unused_4079_; 
v_unused_4079_ = lean_ctor_get(v___x_4061_, 3);
lean_dec(v_unused_4079_);
v___x_4067_ = v___x_4061_;
v_isShared_4068_ = v_isSharedCheck_4078_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_target_4064_);
lean_inc(v_typeAnalysis_4063_);
lean_inc(v_caches_4062_);
lean_dec(v___x_4061_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4078_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 3, v_snd_4060_);
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_caches_4062_);
lean_ctor_set(v_reuseFailAlloc_4077_, 1, v_typeAnalysis_4063_);
lean_ctor_set(v_reuseFailAlloc_4077_, 2, v_target_4064_);
lean_ctor_set(v_reuseFailAlloc_4077_, 3, v_snd_4060_);
lean_ctor_set_uint8(v_reuseFailAlloc_4077_, sizeof(void*)*4, v_didChange_4065_);
v___x_4070_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
lean_object* v___x_4071_; uint8_t v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4075_; 
v___x_4071_ = lean_st_ref_put(v___y_4036_, v___x_4070_);
v___x_4072_ = 0;
v___x_4073_ = lean_box(v___x_4072_);
if (v_isShared_4058_ == 0)
{
lean_ctor_set(v___x_4057_, 0, v___x_4073_);
v___x_4075_ = v___x_4057_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4073_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
}
else
{
lean_object* v_val_4080_; lean_object* v___x_4082_; 
lean_inc_ref(v_fst_4059_);
lean_dec(v_a_4055_);
v_val_4080_ = lean_ctor_get(v_fst_4059_, 0);
lean_inc(v_val_4080_);
lean_dec_ref_known(v_fst_4059_, 1);
if (v_isShared_4058_ == 0)
{
lean_ctor_set(v___x_4057_, 0, v_val_4080_);
v___x_4082_ = v___x_4057_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_val_4080_);
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
else
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4092_; 
v_a_4085_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4087_ = v___x_4054_;
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_4054_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4090_; 
if (v_isShared_4088_ == 0)
{
v___x_4090_ = v___x_4087_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_a_4085_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed(lean_object* v_config_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_){
_start:
{
lean_object* v_res_4106_; 
v_res_4106_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(v_config_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
lean_dec(v___y_4096_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v_config_4119_; lean_object* v___x_4120_; lean_object* v_maxSteps_4121_; lean_object* v_target_4122_; lean_object* v___x_4123_; lean_object* v_config_4124_; lean_object* v___f_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v_config_4119_ = lean_ctor_get(v___y_4107_, 0);
v___x_4120_ = lean_st_ref_get(v___y_4108_);
v_maxSteps_4121_ = lean_ctor_get(v_config_4119_, 1);
v_target_4122_ = lean_ctor_get(v___x_4120_, 2);
lean_inc_ref(v_target_4122_);
lean_dec(v___x_4120_);
v___x_4123_ = lean_unsigned_to_nat(2u);
lean_inc(v_maxSteps_4121_);
v_config_4124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_config_4124_, 0, v_maxSteps_4121_);
lean_ctor_set(v_config_4124_, 1, v___x_4123_);
v___f_4125_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed), 13, 1);
lean_closure_set(v___f_4125_, 0, v_config_4124_);
v___x_4126_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_4122_);
lean_dec_ref(v_target_4122_);
v___x_4127_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v___x_4126_, v___f_4125_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___boxed(lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec(v___y_4130_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(lean_object* v_cls_4149_, lean_object* v_msg_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_){
_start:
{
lean_object* v___x_4163_; 
v___x_4163_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_cls_4149_, v_msg_4150_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___boxed(lean_object* v_cls_4164_, lean_object* v_msg_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(v_cls_4164_, v_msg_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec(v___y_4167_);
lean_dec_ref(v___y_4166_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(lean_object* v_upperBound_4179_, lean_object* v___x_4180_, lean_object* v_config_4181_, lean_object* v_inst_4182_, lean_object* v_R_4183_, lean_object* v_a_4184_, lean_object* v_b_4185_, lean_object* v_c_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v___x_4199_; 
v___x_4199_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_upperBound_4179_, v___x_4180_, v_config_4181_, v_a_4184_, v_b_4185_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_4200_ = _args[0];
lean_object* v___x_4201_ = _args[1];
lean_object* v_config_4202_ = _args[2];
lean_object* v_inst_4203_ = _args[3];
lean_object* v_R_4204_ = _args[4];
lean_object* v_a_4205_ = _args[5];
lean_object* v_b_4206_ = _args[6];
lean_object* v_c_4207_ = _args[7];
lean_object* v___y_4208_ = _args[8];
lean_object* v___y_4209_ = _args[9];
lean_object* v___y_4210_ = _args[10];
lean_object* v___y_4211_ = _args[11];
lean_object* v___y_4212_ = _args[12];
lean_object* v___y_4213_ = _args[13];
lean_object* v___y_4214_ = _args[14];
lean_object* v___y_4215_ = _args[15];
lean_object* v___y_4216_ = _args[16];
lean_object* v___y_4217_ = _args[17];
lean_object* v___y_4218_ = _args[18];
lean_object* v___y_4219_ = _args[19];
_start:
{
lean_object* v_res_4220_; 
v_res_4220_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(v_upperBound_4200_, v___x_4201_, v_config_4202_, v_inst_4203_, v_R_4204_, v_a_4205_, v_b_4206_, v_c_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec_ref(v___x_4201_);
lean_dec(v_upperBound_4200_);
return v_res_4220_;
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
