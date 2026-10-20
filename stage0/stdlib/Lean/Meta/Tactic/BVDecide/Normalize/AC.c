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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Operations mismatch:\n      the left-hand-side has operation "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\n        "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "\n      but the right-hand-side has operation "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Canonicalizing with respect to operation: '"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "'."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Failed to recognize operation: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7___boxed(lean_object**);
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
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Canonicalizing: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4;
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
lean_object* v___x_491_; lean_object* v_env_492_; uint8_t v___x_493_; lean_object* v_env_494_; lean_object* v___x_495_; lean_object* v_toCold_496_; lean_object* v_mctx_497_; lean_object* v_lctx_498_; lean_object* v_options_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_491_ = lean_st_ref_get(v___y_489_);
v_env_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc_ref(v_env_492_);
lean_dec(v___x_491_);
v___x_493_ = 0;
v_env_494_ = l_Lean_Environment_setRecordingDeps(v_env_492_, v___x_493_);
v___x_495_ = lean_st_ref_get(v___y_487_);
v_toCold_496_ = lean_ctor_get(v___y_488_, 0);
v_mctx_497_ = lean_ctor_get(v___x_495_, 0);
lean_inc_ref(v_mctx_497_);
lean_dec(v___x_495_);
v_lctx_498_ = lean_ctor_get(v___y_486_, 2);
v_options_499_ = lean_ctor_get(v_toCold_496_, 2);
lean_inc_ref(v_options_499_);
lean_inc_ref(v_lctx_498_);
v___x_500_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_500_, 0, v_env_494_);
lean_ctor_set(v___x_500_, 1, v_mctx_497_);
lean_ctor_set(v___x_500_, 2, v_lctx_498_);
lean_ctor_set(v___x_500_, 3, v_options_499_);
v___x_501_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
lean_ctor_set(v___x_501_, 1, v_msgData_485_);
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1___boxed(lean_object* v_msgData_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msgData_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(lean_object* v_msg_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v_ref_516_; lean_object* v___x_517_; lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_526_; 
v_ref_516_ = lean_ctor_get(v___y_513_, 2);
v___x_517_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_526_ == 0)
{
v___x_520_ = v___x_517_;
v_isShared_521_ = v_isSharedCheck_526_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_526_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v___x_524_; 
lean_inc(v_ref_516_);
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v_ref_516_);
lean_ctor_set(v___x_522_, 1, v_a_518_);
if (v_isShared_521_ == 0)
{
lean_ctor_set_tag(v___x_520_, 1);
lean_ctor_set(v___x_520_, 0, v___x_522_);
v___x_524_ = v___x_520_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg___boxed(lean_object* v_msg_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__0(lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
if (lean_obj_tag(v_a_534_) == 0)
{
lean_object* v___x_536_; 
v___x_536_ = l_List_reverse___redArg(v_a_535_);
return v___x_536_;
}
else
{
lean_object* v_head_537_; lean_object* v_tail_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_547_; 
v_head_537_ = lean_ctor_get(v_a_534_, 0);
v_tail_538_ = lean_ctor_get(v_a_534_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_a_534_);
if (v_isSharedCheck_547_ == 0)
{
v___x_540_ = v_a_534_;
v_isShared_541_ = v_isSharedCheck_547_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_tail_538_);
lean_inc(v_head_537_);
lean_dec(v_a_534_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_547_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_542_ = l_Lean_MessageData_ofExpr(v_head_537_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v_a_535_);
lean_ctor_set(v___x_540_, 0, v___x_542_);
v___x_544_ = v___x_540_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_a_535_);
v___x_544_ = v_reuseFailAlloc_546_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
v_a_534_ = v_tail_538_;
v_a_535_ = v___x_544_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__0));
v___x_550_ = l_Lean_stringToMessageData(v___x_549_);
return v___x_550_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__2));
v___x_553_ = l_Lean_stringToMessageData(v___x_552_);
return v___x_553_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__4));
v___x_556_ = l_Lean_stringToMessageData(v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(lean_object* v_idx_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v_varToExpr_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v_varToExpr_566_ = lean_ctor_get(v_a_558_, 2);
v___x_567_ = lean_array_get_size(v_varToExpr_566_);
v___x_568_ = lean_nat_dec_lt(v_idx_557_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
lean_inc_ref(v_varToExpr_566_);
lean_dec_ref(v_a_558_);
v___x_569_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1);
v___x_570_ = l_Nat_reprFast(v_idx_557_);
v___x_571_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
v___x_572_ = l_Lean_MessageData_ofFormat(v___x_571_);
v___x_573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_569_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3);
v___x_575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_573_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = l_Nat_reprFast(v___x_567_);
v___x_577_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
v___x_578_ = l_Lean_MessageData_ofFormat(v___x_577_);
v___x_579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_575_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5);
v___x_581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = lean_array_to_list(v_varToExpr_566_);
v___x_583_ = lean_box(0);
v___x_584_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__0(v___x_582_, v___x_583_);
v___x_585_ = l_Lean_MessageData_ofList(v___x_584_);
v___x_586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_581_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v___x_586_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
return v___x_587_;
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_array_fget(v_varToExpr_566_, v_idx_557_);
lean_dec(v_idx_557_);
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
lean_ctor_set(v___x_589_, 1, v_a_558_);
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___boxed(lean_object* v_idx_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(v_idx_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(lean_object* v_00_u03b1_601_, lean_object* v_msg_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_602_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___boxed(lean_object* v_00_u03b1_612_, lean_object* v_msg_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(v_00_u03b1_612_, v_msg_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec_ref(v___y_614_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(lean_object* v_c_623_){
_start:
{
lean_object* v___y_625_; 
if (lean_obj_tag(v_c_623_) == 0)
{
lean_object* v___x_629_; 
v___x_629_ = lean_unsigned_to_nat(0u);
v___y_625_ = v___x_629_;
goto v___jp_624_;
}
else
{
lean_object* v_val_630_; 
v_val_630_ = lean_ctor_get(v_c_623_, 0);
v___y_625_ = v_val_630_;
goto v___jp_624_;
}
v___jp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = lean_nat_add(v___y_625_, v___x_626_);
v___x_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0___boxed(lean_object* v_c_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v_c_631_);
lean_dec(v_c_631_);
return v_res_632_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_box(0);
v___x_634_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(lean_object* v_a_635_, lean_object* v_x_636_){
_start:
{
if (lean_obj_tag(v_x_636_) == 0)
{
lean_object* v___x_637_; lean_object* v_val_638_; lean_object* v___x_639_; 
v___x_637_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0, &l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0);
v_val_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_val_638_);
v___x_639_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_639_, 0, v_a_635_);
lean_ctor_set(v___x_639_, 1, v_val_638_);
lean_ctor_set(v___x_639_, 2, v_x_636_);
return v___x_639_;
}
else
{
lean_object* v_key_640_; lean_object* v_value_641_; lean_object* v_tail_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_657_; 
v_key_640_ = lean_ctor_get(v_x_636_, 0);
v_value_641_ = lean_ctor_get(v_x_636_, 1);
v_tail_642_ = lean_ctor_get(v_x_636_, 2);
v_isSharedCheck_657_ = !lean_is_exclusive(v_x_636_);
if (v_isSharedCheck_657_ == 0)
{
v___x_644_ = v_x_636_;
v_isShared_645_ = v_isSharedCheck_657_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_tail_642_);
lean_inc(v_value_641_);
lean_inc(v_key_640_);
lean_dec(v_x_636_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_657_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
uint8_t v___x_646_; 
v___x_646_ = lean_nat_dec_eq(v_key_640_, v_a_635_);
if (v___x_646_ == 0)
{
lean_object* v_tail_647_; lean_object* v___x_649_; 
v_tail_647_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(v_a_635_, v_tail_642_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 2, v_tail_647_);
v___x_649_ = v___x_644_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_key_640_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_value_641_);
lean_ctor_set(v_reuseFailAlloc_650_, 2, v_tail_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v_val_653_; lean_object* v___x_655_; 
lean_dec(v_key_640_);
v___x_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_651_, 0, v_value_641_);
v___x_652_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v___x_651_);
lean_dec_ref_known(v___x_651_, 1);
v_val_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_val_653_);
lean_dec(v___x_652_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 1, v_val_653_);
lean_ctor_set(v___x_644_, 0, v_a_635_);
v___x_655_ = v___x_644_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_635_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_val_653_);
lean_ctor_set(v_reuseFailAlloc_656_, 2, v_tail_642_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
if (lean_obj_tag(v_x_659_) == 0)
{
return v_x_658_;
}
else
{
lean_object* v_key_660_; lean_object* v_value_661_; lean_object* v_tail_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_685_; 
v_key_660_ = lean_ctor_get(v_x_659_, 0);
v_value_661_ = lean_ctor_get(v_x_659_, 1);
v_tail_662_ = lean_ctor_get(v_x_659_, 2);
v_isSharedCheck_685_ = !lean_is_exclusive(v_x_659_);
if (v_isSharedCheck_685_ == 0)
{
v___x_664_ = v_x_659_;
v_isShared_665_ = v_isSharedCheck_685_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_tail_662_);
lean_inc(v_value_661_);
lean_inc(v_key_660_);
lean_dec(v_x_659_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_685_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; uint64_t v___x_667_; uint64_t v___x_668_; uint64_t v___x_669_; uint64_t v_fold_670_; uint64_t v___x_671_; uint64_t v___x_672_; uint64_t v___x_673_; size_t v___x_674_; size_t v___x_675_; size_t v___x_676_; size_t v___x_677_; size_t v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_666_ = lean_array_get_size(v_x_658_);
v___x_667_ = lean_uint64_of_nat(v_key_660_);
v___x_668_ = 32ULL;
v___x_669_ = lean_uint64_shift_right(v___x_667_, v___x_668_);
v_fold_670_ = lean_uint64_xor(v___x_667_, v___x_669_);
v___x_671_ = 16ULL;
v___x_672_ = lean_uint64_shift_right(v_fold_670_, v___x_671_);
v___x_673_ = lean_uint64_xor(v_fold_670_, v___x_672_);
v___x_674_ = lean_uint64_to_usize(v___x_673_);
v___x_675_ = lean_usize_of_nat(v___x_666_);
v___x_676_ = ((size_t)1ULL);
v___x_677_ = lean_usize_sub(v___x_675_, v___x_676_);
v___x_678_ = lean_usize_land(v___x_674_, v___x_677_);
v___x_679_ = lean_array_uget_borrowed(v_x_658_, v___x_678_);
lean_inc(v___x_679_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 2, v___x_679_);
v___x_681_ = v___x_664_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_key_660_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_value_661_);
lean_ctor_set(v_reuseFailAlloc_684_, 2, v___x_679_);
v___x_681_ = v_reuseFailAlloc_684_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; 
v___x_682_ = lean_array_uset(v_x_658_, v___x_678_, v___x_681_);
v_x_658_ = v___x_682_;
v_x_659_ = v_tail_662_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(lean_object* v_i_686_, lean_object* v_source_687_, lean_object* v_target_688_){
_start:
{
lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = lean_array_get_size(v_source_687_);
v___x_690_ = lean_nat_dec_lt(v_i_686_, v___x_689_);
if (v___x_690_ == 0)
{
lean_dec_ref(v_source_687_);
lean_dec(v_i_686_);
return v_target_688_;
}
else
{
lean_object* v_es_691_; lean_object* v___x_692_; lean_object* v_source_693_; lean_object* v_target_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v_es_691_ = lean_array_fget(v_source_687_, v_i_686_);
v___x_692_ = lean_box(0);
v_source_693_ = lean_array_fset(v_source_687_, v_i_686_, v___x_692_);
v_target_694_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(v_target_688_, v_es_691_);
v___x_695_ = lean_unsigned_to_nat(1u);
v___x_696_ = lean_nat_add(v_i_686_, v___x_695_);
lean_dec(v_i_686_);
v_i_686_ = v___x_696_;
v_source_687_ = v_source_693_;
v_target_688_ = v_target_694_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(lean_object* v_data_698_){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v_nbuckets_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_699_ = lean_array_get_size(v_data_698_);
v___x_700_ = lean_unsigned_to_nat(2u);
v_nbuckets_701_ = lean_nat_mul(v___x_699_, v___x_700_);
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = lean_box(0);
v___x_704_ = lean_mk_array(v_nbuckets_701_, v___x_703_);
v___x_705_ = lean_array_propagate_mark(v_data_698_, v___x_704_);
v___x_706_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(v___x_702_, v_data_698_, v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(lean_object* v_a_707_, lean_object* v_x_708_){
_start:
{
if (lean_obj_tag(v_x_708_) == 0)
{
uint8_t v___x_709_; 
v___x_709_ = 0;
return v___x_709_;
}
else
{
lean_object* v_key_710_; lean_object* v_tail_711_; uint8_t v___x_712_; 
v_key_710_ = lean_ctor_get(v_x_708_, 0);
v_tail_711_ = lean_ctor_get(v_x_708_, 2);
v___x_712_ = lean_nat_dec_eq(v_key_710_, v_a_707_);
if (v___x_712_ == 0)
{
v_x_708_ = v_tail_711_;
goto _start;
}
else
{
return v___x_712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_714_, lean_object* v_x_715_){
_start:
{
uint8_t v_res_716_; lean_object* v_r_717_; 
v_res_716_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_714_, v_x_715_);
lean_dec(v_x_715_);
lean_dec(v_a_714_);
v_r_717_ = lean_box(v_res_716_);
return v_r_717_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(lean_object* v_m_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_size_720_; lean_object* v_buckets_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_769_; 
v_size_720_ = lean_ctor_get(v_m_718_, 0);
v_buckets_721_ = lean_ctor_get(v_m_718_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v_m_718_);
if (v_isSharedCheck_769_ == 0)
{
v___x_723_ = v_m_718_;
v_isShared_724_ = v_isSharedCheck_769_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_buckets_721_);
lean_inc(v_size_720_);
lean_dec(v_m_718_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_769_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; uint64_t v___x_726_; uint64_t v___x_727_; uint64_t v___x_728_; uint64_t v_fold_729_; uint64_t v___x_730_; uint64_t v___x_731_; uint64_t v___x_732_; size_t v___x_733_; size_t v___x_734_; size_t v___x_735_; size_t v___x_736_; size_t v___x_737_; lean_object* v_bkt_738_; uint8_t v___x_739_; 
v___x_725_ = lean_array_get_size(v_buckets_721_);
v___x_726_ = lean_uint64_of_nat(v_a_719_);
v___x_727_ = 32ULL;
v___x_728_ = lean_uint64_shift_right(v___x_726_, v___x_727_);
v_fold_729_ = lean_uint64_xor(v___x_726_, v___x_728_);
v___x_730_ = 16ULL;
v___x_731_ = lean_uint64_shift_right(v_fold_729_, v___x_730_);
v___x_732_ = lean_uint64_xor(v_fold_729_, v___x_731_);
v___x_733_ = lean_uint64_to_usize(v___x_732_);
v___x_734_ = lean_usize_of_nat(v___x_725_);
v___x_735_ = ((size_t)1ULL);
v___x_736_ = lean_usize_sub(v___x_734_, v___x_735_);
v___x_737_ = lean_usize_land(v___x_733_, v___x_736_);
v_bkt_738_ = lean_array_uget_borrowed(v_buckets_721_, v___x_737_);
v___x_739_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_719_, v_bkt_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v_size_x27_741_; lean_object* v___x_742_; lean_object* v_buckets_x27_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_740_ = lean_unsigned_to_nat(1u);
v_size_x27_741_ = lean_nat_add(v_size_720_, v___x_740_);
lean_dec(v_size_720_);
lean_inc(v_bkt_738_);
v___x_742_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_742_, 0, v_a_719_);
lean_ctor_set(v___x_742_, 1, v___x_740_);
lean_ctor_set(v___x_742_, 2, v_bkt_738_);
v_buckets_x27_743_ = lean_array_uset(v_buckets_721_, v___x_737_, v___x_742_);
v___x_744_ = lean_unsigned_to_nat(4u);
v___x_745_ = lean_nat_mul(v_size_x27_741_, v___x_744_);
v___x_746_ = lean_unsigned_to_nat(3u);
v___x_747_ = lean_nat_div(v___x_745_, v___x_746_);
lean_dec(v___x_745_);
v___x_748_ = lean_array_get_size(v_buckets_x27_743_);
v___x_749_ = lean_nat_dec_le(v___x_747_, v___x_748_);
lean_dec(v___x_747_);
if (v___x_749_ == 0)
{
lean_object* v_val_750_; lean_object* v___x_752_; 
v_val_750_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_743_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v_val_750_);
lean_ctor_set(v___x_723_, 0, v_size_x27_741_);
v___x_752_ = v___x_723_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_size_x27_741_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_val_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
else
{
lean_object* v___x_755_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v_buckets_x27_743_);
lean_ctor_set(v___x_723_, 0, v_size_x27_741_);
v___x_755_ = v___x_723_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_size_x27_741_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_buckets_x27_743_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
else
{
lean_object* v___x_757_; lean_object* v_buckets_x27_758_; lean_object* v_bkt_x27_759_; lean_object* v___y_761_; uint8_t v___x_766_; 
lean_inc(v_bkt_738_);
v___x_757_ = lean_box(0);
v_buckets_x27_758_ = lean_array_uset(v_buckets_721_, v___x_737_, v___x_757_);
lean_inc(v_a_719_);
v_bkt_x27_759_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(v_a_719_, v_bkt_738_);
v___x_766_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_719_, v_bkt_x27_759_);
lean_dec(v_a_719_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_unsigned_to_nat(1u);
v___x_768_ = lean_nat_sub(v_size_720_, v___x_767_);
lean_dec(v_size_720_);
v___y_761_ = v___x_768_;
goto v___jp_760_;
}
else
{
v___y_761_ = v_size_720_;
goto v___jp_760_;
}
v___jp_760_:
{
lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_762_ = lean_array_uset(v_buckets_x27_758_, v___x_737_, v_bkt_x27_759_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v___x_762_);
lean_ctor_set(v___x_723_, 0, v___y_761_);
v___x_764_ = v___x_723_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___y_761_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v___x_762_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(lean_object* v_coeff_770_, lean_object* v_e_771_, lean_object* v_a_772_){
_start:
{
lean_object* v___x_774_; lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_792_; 
v___x_774_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_771_, v_a_772_);
v_a_775_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_792_ == 0)
{
v___x_777_ = v___x_774_;
v_isShared_778_ = v_isSharedCheck_792_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_792_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v_fst_779_; lean_object* v_snd_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_791_; 
v_fst_779_ = lean_ctor_get(v_a_775_, 0);
v_snd_780_ = lean_ctor_get(v_a_775_, 1);
v_isSharedCheck_791_ = !lean_is_exclusive(v_a_775_);
if (v_isSharedCheck_791_ == 0)
{
v___x_782_ = v_a_775_;
v_isShared_783_ = v_isSharedCheck_791_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_snd_780_);
lean_inc(v_fst_779_);
lean_dec(v_a_775_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_791_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_784_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(v_coeff_770_, v_fst_779_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_784_);
v___x_786_ = v___x_782_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_snd_780_);
v___x_786_ = v_reuseFailAlloc_790_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_788_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_786_);
v___x_788_ = v___x_777_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___boxed(lean_object* v_coeff_793_, lean_object* v_e_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_793_, v_e_794_, v_a_795_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(lean_object* v_coeff_798_, lean_object* v_e_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_798_, v_e_799_, v_a_800_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___boxed(lean_object* v_coeff_809_, lean_object* v_e_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(v_coeff_809_, v_e_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
return v_res_819_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(lean_object* v_00_u03b2_820_, lean_object* v_a_821_, lean_object* v_x_822_){
_start:
{
uint8_t v___x_823_; 
v___x_823_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_821_, v_x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_824_, lean_object* v_a_825_, lean_object* v_x_826_){
_start:
{
uint8_t v_res_827_; lean_object* v_r_828_; 
v_res_827_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(v_00_u03b2_824_, v_a_825_, v_x_826_);
lean_dec(v_x_826_);
lean_dec(v_a_825_);
v_r_828_ = lean_box(v_res_827_);
return v_r_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1(lean_object* v_00_u03b2_829_, lean_object* v_data_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_data_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_832_, lean_object* v_i_833_, lean_object* v_source_834_, lean_object* v_target_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(v_i_833_, v_source_834_, v_target_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_837_, lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_838_, v_x_839_);
return v___x_840_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_841_; double v___x_842_; 
v___x_841_ = lean_unsigned_to_nat(0u);
v___x_842_ = lean_float_of_nat(v___x_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(lean_object* v_cls_846_, lean_object* v_msg_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_ref_854_; lean_object* v___x_855_; lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_902_; 
v_ref_854_ = lean_ctor_get(v___y_851_, 2);
v___x_855_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_847_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_902_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_902_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_902_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; lean_object* v_traceState_861_; lean_object* v_env_862_; lean_object* v_nextMacroScope_863_; lean_object* v_ngen_864_; lean_object* v_auxDeclNGen_865_; lean_object* v_cache_866_; lean_object* v_recordedDeps_867_; lean_object* v_messages_868_; lean_object* v_infoState_869_; lean_object* v_snapshotTasks_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_901_; 
v___x_860_ = lean_st_ref_take(v___y_852_);
v_traceState_861_ = lean_ctor_get(v___x_860_, 4);
v_env_862_ = lean_ctor_get(v___x_860_, 0);
v_nextMacroScope_863_ = lean_ctor_get(v___x_860_, 1);
v_ngen_864_ = lean_ctor_get(v___x_860_, 2);
v_auxDeclNGen_865_ = lean_ctor_get(v___x_860_, 3);
v_cache_866_ = lean_ctor_get(v___x_860_, 5);
v_recordedDeps_867_ = lean_ctor_get(v___x_860_, 6);
v_messages_868_ = lean_ctor_get(v___x_860_, 7);
v_infoState_869_ = lean_ctor_get(v___x_860_, 8);
v_snapshotTasks_870_ = lean_ctor_get(v___x_860_, 9);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_901_ == 0)
{
v___x_872_ = v___x_860_;
v_isShared_873_ = v_isSharedCheck_901_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_snapshotTasks_870_);
lean_inc(v_infoState_869_);
lean_inc(v_messages_868_);
lean_inc(v_recordedDeps_867_);
lean_inc(v_cache_866_);
lean_inc(v_traceState_861_);
lean_inc(v_auxDeclNGen_865_);
lean_inc(v_ngen_864_);
lean_inc(v_nextMacroScope_863_);
lean_inc(v_env_862_);
lean_dec(v___x_860_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_901_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
uint64_t v_tid_874_; lean_object* v_traces_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_900_; 
v_tid_874_ = lean_ctor_get_uint64(v_traceState_861_, sizeof(void*)*1);
v_traces_875_ = lean_ctor_get(v_traceState_861_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v_traceState_861_);
if (v_isSharedCheck_900_ == 0)
{
v___x_877_ = v_traceState_861_;
v_isShared_878_ = v_isSharedCheck_900_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_traces_875_);
lean_dec(v_traceState_861_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_900_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_880_; double v___x_881_; uint8_t v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_879_ = lean_box(0);
v___x_880_ = lean_box(0);
v___x_881_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_882_ = 0;
v___x_883_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_884_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_884_, 0, v_cls_846_);
lean_ctor_set(v___x_884_, 1, v___x_880_);
lean_ctor_set(v___x_884_, 2, v___x_883_);
lean_ctor_set_float(v___x_884_, sizeof(void*)*3, v___x_881_);
lean_ctor_set_float(v___x_884_, sizeof(void*)*3 + 8, v___x_881_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*3 + 16, v___x_882_);
v___x_885_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_886_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v_a_856_);
lean_ctor_set(v___x_886_, 2, v___x_885_);
lean_inc(v_ref_854_);
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v_ref_854_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = l_Lean_PersistentArray_push___redArg(v_traces_875_, v___x_887_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_888_);
v___x_890_ = v___x_877_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_888_);
lean_ctor_set_uint64(v_reuseFailAlloc_899_, sizeof(void*)*1, v_tid_874_);
v___x_890_ = v_reuseFailAlloc_899_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_892_; 
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 4, v___x_890_);
v___x_892_ = v___x_872_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_env_862_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_nextMacroScope_863_);
lean_ctor_set(v_reuseFailAlloc_898_, 2, v_ngen_864_);
lean_ctor_set(v_reuseFailAlloc_898_, 3, v_auxDeclNGen_865_);
lean_ctor_set(v_reuseFailAlloc_898_, 4, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_898_, 5, v_cache_866_);
lean_ctor_set(v_reuseFailAlloc_898_, 6, v_recordedDeps_867_);
lean_ctor_set(v_reuseFailAlloc_898_, 7, v_messages_868_);
lean_ctor_set(v_reuseFailAlloc_898_, 8, v_infoState_869_);
lean_ctor_set(v_reuseFailAlloc_898_, 9, v_snapshotTasks_870_);
v___x_892_ = v_reuseFailAlloc_898_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_893_ = lean_st_ref_put(v___y_852_, v___x_892_);
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_879_);
lean_ctor_set(v___x_894_, 1, v___y_848_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_894_);
v___x_896_ = v___x_858_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___boxed(lean_object* v_cls_903_, lean_object* v_msg_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_903_, v_msg_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
return v_res_911_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6(void){
_start:
{
lean_object* v_cls_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_cls_922_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_924_ = l_Lean_Name_append(v___x_923_, v_cls_922_);
return v___x_924_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__7));
v___x_927_ = l_Lean_stringToMessageData(v___x_926_);
return v___x_927_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__9));
v___x_930_ = l_Lean_stringToMessageData(v___x_929_);
return v___x_930_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__11));
v___x_933_ = l_Lean_stringToMessageData(v___x_932_);
return v___x_933_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__13));
v___x_936_ = l_Lean_stringToMessageData(v___x_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(lean_object* v_op_937_, lean_object* v_coeff_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
if (lean_obj_tag(v_a_939_) == 5)
{
lean_object* v_fn_948_; 
v_fn_948_ = lean_ctor_get(v_a_939_, 0);
if (lean_obj_tag(v_fn_948_) == 5)
{
lean_object* v_arg_949_; lean_object* v_fn_950_; lean_object* v_arg_951_; uint8_t v___x_952_; 
v_arg_949_ = lean_ctor_get(v_a_939_, 1);
v_fn_950_ = lean_ctor_get(v_fn_948_, 0);
v_arg_951_ = lean_ctor_get(v_fn_948_, 1);
lean_inc_ref(v_fn_950_);
v___x_952_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(v_fn_950_);
if (v___x_952_ == 0)
{
lean_object* v_toCold_953_; lean_object* v_options_954_; uint8_t v_hasTrace_955_; 
v_toCold_953_ = lean_ctor_get(v_a_945_, 0);
v_options_954_ = lean_ctor_get(v_toCold_953_, 2);
v_hasTrace_955_ = lean_ctor_get_uint8(v_options_954_, sizeof(void*)*1);
if (v_hasTrace_955_ == 0)
{
lean_object* v___x_956_; 
lean_dec_ref(v_op_937_);
v___x_956_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_938_, v_a_939_, v_a_940_);
return v___x_956_;
}
else
{
lean_object* v_inheritedTraceOptions_957_; lean_object* v_cls_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v_inheritedTraceOptions_957_ = lean_ctor_get(v_toCold_953_, 11);
v_cls_958_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_959_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_960_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_957_, v_options_954_, v___x_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; 
lean_dec_ref(v_op_937_);
v___x_961_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_938_, v_a_939_, v_a_940_);
return v___x_961_;
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_962_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8);
lean_inc_ref(v_fn_950_);
v___x_963_ = l_Lean_MessageData_ofExpr(v_fn_950_);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
lean_inc_ref(v_arg_951_);
v___x_967_ = l_Lean_MessageData_ofExpr(v_arg_951_);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v___x_965_);
lean_inc_ref(v_arg_949_);
v___x_970_ = l_Lean_MessageData_ofExpr(v_arg_949_);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12);
v___x_973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_971_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_937_);
v___x_975_ = l_Lean_MessageData_ofExpr(v___x_974_);
v___x_976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_973_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14);
v___x_978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_958_, v___x_978_, v_a_940_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v_snd_981_; lean_object* v___x_982_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
v_snd_981_ = lean_ctor_get(v_a_980_, 1);
lean_inc(v_snd_981_);
lean_dec(v_a_980_);
v___x_982_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_938_, v_a_939_, v_snd_981_);
return v___x_982_;
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec_ref_known(v_a_939_, 2);
lean_dec_ref(v_coeff_938_);
v_a_983_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_979_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_979_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
}
else
{
lean_object* v___x_991_; 
lean_inc_ref(v_arg_951_);
lean_inc_ref(v_arg_949_);
lean_dec_ref_known(v_a_939_, 2);
lean_inc_ref(v_op_937_);
v___x_991_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_937_, v_coeff_938_, v_arg_951_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v_fst_993_; lean_object* v_snd_994_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_991_, 1);
v_fst_993_ = lean_ctor_get(v_a_992_, 0);
lean_inc(v_fst_993_);
v_snd_994_ = lean_ctor_get(v_a_992_, 1);
lean_inc(v_snd_994_);
lean_dec(v_a_992_);
v_coeff_938_ = v_fst_993_;
v_a_939_ = v_arg_949_;
v_a_940_ = v_snd_994_;
goto _start;
}
else
{
lean_dec_ref(v_arg_949_);
lean_dec_ref(v_op_937_);
return v___x_991_;
}
}
}
else
{
lean_object* v___x_996_; 
lean_dec_ref(v_op_937_);
v___x_996_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_938_, v_a_939_, v_a_940_);
return v___x_996_;
}
}
else
{
lean_object* v___x_997_; 
lean_dec_ref(v_op_937_);
v___x_997_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_938_, v_a_939_, v_a_940_);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___boxed(lean_object* v_op_998_, lean_object* v_coeff_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_998_, v_coeff_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(lean_object* v_cls_1010_, lean_object* v_msg_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_1010_, v_msg_1011_, v___y_1012_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___boxed(lean_object* v_cls_1021_, lean_object* v_msg_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(v_cls_1021_, v_msg_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
return v_res_1031_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1032_ = lean_box(0);
v___x_1033_ = lean_unsigned_to_nat(16u);
v___x_1034_ = lean_mk_array(v___x_1033_, v___x_1032_);
return v___x_1034_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1035_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1036_ = lean_unsigned_to_nat(0u);
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v___x_1035_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(lean_object* v_op_1038_, lean_object* v_e_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1049_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_1038_, v___x_1048_, v_e_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___boxed(lean_object* v_op_1050_, lean_object* v_e_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_op_1050_, v_e_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(lean_object* v_a_1061_, lean_object* v_x_1062_){
_start:
{
if (lean_obj_tag(v_x_1062_) == 0)
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_box(0);
return v___x_1063_;
}
else
{
lean_object* v_key_1064_; lean_object* v_value_1065_; lean_object* v_tail_1066_; uint8_t v___x_1067_; 
v_key_1064_ = lean_ctor_get(v_x_1062_, 0);
v_value_1065_ = lean_ctor_get(v_x_1062_, 1);
v_tail_1066_ = lean_ctor_get(v_x_1062_, 2);
v___x_1067_ = lean_nat_dec_eq(v_key_1064_, v_a_1061_);
if (v___x_1067_ == 0)
{
v_x_1062_ = v_tail_1066_;
goto _start;
}
else
{
lean_object* v___x_1069_; 
lean_inc(v_value_1065_);
v___x_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1069_, 0, v_value_1065_);
return v___x_1069_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg___boxed(lean_object* v_a_1070_, lean_object* v_x_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1070_, v_x_1071_);
lean_dec(v_x_1071_);
lean_dec(v_a_1070_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(lean_object* v_m_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v_buckets_1075_; lean_object* v___x_1076_; uint64_t v___x_1077_; uint64_t v___x_1078_; uint64_t v___x_1079_; uint64_t v_fold_1080_; uint64_t v___x_1081_; uint64_t v___x_1082_; uint64_t v___x_1083_; size_t v___x_1084_; size_t v___x_1085_; size_t v___x_1086_; size_t v___x_1087_; size_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_buckets_1075_ = lean_ctor_get(v_m_1073_, 1);
v___x_1076_ = lean_array_get_size(v_buckets_1075_);
v___x_1077_ = lean_uint64_of_nat(v_a_1074_);
v___x_1078_ = 32ULL;
v___x_1079_ = lean_uint64_shift_right(v___x_1077_, v___x_1078_);
v_fold_1080_ = lean_uint64_xor(v___x_1077_, v___x_1079_);
v___x_1081_ = 16ULL;
v___x_1082_ = lean_uint64_shift_right(v_fold_1080_, v___x_1081_);
v___x_1083_ = lean_uint64_xor(v_fold_1080_, v___x_1082_);
v___x_1084_ = lean_uint64_to_usize(v___x_1083_);
v___x_1085_ = lean_usize_of_nat(v___x_1076_);
v___x_1086_ = ((size_t)1ULL);
v___x_1087_ = lean_usize_sub(v___x_1085_, v___x_1086_);
v___x_1088_ = lean_usize_land(v___x_1084_, v___x_1087_);
v___x_1089_ = lean_array_uget_borrowed(v_buckets_1075_, v___x_1088_);
v___x_1090_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1074_, v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg___boxed(lean_object* v_m_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1091_, v_a_1092_);
lean_dec(v_a_1092_);
lean_dec_ref(v_m_1091_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(lean_object* v_a_1094_, lean_object* v_b_1095_, lean_object* v_x_1096_){
_start:
{
if (lean_obj_tag(v_x_1096_) == 0)
{
lean_dec(v_b_1095_);
lean_dec(v_a_1094_);
return v_x_1096_;
}
else
{
lean_object* v_key_1097_; lean_object* v_value_1098_; lean_object* v_tail_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1111_; 
v_key_1097_ = lean_ctor_get(v_x_1096_, 0);
v_value_1098_ = lean_ctor_get(v_x_1096_, 1);
v_tail_1099_ = lean_ctor_get(v_x_1096_, 2);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_x_1096_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1101_ = v_x_1096_;
v_isShared_1102_ = v_isSharedCheck_1111_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_tail_1099_);
lean_inc(v_value_1098_);
lean_inc(v_key_1097_);
lean_dec(v_x_1096_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1111_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
uint8_t v___x_1103_; 
v___x_1103_ = lean_nat_dec_eq(v_key_1097_, v_a_1094_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1104_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1094_, v_b_1095_, v_tail_1099_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 2, v___x_1104_);
v___x_1106_ = v___x_1101_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_key_1097_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_value_1098_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
else
{
lean_object* v___x_1109_; 
lean_dec(v_value_1098_);
lean_dec(v_key_1097_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 1, v_b_1095_);
lean_ctor_set(v___x_1101_, 0, v_a_1094_);
v___x_1109_ = v___x_1101_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1094_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_b_1095_);
lean_ctor_set(v_reuseFailAlloc_1110_, 2, v_tail_1099_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(lean_object* v_m_1112_, lean_object* v_a_1113_, lean_object* v_b_1114_){
_start:
{
lean_object* v_size_1115_; lean_object* v_buckets_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1159_; 
v_size_1115_ = lean_ctor_get(v_m_1112_, 0);
v_buckets_1116_ = lean_ctor_get(v_m_1112_, 1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_m_1112_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1118_ = v_m_1112_;
v_isShared_1119_ = v_isSharedCheck_1159_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_buckets_1116_);
lean_inc(v_size_1115_);
lean_dec(v_m_1112_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1159_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; uint64_t v___x_1121_; uint64_t v___x_1122_; uint64_t v___x_1123_; uint64_t v_fold_1124_; uint64_t v___x_1125_; uint64_t v___x_1126_; uint64_t v___x_1127_; size_t v___x_1128_; size_t v___x_1129_; size_t v___x_1130_; size_t v___x_1131_; size_t v___x_1132_; lean_object* v_bkt_1133_; uint8_t v___x_1134_; 
v___x_1120_ = lean_array_get_size(v_buckets_1116_);
v___x_1121_ = lean_uint64_of_nat(v_a_1113_);
v___x_1122_ = 32ULL;
v___x_1123_ = lean_uint64_shift_right(v___x_1121_, v___x_1122_);
v_fold_1124_ = lean_uint64_xor(v___x_1121_, v___x_1123_);
v___x_1125_ = 16ULL;
v___x_1126_ = lean_uint64_shift_right(v_fold_1124_, v___x_1125_);
v___x_1127_ = lean_uint64_xor(v_fold_1124_, v___x_1126_);
v___x_1128_ = lean_uint64_to_usize(v___x_1127_);
v___x_1129_ = lean_usize_of_nat(v___x_1120_);
v___x_1130_ = ((size_t)1ULL);
v___x_1131_ = lean_usize_sub(v___x_1129_, v___x_1130_);
v___x_1132_ = lean_usize_land(v___x_1128_, v___x_1131_);
v_bkt_1133_ = lean_array_uget_borrowed(v_buckets_1116_, v___x_1132_);
v___x_1134_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1113_, v_bkt_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; lean_object* v_size_x27_1136_; lean_object* v___x_1137_; lean_object* v_buckets_x27_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1135_ = lean_unsigned_to_nat(1u);
v_size_x27_1136_ = lean_nat_add(v_size_1115_, v___x_1135_);
lean_dec(v_size_1115_);
lean_inc(v_bkt_1133_);
v___x_1137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1137_, 0, v_a_1113_);
lean_ctor_set(v___x_1137_, 1, v_b_1114_);
lean_ctor_set(v___x_1137_, 2, v_bkt_1133_);
v_buckets_x27_1138_ = lean_array_uset(v_buckets_1116_, v___x_1132_, v___x_1137_);
v___x_1139_ = lean_unsigned_to_nat(4u);
v___x_1140_ = lean_nat_mul(v_size_x27_1136_, v___x_1139_);
v___x_1141_ = lean_unsigned_to_nat(3u);
v___x_1142_ = lean_nat_div(v___x_1140_, v___x_1141_);
lean_dec(v___x_1140_);
v___x_1143_ = lean_array_get_size(v_buckets_x27_1138_);
v___x_1144_ = lean_nat_dec_le(v___x_1142_, v___x_1143_);
lean_dec(v___x_1142_);
if (v___x_1144_ == 0)
{
lean_object* v_val_1145_; lean_object* v___x_1147_; 
v_val_1145_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_1138_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 1, v_val_1145_);
lean_ctor_set(v___x_1118_, 0, v_size_x27_1136_);
v___x_1147_ = v___x_1118_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_size_x27_1136_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_val_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
else
{
lean_object* v___x_1150_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 1, v_buckets_x27_1138_);
lean_ctor_set(v___x_1118_, 0, v_size_x27_1136_);
v___x_1150_ = v___x_1118_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_size_x27_1136_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_buckets_x27_1138_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
else
{
lean_object* v___x_1152_; lean_object* v_buckets_x27_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
lean_inc(v_bkt_1133_);
v___x_1152_ = lean_box(0);
v_buckets_x27_1153_ = lean_array_uset(v_buckets_1116_, v___x_1132_, v___x_1152_);
v___x_1154_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1113_, v_b_1114_, v_bkt_1133_);
v___x_1155_ = lean_array_uset(v_buckets_x27_1153_, v___x_1132_, v___x_1154_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 1, v___x_1155_);
v___x_1157_ = v___x_1118_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_size_1115_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(lean_object* v_snd_1160_, lean_object* v_x_1161_, lean_object* v_x_1162_){
_start:
{
if (lean_obj_tag(v_x_1162_) == 0)
{
return v_x_1161_;
}
else
{
lean_object* v_key_1163_; lean_object* v_value_1164_; lean_object* v_tail_1165_; lean_object* v___y_1167_; lean_object* v___x_1170_; 
v_key_1163_ = lean_ctor_get(v_x_1162_, 0);
lean_inc(v_key_1163_);
v_value_1164_ = lean_ctor_get(v_x_1162_, 1);
lean_inc(v_value_1164_);
v_tail_1165_ = lean_ctor_get(v_x_1162_, 2);
lean_inc(v_tail_1165_);
lean_dec_ref_known(v_x_1162_, 3);
v___x_1170_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_snd_1160_, v_key_1163_);
if (lean_obj_tag(v___x_1170_) == 1)
{
lean_object* v_val_1171_; uint8_t v___x_1172_; 
v_val_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_val_1171_);
lean_dec_ref_known(v___x_1170_, 1);
v___x_1172_ = lean_nat_dec_le(v_value_1164_, v_val_1171_);
if (v___x_1172_ == 0)
{
lean_dec(v_value_1164_);
v___y_1167_ = v_val_1171_;
goto v___jp_1166_;
}
else
{
lean_dec(v_val_1171_);
v___y_1167_ = v_value_1164_;
goto v___jp_1166_;
}
}
else
{
lean_dec(v___x_1170_);
lean_dec(v_value_1164_);
lean_dec(v_key_1163_);
v_x_1162_ = v_tail_1165_;
goto _start;
}
v___jp_1166_:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(v_x_1161_, v_key_1163_, v___y_1167_);
v_x_1161_ = v___x_1168_;
v_x_1162_ = v_tail_1165_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5___boxed(lean_object* v_snd_1174_, lean_object* v_x_1175_, lean_object* v_x_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(v_snd_1174_, v_x_1175_, v_x_1176_);
lean_dec_ref(v_snd_1174_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(lean_object* v_snd_1178_, lean_object* v_as_1179_, size_t v_i_1180_, size_t v_stop_1181_, lean_object* v_b_1182_){
_start:
{
uint8_t v___x_1183_; 
v___x_1183_ = lean_usize_dec_eq(v_i_1180_, v_stop_1181_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; lean_object* v___x_1185_; size_t v___x_1186_; size_t v___x_1187_; 
v___x_1184_ = lean_array_uget_borrowed(v_as_1179_, v_i_1180_);
lean_inc(v___x_1184_);
v___x_1185_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(v_snd_1178_, v_b_1182_, v___x_1184_);
v___x_1186_ = ((size_t)1ULL);
v___x_1187_ = lean_usize_add(v_i_1180_, v___x_1186_);
v_i_1180_ = v___x_1187_;
v_b_1182_ = v___x_1185_;
goto _start;
}
else
{
return v_b_1182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6___boxed(lean_object* v_snd_1189_, lean_object* v_as_1190_, lean_object* v_i_1191_, lean_object* v_stop_1192_, lean_object* v_b_1193_){
_start:
{
size_t v_i_boxed_1194_; size_t v_stop_boxed_1195_; lean_object* v_res_1196_; 
v_i_boxed_1194_ = lean_unbox_usize(v_i_1191_);
lean_dec(v_i_1191_);
v_stop_boxed_1195_ = lean_unbox_usize(v_stop_1192_);
lean_dec(v_stop_1192_);
v_res_1196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1189_, v_as_1190_, v_i_boxed_1194_, v_stop_boxed_1195_, v_b_1193_);
lean_dec_ref(v_as_1190_);
lean_dec_ref(v_snd_1189_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(lean_object* v_commonCnt_1197_, lean_object* v_a_1198_, lean_object* v_x_1199_){
_start:
{
if (lean_obj_tag(v_x_1199_) == 0)
{
lean_dec(v_a_1198_);
return v_x_1199_;
}
else
{
lean_object* v_key_1200_; lean_object* v_value_1201_; lean_object* v_tail_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1215_; 
v_key_1200_ = lean_ctor_get(v_x_1199_, 0);
v_value_1201_ = lean_ctor_get(v_x_1199_, 1);
v_tail_1202_ = lean_ctor_get(v_x_1199_, 2);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_x_1199_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1204_ = v_x_1199_;
v_isShared_1205_ = v_isSharedCheck_1215_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_tail_1202_);
lean_inc(v_value_1201_);
lean_inc(v_key_1200_);
lean_dec(v_x_1199_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1215_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
uint8_t v___x_1206_; 
v___x_1206_ = lean_nat_dec_eq(v_key_1200_, v_a_1198_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1207_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1197_, v_a_1198_, v_tail_1202_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 2, v___x_1207_);
v___x_1209_ = v___x_1204_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_key_1200_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_value_1201_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
else
{
lean_object* v___x_1211_; lean_object* v___x_1213_; 
lean_dec(v_key_1200_);
v___x_1211_ = lean_nat_sub(v_value_1201_, v_commonCnt_1197_);
lean_dec(v_value_1201_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v___x_1211_);
lean_ctor_set(v___x_1204_, 0, v_a_1198_);
v___x_1213_ = v___x_1204_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1198_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v___x_1211_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v_tail_1202_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0___boxed(lean_object* v_commonCnt_1216_, lean_object* v_a_1217_, lean_object* v_x_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1216_, v_a_1217_, v_x_1218_);
lean_dec(v_commonCnt_1216_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(lean_object* v_commonCnt_1220_, lean_object* v_m_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v_size_1223_; lean_object* v_buckets_1224_; lean_object* v___x_1225_; uint64_t v___x_1226_; uint64_t v___x_1227_; uint64_t v___x_1228_; uint64_t v_fold_1229_; uint64_t v___x_1230_; uint64_t v___x_1231_; uint64_t v___x_1232_; size_t v___x_1233_; size_t v___x_1234_; size_t v___x_1235_; size_t v___x_1236_; size_t v___x_1237_; lean_object* v_bucket_1238_; uint8_t v___x_1239_; 
v_size_1223_ = lean_ctor_get(v_m_1221_, 0);
v_buckets_1224_ = lean_ctor_get(v_m_1221_, 1);
v___x_1225_ = lean_array_get_size(v_buckets_1224_);
v___x_1226_ = lean_uint64_of_nat(v_a_1222_);
v___x_1227_ = 32ULL;
v___x_1228_ = lean_uint64_shift_right(v___x_1226_, v___x_1227_);
v_fold_1229_ = lean_uint64_xor(v___x_1226_, v___x_1228_);
v___x_1230_ = 16ULL;
v___x_1231_ = lean_uint64_shift_right(v_fold_1229_, v___x_1230_);
v___x_1232_ = lean_uint64_xor(v_fold_1229_, v___x_1231_);
v___x_1233_ = lean_uint64_to_usize(v___x_1232_);
v___x_1234_ = lean_usize_of_nat(v___x_1225_);
v___x_1235_ = ((size_t)1ULL);
v___x_1236_ = lean_usize_sub(v___x_1234_, v___x_1235_);
v___x_1237_ = lean_usize_land(v___x_1233_, v___x_1236_);
v_bucket_1238_ = lean_array_uget_borrowed(v_buckets_1224_, v___x_1237_);
v___x_1239_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1222_, v_bucket_1238_);
if (v___x_1239_ == 0)
{
lean_dec(v_a_1222_);
return v_m_1221_;
}
else
{
lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1250_; 
lean_inc(v_bucket_1238_);
lean_inc_ref(v_buckets_1224_);
lean_inc(v_size_1223_);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_m_1221_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; lean_object* v_unused_1252_; 
v_unused_1251_ = lean_ctor_get(v_m_1221_, 1);
lean_dec(v_unused_1251_);
v_unused_1252_ = lean_ctor_get(v_m_1221_, 0);
lean_dec(v_unused_1252_);
v___x_1241_ = v_m_1221_;
v_isShared_1242_ = v_isSharedCheck_1250_;
goto v_resetjp_1240_;
}
else
{
lean_dec(v_m_1221_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1250_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; lean_object* v_buckets_1244_; lean_object* v_bucket_1245_; lean_object* v___x_1246_; lean_object* v___x_1248_; 
v___x_1243_ = lean_box(0);
v_buckets_1244_ = lean_array_uset(v_buckets_1224_, v___x_1237_, v___x_1243_);
v_bucket_1245_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1220_, v_a_1222_, v_bucket_1238_);
v___x_1246_ = lean_array_uset(v_buckets_1244_, v___x_1237_, v_bucket_1245_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 1, v___x_1246_);
v___x_1248_ = v___x_1241_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_size_1223_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0___boxed(lean_object* v_commonCnt_1253_, lean_object* v_m_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_commonCnt_1253_, v_m_1254_, v_a_1255_);
lean_dec(v_commonCnt_1253_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
if (lean_obj_tag(v_x_1258_) == 0)
{
return v_x_1257_;
}
else
{
lean_object* v_key_1259_; lean_object* v_value_1260_; lean_object* v_tail_1261_; lean_object* v___x_1262_; 
v_key_1259_ = lean_ctor_get(v_x_1258_, 0);
lean_inc(v_key_1259_);
v_value_1260_ = lean_ctor_get(v_x_1258_, 1);
lean_inc(v_value_1260_);
v_tail_1261_ = lean_ctor_get(v_x_1258_, 2);
lean_inc(v_tail_1261_);
lean_dec_ref_known(v_x_1258_, 3);
v___x_1262_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_value_1260_, v_x_1257_, v_key_1259_);
lean_dec(v_value_1260_);
v_x_1257_ = v___x_1262_;
v_x_1258_ = v_tail_1261_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(lean_object* v_x_1264_, lean_object* v_x_1265_){
_start:
{
if (lean_obj_tag(v_x_1265_) == 0)
{
return v_x_1264_;
}
else
{
lean_object* v_key_1266_; lean_object* v_value_1267_; lean_object* v_tail_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v_key_1266_ = lean_ctor_get(v_x_1265_, 0);
lean_inc(v_key_1266_);
v_value_1267_ = lean_ctor_get(v_x_1265_, 1);
lean_inc(v_value_1267_);
v_tail_1268_ = lean_ctor_get(v_x_1265_, 2);
lean_inc(v_tail_1268_);
lean_dec_ref_known(v_x_1265_, 3);
v___x_1269_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_value_1267_, v_x_1264_, v_key_1266_);
lean_dec(v_value_1267_);
v___x_1270_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(v___x_1269_, v_tail_1268_);
return v___x_1270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(lean_object* v_as_1271_, size_t v_i_1272_, size_t v_stop_1273_, lean_object* v_b_1274_){
_start:
{
uint8_t v___x_1275_; 
v___x_1275_ = lean_usize_dec_eq(v_i_1272_, v_stop_1273_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; lean_object* v___x_1277_; size_t v___x_1278_; size_t v___x_1279_; 
v___x_1276_ = lean_array_uget_borrowed(v_as_1271_, v_i_1272_);
lean_inc(v___x_1276_);
v___x_1277_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(v_b_1274_, v___x_1276_);
v___x_1278_ = ((size_t)1ULL);
v___x_1279_ = lean_usize_add(v_i_1272_, v___x_1278_);
v_i_1272_ = v___x_1279_;
v_b_1274_ = v___x_1277_;
goto _start;
}
else
{
return v_b_1274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2___boxed(lean_object* v_as_1281_, lean_object* v_i_1282_, lean_object* v_stop_1283_, lean_object* v_b_1284_){
_start:
{
size_t v_i_boxed_1285_; size_t v_stop_boxed_1286_; lean_object* v_res_1287_; 
v_i_boxed_1285_ = lean_unbox_usize(v_i_1282_);
lean_dec(v_i_1282_);
v_stop_boxed_1286_ = lean_unbox_usize(v_stop_1283_);
lean_dec(v_stop_1283_);
v_res_1287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_as_1281_, v_i_boxed_1285_, v_stop_boxed_1286_, v_b_1284_);
lean_dec_ref(v_as_1281_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(lean_object* v_x_1288_, lean_object* v_y_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v___y_1293_; lean_object* v_fst_1294_; lean_object* v_snd_1295_; lean_object* v_size_1299_; lean_object* v_buckets_1300_; lean_object* v_size_1301_; lean_object* v_buckets_1302_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1309_; lean_object* v_buckets_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v_buckets_1323_; lean_object* v_fst_1331_; lean_object* v_buckets_1332_; lean_object* v_snd_1333_; uint8_t v___x_1343_; 
v_size_1299_ = lean_ctor_get(v_y_1289_, 0);
lean_inc(v_size_1299_);
v_buckets_1300_ = lean_ctor_get(v_y_1289_, 1);
v_size_1301_ = lean_ctor_get(v_x_1288_, 0);
lean_inc(v_size_1301_);
v_buckets_1302_ = lean_ctor_get(v_x_1288_, 1);
v___x_1343_ = lean_nat_dec_lt(v_size_1299_, v_size_1301_);
if (v___x_1343_ == 0)
{
lean_inc_ref(v_buckets_1302_);
v_fst_1331_ = v_x_1288_;
v_buckets_1332_ = v_buckets_1302_;
v_snd_1333_ = v_y_1289_;
goto v___jp_1330_;
}
else
{
lean_inc_ref(v_buckets_1300_);
v_fst_1331_ = v_y_1289_;
v_buckets_1332_ = v_buckets_1300_;
v_snd_1333_ = v_x_1288_;
goto v___jp_1330_;
}
v___jp_1292_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1296_, 0, v___y_1293_);
lean_ctor_set(v___x_1296_, 1, v_fst_1294_);
lean_ctor_set(v___x_1296_, 2, v_snd_1295_);
v___x_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
lean_ctor_set(v___x_1297_, 1, v_a_1290_);
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
v___jp_1303_:
{
uint8_t v___x_1307_; 
v___x_1307_ = lean_nat_dec_lt(v_size_1299_, v_size_1301_);
lean_dec(v_size_1301_);
lean_dec(v_size_1299_);
if (v___x_1307_ == 0)
{
v___y_1293_ = v___y_1305_;
v_fst_1294_ = v___y_1304_;
v_snd_1295_ = v___y_1306_;
goto v___jp_1292_;
}
else
{
v___y_1293_ = v___y_1305_;
v_fst_1294_ = v___y_1306_;
v_snd_1295_ = v___y_1304_;
goto v___jp_1292_;
}
}
v___jp_1308_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1313_ = lean_unsigned_to_nat(0u);
v___x_1314_ = lean_array_get_size(v_buckets_1310_);
v___x_1315_ = lean_nat_dec_lt(v___x_1313_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_dec_ref(v_buckets_1310_);
v___y_1304_ = v___y_1312_;
v___y_1305_ = v___y_1309_;
v___y_1306_ = v___y_1311_;
goto v___jp_1303_;
}
else
{
size_t v___x_1316_; size_t v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = ((size_t)0ULL);
v___x_1317_ = lean_usize_of_nat(v___x_1314_);
v___x_1318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1310_, v___x_1316_, v___x_1317_, v___y_1311_);
lean_dec_ref(v_buckets_1310_);
v___y_1304_ = v___y_1312_;
v___y_1305_ = v___y_1309_;
v___y_1306_ = v___x_1318_;
goto v___jp_1303_;
}
}
v___jp_1319_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1324_ = lean_unsigned_to_nat(0u);
v___x_1325_ = lean_array_get_size(v_buckets_1323_);
v___x_1326_ = lean_nat_dec_lt(v___x_1324_, v___x_1325_);
if (v___x_1326_ == 0)
{
v___y_1309_ = v___y_1322_;
v_buckets_1310_ = v_buckets_1323_;
v___y_1311_ = v___y_1320_;
v___y_1312_ = v___y_1321_;
goto v___jp_1308_;
}
else
{
size_t v___x_1327_; size_t v___x_1328_; lean_object* v___x_1329_; 
v___x_1327_ = ((size_t)0ULL);
v___x_1328_ = lean_usize_of_nat(v___x_1325_);
v___x_1329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1323_, v___x_1327_, v___x_1328_, v___y_1321_);
v___y_1309_ = v___y_1322_;
v_buckets_1310_ = v_buckets_1323_;
v___y_1311_ = v___y_1320_;
v___y_1312_ = v___x_1329_;
goto v___jp_1308_;
}
}
v___jp_1330_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v___x_1334_ = lean_unsigned_to_nat(0u);
v___x_1335_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1336_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1337_ = lean_array_get_size(v_buckets_1332_);
v___x_1338_ = lean_nat_dec_lt(v___x_1334_, v___x_1337_);
if (v___x_1338_ == 0)
{
lean_dec_ref(v_buckets_1332_);
v___y_1320_ = v_snd_1333_;
v___y_1321_ = v_fst_1331_;
v___y_1322_ = v___x_1336_;
v_buckets_1323_ = v___x_1335_;
goto v___jp_1319_;
}
else
{
size_t v___x_1339_; size_t v___x_1340_; lean_object* v___x_1341_; lean_object* v_buckets_1342_; 
v___x_1339_ = ((size_t)0ULL);
v___x_1340_ = lean_usize_of_nat(v___x_1337_);
v___x_1341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1333_, v_buckets_1332_, v___x_1339_, v___x_1340_, v___x_1336_);
lean_dec_ref(v_buckets_1332_);
v_buckets_1342_ = lean_ctor_get(v___x_1341_, 1);
lean_inc_ref(v_buckets_1342_);
v___y_1320_ = v_snd_1333_;
v___y_1321_ = v_fst_1331_;
v___y_1322_ = v___x_1341_;
v_buckets_1323_ = v_buckets_1342_;
goto v___jp_1319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg___boxed(lean_object* v_x_1344_, lean_object* v_y_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1344_, v_y_1345_, v_a_1346_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(lean_object* v_x_1349_, lean_object* v_y_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1349_, v_y_1350_, v_a_1351_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___boxed(lean_object* v_x_1360_, lean_object* v_y_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(v_x_1360_, v_y_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3(lean_object* v_00_u03b2_1371_, lean_object* v_m_1372_, lean_object* v_a_1373_, lean_object* v_b_1374_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(v_m_1372_, v_a_1373_, v_b_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4(lean_object* v_00_u03b2_1376_, lean_object* v_m_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1377_, v_a_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___boxed(lean_object* v_00_u03b2_1380_, lean_object* v_m_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4(v_00_u03b2_1380_, v_m_1381_, v_a_1382_);
lean_dec(v_a_1382_);
lean_dec_ref(v_m_1381_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5(lean_object* v_00_u03b2_1384_, lean_object* v_a_1385_, lean_object* v_b_1386_, lean_object* v_x_1387_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1385_, v_b_1386_, v_x_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7(lean_object* v_00_u03b2_1389_, lean_object* v_a_1390_, lean_object* v_x_1391_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1390_, v_x_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1393_, lean_object* v_a_1394_, lean_object* v_x_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7(v_00_u03b2_1393_, v_a_1394_, v_x_1395_);
lean_dec(v_x_1395_);
lean_dec(v_a_1394_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(lean_object* v_x_1397_, lean_object* v_x_1398_){
_start:
{
if (lean_obj_tag(v_x_1398_) == 0)
{
return v_x_1397_;
}
else
{
lean_object* v_key_1399_; lean_object* v_value_1400_; lean_object* v_tail_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v_key_1399_ = lean_ctor_get(v_x_1398_, 0);
v_value_1400_ = lean_ctor_get(v_x_1398_, 1);
v_tail_1401_ = lean_ctor_get(v_x_1398_, 2);
lean_inc(v_value_1400_);
lean_inc(v_key_1399_);
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_key_1399_);
lean_ctor_set(v___x_1402_, 1, v_value_1400_);
v___x_1403_ = lean_array_push(v_x_1397_, v___x_1402_);
v_x_1397_ = v___x_1403_;
v_x_1398_ = v_tail_1401_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___boxed(lean_object* v_x_1405_, lean_object* v_x_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(v_x_1405_, v_x_1406_);
lean_dec(v_x_1406_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(lean_object* v_as_1408_, size_t v_i_1409_, size_t v_stop_1410_, lean_object* v_b_1411_){
_start:
{
uint8_t v___x_1412_; 
v___x_1412_ = lean_usize_dec_eq(v_i_1409_, v_stop_1410_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1414_; size_t v___x_1415_; size_t v___x_1416_; 
v___x_1413_ = lean_array_uget_borrowed(v_as_1408_, v_i_1409_);
v___x_1414_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(v_b_1411_, v___x_1413_);
v___x_1415_ = ((size_t)1ULL);
v___x_1416_ = lean_usize_add(v_i_1409_, v___x_1415_);
v_i_1409_ = v___x_1416_;
v_b_1411_ = v___x_1414_;
goto _start;
}
else
{
return v_b_1411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4___boxed(lean_object* v_as_1418_, lean_object* v_i_1419_, lean_object* v_stop_1420_, lean_object* v_b_1421_){
_start:
{
size_t v_i_boxed_1422_; size_t v_stop_boxed_1423_; lean_object* v_res_1424_; 
v_i_boxed_1422_ = lean_unbox_usize(v_i_1419_);
lean_dec(v_i_1419_);
v_stop_boxed_1423_ = lean_unbox_usize(v_stop_1420_);
lean_dec(v_stop_1420_);
v_res_1424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_as_1418_, v_i_boxed_1422_, v_stop_boxed_1423_, v_b_1421_);
lean_dec_ref(v_as_1418_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(lean_object* v_upperBound_1425_, lean_object* v___x_1426_, lean_object* v_op_1427_, lean_object* v_a_1428_, lean_object* v_b_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v___y_1433_; uint8_t v___x_1437_; 
v___x_1437_ = lean_nat_dec_lt(v_a_1428_, v_upperBound_1425_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_dec(v_a_1428_);
lean_dec_ref(v_op_1427_);
lean_dec_ref(v___x_1426_);
v___x_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1438_, 0, v_b_1429_);
lean_ctor_set(v___x_1438_, 1, v___y_1430_);
v___x_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
return v___x_1439_;
}
else
{
if (lean_obj_tag(v_b_1429_) == 0)
{
lean_object* v___x_1440_; 
lean_inc_ref(v___x_1426_);
v___x_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1426_);
v___y_1433_ = v___x_1440_;
goto v___jp_1432_;
}
else
{
lean_object* v_val_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1450_; 
v_val_1441_ = lean_ctor_get(v_b_1429_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_b_1429_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1443_ = v_b_1429_;
v_isShared_1444_ = v_isSharedCheck_1450_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_val_1441_);
lean_dec(v_b_1429_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1450_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1448_; 
lean_inc_ref(v_op_1427_);
v___x_1445_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_1427_);
lean_inc_ref(v___x_1426_);
v___x_1446_ = l_Lean_mkAppB(v___x_1445_, v_val_1441_, v___x_1426_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1446_);
v___x_1448_ = v___x_1443_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1446_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
v___y_1433_ = v___x_1448_;
goto v___jp_1432_;
}
}
}
}
v___jp_1432_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_unsigned_to_nat(1u);
v___x_1435_ = lean_nat_add(v_a_1428_, v___x_1434_);
lean_dec(v_a_1428_);
v_a_1428_ = v___x_1435_;
v_b_1429_ = v___y_1433_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg___boxed(lean_object* v_upperBound_1451_, lean_object* v___x_1452_, lean_object* v_op_1453_, lean_object* v_a_1454_, lean_object* v_b_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1451_, v___x_1452_, v_op_1453_, v_a_1454_, v_b_1455_, v___y_1456_);
lean_dec(v_upperBound_1451_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(lean_object* v_op_1459_, lean_object* v_as_1460_, size_t v_sz_1461_, size_t v_i_1462_, lean_object* v_b_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
uint8_t v___x_1472_; 
v___x_1472_ = lean_usize_dec_lt(v_i_1462_, v_sz_1461_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_dec_ref(v_op_1459_);
v___x_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1473_, 0, v_b_1463_);
lean_ctor_set(v___x_1473_, 1, v___y_1464_);
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
return v___x_1474_;
}
else
{
lean_object* v_a_1475_; lean_object* v_fst_1476_; lean_object* v_snd_1477_; lean_object* v_varToExpr_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v_a_1475_ = lean_array_uget_borrowed(v_as_1460_, v_i_1462_);
v_fst_1476_ = lean_ctor_get(v_a_1475_, 0);
v_snd_1477_ = lean_ctor_get(v_a_1475_, 1);
v_varToExpr_1478_ = lean_ctor_get(v___y_1464_, 2);
v___x_1479_ = l_Lean_instInhabitedExpr;
v___x_1480_ = lean_unsigned_to_nat(0u);
v___x_1481_ = lean_array_get(v___x_1479_, v_varToExpr_1478_, v_fst_1476_);
lean_inc_ref(v_op_1459_);
v___x_1482_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_snd_1477_, v___x_1481_, v_op_1459_, v___x_1480_, v_b_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v_fst_1484_; lean_object* v_snd_1485_; size_t v___x_1486_; size_t v___x_1487_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1483_);
lean_dec_ref_known(v___x_1482_, 1);
v_fst_1484_ = lean_ctor_get(v_a_1483_, 0);
lean_inc(v_fst_1484_);
v_snd_1485_ = lean_ctor_get(v_a_1483_, 1);
lean_inc(v_snd_1485_);
lean_dec(v_a_1483_);
v___x_1486_ = ((size_t)1ULL);
v___x_1487_ = lean_usize_add(v_i_1462_, v___x_1486_);
v_i_1462_ = v___x_1487_;
v_b_1463_ = v_fst_1484_;
v___y_1464_ = v_snd_1485_;
goto _start;
}
else
{
lean_dec_ref(v_op_1459_);
return v___x_1482_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1___boxed(lean_object* v_op_1489_, lean_object* v_as_1490_, lean_object* v_sz_1491_, lean_object* v_i_1492_, lean_object* v_b_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
size_t v_sz_boxed_1502_; size_t v_i_boxed_1503_; lean_object* v_res_1504_; 
v_sz_boxed_1502_ = lean_unbox_usize(v_sz_1491_);
lean_dec(v_sz_1491_);
v_i_boxed_1503_ = lean_unbox_usize(v_i_1492_);
lean_dec(v_i_1492_);
v_res_1504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1489_, v_as_1490_, v_sz_boxed_1502_, v_i_boxed_1503_, v_b_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec_ref(v_as_1490_);
return v_res_1504_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(lean_object* v_x1_1505_, lean_object* v_x2_1506_){
_start:
{
lean_object* v_fst_1507_; lean_object* v_fst_1508_; uint8_t v___x_1509_; 
v_fst_1507_ = lean_ctor_get(v_x1_1505_, 0);
v_fst_1508_ = lean_ctor_get(v_x2_1506_, 0);
v___x_1509_ = lean_nat_dec_lt(v_fst_1507_, v_fst_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed(lean_object* v_x1_1510_, lean_object* v_x2_1511_){
_start:
{
uint8_t v_res_1512_; lean_object* v_r_1513_; 
v_res_1512_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v_x1_1510_, v_x2_1511_);
lean_dec_ref(v_x2_1511_);
lean_dec_ref(v_x1_1510_);
v_r_1513_ = lean_box(v_res_1512_);
return v_r_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(lean_object* v_hi_1514_, lean_object* v_pivot_1515_, lean_object* v_as_1516_, lean_object* v_i_1517_, lean_object* v_k_1518_){
_start:
{
uint8_t v___x_1519_; 
v___x_1519_ = lean_nat_dec_lt(v_k_1518_, v_hi_1514_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
lean_dec(v_k_1518_);
v___x_1520_ = lean_array_fswap(v_as_1516_, v_i_1517_, v_hi_1514_);
v___x_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1521_, 0, v_i_1517_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
return v___x_1521_;
}
else
{
lean_object* v___x_1522_; lean_object* v_fst_1523_; lean_object* v_fst_1524_; uint8_t v___x_1525_; 
v___x_1522_ = lean_array_fget_borrowed(v_as_1516_, v_k_1518_);
v_fst_1523_ = lean_ctor_get(v___x_1522_, 0);
v_fst_1524_ = lean_ctor_get(v_pivot_1515_, 0);
v___x_1525_ = lean_nat_dec_lt(v_fst_1523_, v_fst_1524_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = lean_unsigned_to_nat(1u);
v___x_1527_ = lean_nat_add(v_k_1518_, v___x_1526_);
lean_dec(v_k_1518_);
v_k_1518_ = v___x_1527_;
goto _start;
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1529_ = lean_array_fswap(v_as_1516_, v_i_1517_, v_k_1518_);
v___x_1530_ = lean_unsigned_to_nat(1u);
v___x_1531_ = lean_nat_add(v_i_1517_, v___x_1530_);
lean_dec(v_i_1517_);
v___x_1532_ = lean_nat_add(v_k_1518_, v___x_1530_);
lean_dec(v_k_1518_);
v_as_1516_ = v___x_1529_;
v_i_1517_ = v___x_1531_;
v_k_1518_ = v___x_1532_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg___boxed(lean_object* v_hi_1534_, lean_object* v_pivot_1535_, lean_object* v_as_1536_, lean_object* v_i_1537_, lean_object* v_k_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1534_, v_pivot_1535_, v_as_1536_, v_i_1537_, v_k_1538_);
lean_dec_ref(v_pivot_1535_);
lean_dec(v_hi_1534_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(lean_object* v_n_1540_, lean_object* v_as_1541_, lean_object* v_lo_1542_, lean_object* v_hi_1543_){
_start:
{
lean_object* v___y_1545_; uint8_t v___x_1555_; 
v___x_1555_ = lean_nat_dec_lt(v_lo_1542_, v_hi_1543_);
if (v___x_1555_ == 0)
{
lean_dec(v_lo_1542_);
return v_as_1541_;
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v_mid_1558_; lean_object* v___y_1560_; lean_object* v___y_1566_; lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1556_ = lean_nat_add(v_lo_1542_, v_hi_1543_);
v___x_1557_ = lean_unsigned_to_nat(1u);
v_mid_1558_ = lean_nat_shiftr(v___x_1556_, v___x_1557_);
lean_dec(v___x_1556_);
v___x_1571_ = lean_array_fget_borrowed(v_as_1541_, v_mid_1558_);
v___x_1572_ = lean_array_fget_borrowed(v_as_1541_, v_lo_1542_);
v___x_1573_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1571_, v___x_1572_);
if (v___x_1573_ == 0)
{
v___y_1566_ = v_as_1541_;
goto v___jp_1565_;
}
else
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_array_fswap(v_as_1541_, v_lo_1542_, v_mid_1558_);
v___y_1566_ = v___x_1574_;
goto v___jp_1565_;
}
v___jp_1559_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
v___x_1561_ = lean_array_fget_borrowed(v___y_1560_, v_mid_1558_);
v___x_1562_ = lean_array_fget_borrowed(v___y_1560_, v_hi_1543_);
v___x_1563_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1561_, v___x_1562_);
if (v___x_1563_ == 0)
{
lean_dec(v_mid_1558_);
v___y_1545_ = v___y_1560_;
goto v___jp_1544_;
}
else
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_array_fswap(v___y_1560_, v_mid_1558_, v_hi_1543_);
lean_dec(v_mid_1558_);
v___y_1545_ = v___x_1564_;
goto v___jp_1544_;
}
}
v___jp_1565_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v___x_1567_ = lean_array_fget_borrowed(v___y_1566_, v_hi_1543_);
v___x_1568_ = lean_array_fget_borrowed(v___y_1566_, v_lo_1542_);
v___x_1569_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1567_, v___x_1568_);
if (v___x_1569_ == 0)
{
v___y_1560_ = v___y_1566_;
goto v___jp_1559_;
}
else
{
lean_object* v___x_1570_; 
v___x_1570_ = lean_array_fswap(v___y_1566_, v_lo_1542_, v_hi_1543_);
v___y_1560_ = v___x_1570_;
goto v___jp_1559_;
}
}
}
v___jp_1544_:
{
lean_object* v_pivot_1546_; lean_object* v___x_1547_; lean_object* v_fst_1548_; lean_object* v_snd_1549_; uint8_t v___x_1550_; 
v_pivot_1546_ = lean_array_fget(v___y_1545_, v_hi_1543_);
lean_inc_n(v_lo_1542_, 2);
v___x_1547_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1543_, v_pivot_1546_, v___y_1545_, v_lo_1542_, v_lo_1542_);
lean_dec(v_pivot_1546_);
v_fst_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_fst_1548_);
v_snd_1549_ = lean_ctor_get(v___x_1547_, 1);
lean_inc(v_snd_1549_);
lean_dec_ref(v___x_1547_);
v___x_1550_ = lean_nat_dec_le(v_hi_1543_, v_fst_1548_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1551_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1540_, v_snd_1549_, v_lo_1542_, v_fst_1548_);
v___x_1552_ = lean_unsigned_to_nat(1u);
v___x_1553_ = lean_nat_add(v_fst_1548_, v___x_1552_);
lean_dec(v_fst_1548_);
v_as_1541_ = v___x_1551_;
v_lo_1542_ = v___x_1553_;
goto _start;
}
else
{
lean_dec(v_fst_1548_);
lean_dec(v_lo_1542_);
return v_snd_1549_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___boxed(lean_object* v_n_1575_, lean_object* v_as_1576_, lean_object* v_lo_1577_, lean_object* v_hi_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1575_, v_as_1576_, v_lo_1577_, v_hi_1578_);
lean_dec(v_hi_1578_);
lean_dec(v_n_1575_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(lean_object* v_coeff_1580_, lean_object* v_op_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v___y_1591_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1609_; lean_object* v_size_1616_; lean_object* v_buckets_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v_size_1616_ = lean_ctor_get(v_coeff_1580_, 0);
v_buckets_1617_ = lean_ctor_get(v_coeff_1580_, 1);
v___x_1618_ = lean_mk_empty_array_with_capacity(v_size_1616_);
v___x_1619_ = lean_unsigned_to_nat(0u);
v___x_1620_ = lean_array_get_size(v_buckets_1617_);
v___x_1621_ = lean_nat_dec_lt(v___x_1619_, v___x_1620_);
if (v___x_1621_ == 0)
{
v___y_1609_ = v___x_1618_;
goto v___jp_1608_;
}
else
{
size_t v___x_1622_; size_t v___x_1623_; lean_object* v___x_1624_; 
v___x_1622_ = ((size_t)0ULL);
v___x_1623_ = lean_usize_of_nat(v___x_1620_);
v___x_1624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_buckets_1617_, v___x_1622_, v___x_1623_, v___x_1618_);
v___y_1609_ = v___x_1624_;
goto v___jp_1608_;
}
v___jp_1590_:
{
lean_object* v_acc_1592_; size_t v_sz_1593_; size_t v___x_1594_; lean_object* v___x_1595_; 
v_acc_1592_ = lean_box(0);
v_sz_1593_ = lean_array_size(v___y_1591_);
v___x_1594_ = ((size_t)0ULL);
v___x_1595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1581_, v___y_1591_, v_sz_1593_, v___x_1594_, v_acc_1592_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_);
lean_dec_ref(v___y_1591_);
return v___x_1595_;
}
v___jp_1596_:
{
lean_object* v___x_1601_; 
v___x_1601_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v___y_1598_, v___y_1597_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec(v___y_1598_);
v___y_1591_ = v___x_1601_;
goto v___jp_1590_;
}
v___jp_1602_:
{
uint8_t v___x_1607_; 
v___x_1607_ = lean_nat_dec_le(v___y_1606_, v___y_1605_);
if (v___x_1607_ == 0)
{
lean_dec(v___y_1605_);
lean_inc(v___y_1606_);
v___y_1597_ = v___y_1603_;
v___y_1598_ = v___y_1604_;
v___y_1599_ = v___y_1606_;
v___y_1600_ = v___y_1606_;
goto v___jp_1596_;
}
else
{
v___y_1597_ = v___y_1603_;
v___y_1598_ = v___y_1604_;
v___y_1599_ = v___y_1606_;
v___y_1600_ = v___y_1605_;
goto v___jp_1596_;
}
}
v___jp_1608_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1610_ = lean_array_get_size(v___y_1609_);
v___x_1611_ = lean_unsigned_to_nat(0u);
v___x_1612_ = lean_nat_dec_eq(v___x_1610_, v___x_1611_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1613_ = lean_unsigned_to_nat(1u);
v___x_1614_ = lean_nat_sub(v___x_1610_, v___x_1613_);
v___x_1615_ = lean_nat_dec_le(v___x_1611_, v___x_1614_);
if (v___x_1615_ == 0)
{
lean_inc(v___x_1614_);
v___y_1603_ = v___y_1609_;
v___y_1604_ = v___x_1610_;
v___y_1605_ = v___x_1614_;
v___y_1606_ = v___x_1614_;
goto v___jp_1602_;
}
else
{
v___y_1603_ = v___y_1609_;
v___y_1604_ = v___x_1610_;
v___y_1605_ = v___x_1614_;
v___y_1606_ = v___x_1611_;
goto v___jp_1602_;
}
}
else
{
v___y_1591_ = v___y_1609_;
goto v___jp_1590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr___boxed(lean_object* v_coeff_1625_, lean_object* v_op_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_coeff_1625_, v_op_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
lean_dec_ref(v_coeff_1625_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(lean_object* v_upperBound_1636_, lean_object* v___x_1637_, lean_object* v_op_1638_, lean_object* v_inst_1639_, lean_object* v_R_1640_, lean_object* v_a_1641_, lean_object* v_b_1642_, lean_object* v_c_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1636_, v___x_1637_, v_op_1638_, v_a_1641_, v_b_1642_, v___y_1644_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___boxed(lean_object* v_upperBound_1653_, lean_object* v___x_1654_, lean_object* v_op_1655_, lean_object* v_inst_1656_, lean_object* v_R_1657_, lean_object* v_a_1658_, lean_object* v_b_1659_, lean_object* v_c_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(v_upperBound_1653_, v___x_1654_, v_op_1655_, v_inst_1656_, v_R_1657_, v_a_1658_, v_b_1659_, v_c_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v_upperBound_1653_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(lean_object* v_n_1670_, lean_object* v_as_1671_, lean_object* v_lo_1672_, lean_object* v_hi_1673_, lean_object* v_w_1674_, lean_object* v_hlo_1675_, lean_object* v_hhi_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1670_, v_as_1671_, v_lo_1672_, v_hi_1673_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___boxed(lean_object* v_n_1678_, lean_object* v_as_1679_, lean_object* v_lo_1680_, lean_object* v_hi_1681_, lean_object* v_w_1682_, lean_object* v_hlo_1683_, lean_object* v_hhi_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(v_n_1678_, v_as_1679_, v_lo_1680_, v_hi_1681_, v_w_1682_, v_hlo_1683_, v_hhi_1684_);
lean_dec(v_hi_1681_);
lean_dec(v_n_1678_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(lean_object* v_n_1686_, lean_object* v_lo_1687_, lean_object* v_hi_1688_, lean_object* v_hhi_1689_, lean_object* v_pivot_1690_, lean_object* v_as_1691_, lean_object* v_i_1692_, lean_object* v_k_1693_, lean_object* v_ilo_1694_, lean_object* v_ik_1695_, lean_object* v_w_1696_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1688_, v_pivot_1690_, v_as_1691_, v_i_1692_, v_k_1693_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___boxed(lean_object* v_n_1698_, lean_object* v_lo_1699_, lean_object* v_hi_1700_, lean_object* v_hhi_1701_, lean_object* v_pivot_1702_, lean_object* v_as_1703_, lean_object* v_i_1704_, lean_object* v_k_1705_, lean_object* v_ilo_1706_, lean_object* v_ik_1707_, lean_object* v_w_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(v_n_1698_, v_lo_1699_, v_hi_1700_, v_hhi_1701_, v_pivot_1702_, v_as_1703_, v_i_1704_, v_k_1705_, v_ilo_1706_, v_ik_1707_, v_w_1708_);
lean_dec_ref(v_pivot_1702_);
lean_dec(v_hi_1700_);
lean_dec(v_lo_1699_);
lean_dec(v_n_1698_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(lean_object* v_e_1710_, lean_object* v___y_1711_){
_start:
{
uint8_t v___x_1713_; 
v___x_1713_ = l_Lean_Expr_hasMVar(v_e_1710_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1714_, 0, v_e_1710_);
return v___x_1714_;
}
else
{
lean_object* v___x_1715_; lean_object* v_mctx_1716_; lean_object* v___x_1717_; lean_object* v_fst_1718_; lean_object* v_snd_1719_; lean_object* v___x_1720_; lean_object* v_cache_1721_; lean_object* v_zetaDeltaFVarIds_1722_; lean_object* v_postponed_1723_; lean_object* v_diag_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1733_; 
v___x_1715_ = lean_st_ref_get(v___y_1711_);
v_mctx_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc_ref(v_mctx_1716_);
lean_dec(v___x_1715_);
v___x_1717_ = l_Lean_instantiateMVarsCore(v_mctx_1716_, v_e_1710_);
v_fst_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_fst_1718_);
v_snd_1719_ = lean_ctor_get(v___x_1717_, 1);
lean_inc(v_snd_1719_);
lean_dec_ref(v___x_1717_);
v___x_1720_ = lean_st_ref_take(v___y_1711_);
v_cache_1721_ = lean_ctor_get(v___x_1720_, 1);
v_zetaDeltaFVarIds_1722_ = lean_ctor_get(v___x_1720_, 2);
v_postponed_1723_ = lean_ctor_get(v___x_1720_, 3);
v_diag_1724_ = lean_ctor_get(v___x_1720_, 4);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1733_ == 0)
{
lean_object* v_unused_1734_; 
v_unused_1734_ = lean_ctor_get(v___x_1720_, 0);
lean_dec(v_unused_1734_);
v___x_1726_ = v___x_1720_;
v_isShared_1727_ = v_isSharedCheck_1733_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_diag_1724_);
lean_inc(v_postponed_1723_);
lean_inc(v_zetaDeltaFVarIds_1722_);
lean_inc(v_cache_1721_);
lean_dec(v___x_1720_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1733_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v_snd_1719_);
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_snd_1719_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_cache_1721_);
lean_ctor_set(v_reuseFailAlloc_1732_, 2, v_zetaDeltaFVarIds_1722_);
lean_ctor_set(v_reuseFailAlloc_1732_, 3, v_postponed_1723_);
lean_ctor_set(v_reuseFailAlloc_1732_, 4, v_diag_1724_);
v___x_1729_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = lean_st_ref_put(v___y_1711_, v___x_1729_);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v_fst_1718_);
return v___x_1731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg___boxed(lean_object* v_e_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1735_, v___y_1736_);
lean_dec(v___y_1736_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(lean_object* v_e_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1739_, v___y_1741_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___boxed(lean_object* v_e_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(v_e_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(lean_object* v_x_1753_, lean_object* v_y_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Lean_Meta_mkEq(v_x_1753_, v_y_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1783_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1763_ = v___x_1760_;
v_isShared_1764_ = v_isSharedCheck_1783_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1760_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1783_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
lean_ctor_set_tag(v___x_1763_, 1);
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
uint8_t v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = 0;
v___x_1768_ = lean_box(0);
v___x_1769_ = l_Lean_Meta_mkFreshExprMVar(v___x_1766_, v___x_1767_, v___x_1768_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref_known(v___x_1769_, 1);
v___x_1771_ = l_Lean_Expr_mvarId_x21(v_a_1770_);
v___x_1772_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v___x_1771_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v___x_1773_; 
lean_dec_ref_known(v___x_1772_, 1);
v___x_1773_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_a_1770_, v_a_1756_);
return v___x_1773_;
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
lean_dec(v_a_1770_);
v_a_1774_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1772_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1772_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
else
{
return v___x_1769_;
}
}
}
}
else
{
return v___x_1760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC___boxed(lean_object* v_x_1784_, lean_object* v_y_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v_x_1784_, v_y_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
return v_res_1791_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1792_ = lean_unsigned_to_nat(32u);
v___x_1793_ = lean_mk_empty_array_with_capacity(v___x_1792_);
v___x_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
return v___x_1794_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1795_ = ((size_t)5ULL);
v___x_1796_ = lean_unsigned_to_nat(0u);
v___x_1797_ = lean_unsigned_to_nat(32u);
v___x_1798_ = lean_mk_empty_array_with_capacity(v___x_1797_);
v___x_1799_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0);
v___x_1800_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
lean_ctor_set(v___x_1800_, 1, v___x_1798_);
lean_ctor_set(v___x_1800_, 2, v___x_1796_);
lean_ctor_set(v___x_1800_, 3, v___x_1796_);
lean_ctor_set_usize(v___x_1800_, 4, v___x_1795_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; lean_object* v_traceState_1804_; lean_object* v_traces_1805_; lean_object* v___x_1806_; lean_object* v_traceState_1807_; lean_object* v_env_1808_; lean_object* v_nextMacroScope_1809_; lean_object* v_ngen_1810_; lean_object* v_auxDeclNGen_1811_; lean_object* v_cache_1812_; lean_object* v_recordedDeps_1813_; lean_object* v_messages_1814_; lean_object* v_infoState_1815_; lean_object* v_snapshotTasks_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1835_; 
v___x_1803_ = lean_st_ref_get(v___y_1801_);
v_traceState_1804_ = lean_ctor_get(v___x_1803_, 4);
lean_inc_ref(v_traceState_1804_);
lean_dec(v___x_1803_);
v_traces_1805_ = lean_ctor_get(v_traceState_1804_, 0);
lean_inc_ref(v_traces_1805_);
lean_dec_ref(v_traceState_1804_);
v___x_1806_ = lean_st_ref_take(v___y_1801_);
v_traceState_1807_ = lean_ctor_get(v___x_1806_, 4);
v_env_1808_ = lean_ctor_get(v___x_1806_, 0);
v_nextMacroScope_1809_ = lean_ctor_get(v___x_1806_, 1);
v_ngen_1810_ = lean_ctor_get(v___x_1806_, 2);
v_auxDeclNGen_1811_ = lean_ctor_get(v___x_1806_, 3);
v_cache_1812_ = lean_ctor_get(v___x_1806_, 5);
v_recordedDeps_1813_ = lean_ctor_get(v___x_1806_, 6);
v_messages_1814_ = lean_ctor_get(v___x_1806_, 7);
v_infoState_1815_ = lean_ctor_get(v___x_1806_, 8);
v_snapshotTasks_1816_ = lean_ctor_get(v___x_1806_, 9);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1818_ = v___x_1806_;
v_isShared_1819_ = v_isSharedCheck_1835_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_snapshotTasks_1816_);
lean_inc(v_infoState_1815_);
lean_inc(v_messages_1814_);
lean_inc(v_recordedDeps_1813_);
lean_inc(v_cache_1812_);
lean_inc(v_traceState_1807_);
lean_inc(v_auxDeclNGen_1811_);
lean_inc(v_ngen_1810_);
lean_inc(v_nextMacroScope_1809_);
lean_inc(v_env_1808_);
lean_dec(v___x_1806_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1835_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
uint64_t v_tid_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1833_; 
v_tid_1820_ = lean_ctor_get_uint64(v_traceState_1807_, sizeof(void*)*1);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_traceState_1807_);
if (v_isSharedCheck_1833_ == 0)
{
lean_object* v_unused_1834_; 
v_unused_1834_ = lean_ctor_get(v_traceState_1807_, 0);
lean_dec(v_unused_1834_);
v___x_1822_ = v_traceState_1807_;
v_isShared_1823_ = v_isSharedCheck_1833_;
goto v_resetjp_1821_;
}
else
{
lean_dec(v_traceState_1807_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1833_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1824_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v___x_1824_);
v___x_1826_ = v___x_1822_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1824_);
lean_ctor_set_uint64(v_reuseFailAlloc_1832_, sizeof(void*)*1, v_tid_1820_);
v___x_1826_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v___x_1828_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 4, v___x_1826_);
v___x_1828_ = v___x_1818_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_env_1808_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_nextMacroScope_1809_);
lean_ctor_set(v_reuseFailAlloc_1831_, 2, v_ngen_1810_);
lean_ctor_set(v_reuseFailAlloc_1831_, 3, v_auxDeclNGen_1811_);
lean_ctor_set(v_reuseFailAlloc_1831_, 4, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1831_, 5, v_cache_1812_);
lean_ctor_set(v_reuseFailAlloc_1831_, 6, v_recordedDeps_1813_);
lean_ctor_set(v_reuseFailAlloc_1831_, 7, v_messages_1814_);
lean_ctor_set(v_reuseFailAlloc_1831_, 8, v_infoState_1815_);
lean_ctor_set(v_reuseFailAlloc_1831_, 9, v_snapshotTasks_1816_);
v___x_1828_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = lean_st_ref_put(v___y_1801_, v___x_1828_);
v___x_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1830_, 0, v_traces_1805_);
return v___x_1830_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___boxed(lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1836_);
lean_dec(v___y_1836_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1847_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
return v_res_1860_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(lean_object* v_opts_1861_, lean_object* v_opt_1862_){
_start:
{
lean_object* v_name_1863_; lean_object* v_defValue_1864_; lean_object* v_map_1865_; lean_object* v___x_1866_; 
v_name_1863_ = lean_ctor_get(v_opt_1862_, 0);
v_defValue_1864_ = lean_ctor_get(v_opt_1862_, 1);
v_map_1865_ = lean_ctor_get(v_opts_1861_, 0);
v___x_1866_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1865_, v_name_1863_);
if (lean_obj_tag(v___x_1866_) == 0)
{
uint8_t v___x_1867_; 
v___x_1867_ = lean_unbox(v_defValue_1864_);
return v___x_1867_;
}
else
{
lean_object* v_val_1868_; 
v_val_1868_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_val_1868_);
lean_dec_ref_known(v___x_1866_, 1);
if (lean_obj_tag(v_val_1868_) == 1)
{
uint8_t v_v_1869_; 
v_v_1869_ = lean_ctor_get_uint8(v_val_1868_, 0);
lean_dec_ref_known(v_val_1868_, 0);
return v_v_1869_;
}
else
{
uint8_t v___x_1870_; 
lean_dec(v_val_1868_);
v___x_1870_ = lean_unbox(v_defValue_1864_);
return v___x_1870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object* v_opts_1871_, lean_object* v_opt_1872_){
_start:
{
uint8_t v_res_1873_; lean_object* v_r_1874_; 
v_res_1873_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_1871_, v_opt_1872_);
lean_dec_ref(v_opt_1872_);
lean_dec_ref(v_opts_1871_);
v_r_1874_ = lean_box(v_res_1873_);
return v_r_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(lean_object* v_cls_1875_, lean_object* v_____do__lift_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_toCold_1887_; lean_object* v_options_1888_; uint8_t v_hasTrace_1889_; 
v_toCold_1887_ = lean_ctor_get(v___y_1884_, 0);
v_options_1888_ = lean_ctor_get(v_toCold_1887_, 2);
v_hasTrace_1889_ = lean_ctor_get_uint8(v_options_1888_, sizeof(void*)*1);
if (v_hasTrace_1889_ == 0)
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
lean_dec(v_cls_1875_);
v___x_1890_ = lean_box(v_hasTrace_1889_);
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
return v___x_1891_;
}
else
{
lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1892_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_1893_ = l_Lean_Name_append(v___x_1892_, v_cls_1875_);
v___x_1894_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_1876_, v_options_1888_, v___x_1893_);
lean_dec(v___x_1893_);
v___x_1895_ = lean_box(v___x_1894_);
v___x_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
return v___x_1896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0___boxed(lean_object* v_cls_1897_, lean_object* v_____do__lift_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_1897_, v_____do__lift_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v_____do__lift_1898_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1(lean_object* v___x_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Lean_mkAppB(v___x_1910_, v___y_1911_, v___y_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(lean_object* v_val_1914_, lean_object* v_lhs_1915_, lean_object* v_rhs_1916_, lean_object* v_P_1917_, uint8_t v___x_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v___x_1927_; 
lean_inc_ref(v_lhs_1915_);
lean_inc_ref(v_val_1914_);
v___x_1927_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1914_, v_lhs_1915_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v_fst_1929_; lean_object* v_snd_1930_; lean_object* v___x_1931_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
v_fst_1929_ = lean_ctor_get(v_a_1928_, 0);
lean_inc(v_fst_1929_);
v_snd_1930_ = lean_ctor_get(v_a_1928_, 1);
lean_inc(v_snd_1930_);
lean_dec(v_a_1928_);
lean_inc_ref(v_rhs_1916_);
lean_inc_ref(v_val_1914_);
v___x_1931_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1914_, v_rhs_1916_, v_snd_1930_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v_fst_1933_; lean_object* v_snd_1934_; lean_object* v___x_1935_; lean_object* v_a_1936_; lean_object* v_fst_1937_; lean_object* v_snd_1938_; lean_object* v_common_1939_; lean_object* v_x_1940_; lean_object* v_y_1941_; lean_object* v___x_1942_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1931_, 1);
v_fst_1933_ = lean_ctor_get(v_a_1932_, 0);
lean_inc(v_fst_1933_);
v_snd_1934_ = lean_ctor_get(v_a_1932_, 1);
lean_inc(v_snd_1934_);
lean_dec(v_a_1932_);
v___x_1935_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_1929_, v_fst_1933_, v_snd_1934_);
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref(v___x_1935_);
v_fst_1937_ = lean_ctor_get(v_a_1936_, 0);
lean_inc(v_fst_1937_);
v_snd_1938_ = lean_ctor_get(v_a_1936_, 1);
lean_inc(v_snd_1938_);
lean_dec(v_a_1936_);
v_common_1939_ = lean_ctor_get(v_fst_1937_, 0);
lean_inc_ref(v_common_1939_);
v_x_1940_ = lean_ctor_get(v_fst_1937_, 1);
lean_inc_ref(v_x_1940_);
v_y_1941_ = lean_ctor_get(v_fst_1937_, 2);
lean_inc_ref(v_y_1941_);
lean_dec(v_fst_1937_);
lean_inc_ref(v_val_1914_);
v___x_1942_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_1939_, v_val_1914_, v_snd_1938_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
lean_dec_ref(v_common_1939_);
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
lean_inc_ref(v_val_1914_);
v___x_1946_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_1940_, v_val_1914_, v_snd_1945_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
lean_dec_ref(v_x_1940_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v_fst_1948_; lean_object* v_snd_1949_; lean_object* v___x_1950_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1946_, 1);
v_fst_1948_ = lean_ctor_get(v_a_1947_, 0);
lean_inc(v_fst_1948_);
v_snd_1949_ = lean_ctor_get(v_a_1947_, 1);
lean_inc(v_snd_1949_);
lean_dec(v_a_1947_);
lean_inc_ref(v_val_1914_);
v___x_1950_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_1941_, v_val_1914_, v_snd_1949_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
lean_dec_ref(v_y_1941_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_2015_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_1953_ = v___x_1950_;
v_isShared_1954_ = v_isSharedCheck_2015_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_2015_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v_fst_1955_; lean_object* v_snd_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_2014_; 
v_fst_1955_ = lean_ctor_get(v_a_1951_, 0);
v_snd_1956_ = lean_ctor_get(v_a_1951_, 1);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_a_1951_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1958_ = v_a_1951_;
v_isShared_1959_ = v_isSharedCheck_2014_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_snd_1956_);
lean_inc(v_fst_1955_);
lean_dec(v_a_1951_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_2014_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___x_2004_; lean_object* v___f_2005_; lean_object* v___y_2007_; lean_object* v___x_2011_; 
lean_inc_ref(v_val_1914_);
v___x_2004_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_1914_);
v___f_2005_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_2005_, 0, v___x_2004_);
lean_inc(v_fst_1944_);
lean_inc_ref(v___f_2005_);
v___x_2011_ = l_Option_merge___redArg(v___f_2005_, v_fst_1944_, v_fst_1948_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v___x_2012_; 
lean_inc_ref(v_val_1914_);
v___x_2012_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1914_);
v___y_2007_ = v___x_2012_;
goto v___jp_2006_;
}
else
{
lean_object* v_val_2013_; 
v_val_2013_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_val_2013_);
lean_dec_ref_known(v___x_2011_, 1);
v___y_2007_ = v_val_2013_;
goto v___jp_2006_;
}
v___jp_1960_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
lean_inc_ref(v_P_1917_);
v___x_1963_ = l_Lean_mkAppB(v_P_1917_, v_lhs_1915_, v_rhs_1916_);
v___x_1964_ = l_Lean_mkAppB(v_P_1917_, v___y_1961_, v___y_1962_);
v___x_1965_ = lean_expr_eqv(v___x_1963_, v___x_1964_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; 
lean_del_object(v___x_1953_);
lean_inc_ref(v___x_1964_);
v___x_1966_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_1963_, v___x_1964_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1968_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
v___x_1968_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1964_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1980_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_1980_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1980_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1973_; lean_object* v___x_1975_; 
v___x_1973_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1973_, 0, v_a_1969_);
lean_ctor_set(v___x_1973_, 1, v_a_1967_);
lean_ctor_set_uint8(v___x_1973_, sizeof(void*)*2, v___x_1965_);
lean_ctor_set_uint8(v___x_1973_, sizeof(void*)*2 + 1, v___x_1965_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1973_);
v___x_1975_ = v___x_1958_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v_snd_1956_);
v___x_1975_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
lean_object* v___x_1977_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v___x_1975_);
v___x_1977_ = v___x_1971_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
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
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_dec(v_a_1967_);
lean_del_object(v___x_1958_);
lean_dec(v_snd_1956_);
v_a_1981_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1968_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1968_);
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
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec_ref(v___x_1964_);
lean_del_object(v___x_1958_);
lean_dec(v_snd_1956_);
v_a_1989_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1966_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1966_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1999_; 
lean_dec_ref(v___x_1964_);
lean_dec_ref(v___x_1963_);
v___x_1997_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1997_, 0, v___x_1918_);
lean_ctor_set_uint8(v___x_1997_, 1, v___x_1918_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1997_);
v___x_1999_ = v___x_1958_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1997_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_snd_1956_);
v___x_1999_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2001_; 
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 0, v___x_1999_);
v___x_2001_ = v___x_1953_;
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
v___jp_2006_:
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Option_merge___redArg(v___f_2005_, v_fst_1944_, v_fst_1955_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v___x_2009_; 
v___x_2009_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1914_);
v___y_1961_ = v___y_2007_;
v___y_1962_ = v___x_2009_;
goto v___jp_1960_;
}
else
{
lean_object* v_val_2010_; 
lean_dec_ref(v_val_1914_);
v_val_2010_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_val_2010_);
lean_dec_ref_known(v___x_2008_, 1);
v___y_1961_ = v___y_2007_;
v___y_1962_ = v_val_2010_;
goto v___jp_1960_;
}
}
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec(v_fst_1948_);
lean_dec(v_fst_1944_);
lean_dec_ref(v_P_1917_);
lean_dec_ref(v_rhs_1916_);
lean_dec_ref(v_lhs_1915_);
lean_dec_ref(v_val_1914_);
v_a_2016_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_1950_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_1950_);
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
lean_dec(v_fst_1944_);
lean_dec_ref(v_y_1941_);
lean_dec_ref(v_P_1917_);
lean_dec_ref(v_rhs_1916_);
lean_dec_ref(v_lhs_1915_);
lean_dec_ref(v_val_1914_);
v_a_2024_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_1946_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_1946_);
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
lean_dec_ref(v_y_1941_);
lean_dec_ref(v_x_1940_);
lean_dec_ref(v_P_1917_);
lean_dec_ref(v_rhs_1916_);
lean_dec_ref(v_lhs_1915_);
lean_dec_ref(v_val_1914_);
v_a_2032_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_1942_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_1942_);
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
lean_dec(v_fst_1929_);
lean_dec_ref(v_P_1917_);
lean_dec_ref(v_rhs_1916_);
lean_dec_ref(v_lhs_1915_);
lean_dec_ref(v_val_1914_);
v_a_2040_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_1931_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_1931_);
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
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec_ref(v_P_1917_);
lean_dec_ref(v_rhs_1916_);
lean_dec_ref(v_lhs_1915_);
lean_dec_ref(v_val_1914_);
v_a_2048_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_1927_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_1927_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object* v_val_2056_, lean_object* v_lhs_2057_, lean_object* v_rhs_2058_, lean_object* v_P_2059_, lean_object* v___x_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
uint8_t v___x_187933__boxed_2069_; lean_object* v_res_2070_; 
v___x_187933__boxed_2069_ = lean_unbox(v___x_2060_);
v_res_2070_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(v_val_2056_, v_lhs_2057_, v_rhs_2058_, v_P_2059_, v___x_187933__boxed_2069_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
return v_res_2070_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_2073_ = l_Lean_stringToMessageData(v___x_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(lean_object* v_x_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1);
v___x_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object* v_x_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(v_x_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v_x_2087_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object* v_cls_2099_, lean_object* v_msg_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_ref_2106_; lean_object* v___x_2107_; lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2153_; 
v_ref_2106_ = lean_ctor_get(v___y_2103_, 2);
v___x_2107_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2110_ = v___x_2107_;
v_isShared_2111_ = v_isSharedCheck_2153_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2107_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2153_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2112_; lean_object* v_traceState_2113_; lean_object* v_env_2114_; lean_object* v_nextMacroScope_2115_; lean_object* v_ngen_2116_; lean_object* v_auxDeclNGen_2117_; lean_object* v_cache_2118_; lean_object* v_recordedDeps_2119_; lean_object* v_messages_2120_; lean_object* v_infoState_2121_; lean_object* v_snapshotTasks_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2152_; 
v___x_2112_ = lean_st_ref_take(v___y_2104_);
v_traceState_2113_ = lean_ctor_get(v___x_2112_, 4);
v_env_2114_ = lean_ctor_get(v___x_2112_, 0);
v_nextMacroScope_2115_ = lean_ctor_get(v___x_2112_, 1);
v_ngen_2116_ = lean_ctor_get(v___x_2112_, 2);
v_auxDeclNGen_2117_ = lean_ctor_get(v___x_2112_, 3);
v_cache_2118_ = lean_ctor_get(v___x_2112_, 5);
v_recordedDeps_2119_ = lean_ctor_get(v___x_2112_, 6);
v_messages_2120_ = lean_ctor_get(v___x_2112_, 7);
v_infoState_2121_ = lean_ctor_get(v___x_2112_, 8);
v_snapshotTasks_2122_ = lean_ctor_get(v___x_2112_, 9);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2124_ = v___x_2112_;
v_isShared_2125_ = v_isSharedCheck_2152_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_snapshotTasks_2122_);
lean_inc(v_infoState_2121_);
lean_inc(v_messages_2120_);
lean_inc(v_recordedDeps_2119_);
lean_inc(v_cache_2118_);
lean_inc(v_traceState_2113_);
lean_inc(v_auxDeclNGen_2117_);
lean_inc(v_ngen_2116_);
lean_inc(v_nextMacroScope_2115_);
lean_inc(v_env_2114_);
lean_dec(v___x_2112_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2152_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
uint64_t v_tid_2126_; lean_object* v_traces_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2151_; 
v_tid_2126_ = lean_ctor_get_uint64(v_traceState_2113_, sizeof(void*)*1);
v_traces_2127_ = lean_ctor_get(v_traceState_2113_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_traceState_2113_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2129_ = v_traceState_2113_;
v_isShared_2130_ = v_isSharedCheck_2151_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_traces_2127_);
lean_dec(v_traceState_2113_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2151_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; double v___x_2133_; uint8_t v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2131_ = lean_box(0);
v___x_2132_ = lean_box(0);
v___x_2133_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_2134_ = 0;
v___x_2135_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_2136_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2136_, 0, v_cls_2099_);
lean_ctor_set(v___x_2136_, 1, v___x_2132_);
lean_ctor_set(v___x_2136_, 2, v___x_2135_);
lean_ctor_set_float(v___x_2136_, sizeof(void*)*3, v___x_2133_);
lean_ctor_set_float(v___x_2136_, sizeof(void*)*3 + 8, v___x_2133_);
lean_ctor_set_uint8(v___x_2136_, sizeof(void*)*3 + 16, v___x_2134_);
v___x_2137_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_2138_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2136_);
lean_ctor_set(v___x_2138_, 1, v_a_2108_);
lean_ctor_set(v___x_2138_, 2, v___x_2137_);
lean_inc(v_ref_2106_);
v___x_2139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2139_, 0, v_ref_2106_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = l_Lean_PersistentArray_push___redArg(v_traces_2127_, v___x_2139_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v___x_2140_);
v___x_2142_ = v___x_2129_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2140_);
lean_ctor_set_uint64(v_reuseFailAlloc_2150_, sizeof(void*)*1, v_tid_2126_);
v___x_2142_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2144_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 4, v___x_2142_);
v___x_2144_ = v___x_2124_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_env_2114_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_nextMacroScope_2115_);
lean_ctor_set(v_reuseFailAlloc_2149_, 2, v_ngen_2116_);
lean_ctor_set(v_reuseFailAlloc_2149_, 3, v_auxDeclNGen_2117_);
lean_ctor_set(v_reuseFailAlloc_2149_, 4, v___x_2142_);
lean_ctor_set(v_reuseFailAlloc_2149_, 5, v_cache_2118_);
lean_ctor_set(v_reuseFailAlloc_2149_, 6, v_recordedDeps_2119_);
lean_ctor_set(v_reuseFailAlloc_2149_, 7, v_messages_2120_);
lean_ctor_set(v_reuseFailAlloc_2149_, 8, v_infoState_2121_);
lean_ctor_set(v_reuseFailAlloc_2149_, 9, v_snapshotTasks_2122_);
v___x_2144_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_object* v___x_2145_; lean_object* v___x_2147_; 
v___x_2145_ = lean_st_ref_put(v___y_2104_, v___x_2144_);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 0, v___x_2131_);
v___x_2147_ = v___x_2110_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2131_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object* v_cls_2154_, lean_object* v_msg_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2154_, v_msg_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
return v_res_2161_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1));
v___x_2166_ = l_Lean_stringToMessageData(v___x_2165_);
return v___x_2166_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4(void){
_start:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2168_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3));
v___x_2169_ = l_Lean_stringToMessageData(v___x_2168_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5));
v___x_2172_ = l_Lean_stringToMessageData(v___x_2171_);
return v___x_2172_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2173_ = lean_box(0);
v___x_2174_ = lean_unsigned_to_nat(16u);
v___x_2175_ = lean_mk_array(v___x_2174_, v___x_2173_);
return v___x_2175_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7);
v___x_2177_ = lean_unsigned_to_nat(0u);
v___x_2178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2177_);
lean_ctor_set(v___x_2178_, 1, v___x_2176_);
return v___x_2178_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11(void){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10));
v___x_2183_ = l_Lean_stringToMessageData(v___x_2182_);
return v___x_2183_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13(void){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12));
v___x_2186_ = l_Lean_stringToMessageData(v___x_2185_);
return v___x_2186_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14));
v___x_2189_ = l_Lean_stringToMessageData(v___x_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(lean_object* v_lhs_2190_, lean_object* v_rhs_2191_, lean_object* v___f_2192_, lean_object* v_cls_2193_, lean_object* v_P_2194_, lean_object* v_____r_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v___x_2212_; 
lean_inc_ref(v_lhs_2190_);
v___x_2212_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2190_);
if (lean_obj_tag(v___x_2212_) == 1)
{
lean_object* v_val_2213_; lean_object* v___x_2214_; 
v_val_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_val_2213_);
lean_dec_ref_known(v___x_2212_, 1);
lean_inc_ref(v_rhs_2191_);
v___x_2214_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2191_);
if (lean_obj_tag(v___x_2214_) == 1)
{
lean_object* v_val_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2299_; 
v_val_2215_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2217_ = v___x_2214_;
v_isShared_2218_ = v_isSharedCheck_2299_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_val_2215_);
lean_dec(v___x_2214_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2299_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
uint8_t v___x_2219_; 
v___x_2219_ = lean_expr_eqv(v_val_2213_, v_val_2215_);
if (v___x_2219_ == 0)
{
lean_object* v_toCold_2225_; lean_object* v_inheritedTraceOptions_2226_; lean_object* v___x_2227_; 
lean_dec_ref(v_P_2194_);
v_toCold_2225_ = lean_ctor_get(v___y_2203_, 0);
v_inheritedTraceOptions_2226_ = lean_ctor_get(v_toCold_2225_, 11);
lean_inc(v___y_2204_);
lean_inc_ref(v___y_2203_);
lean_inc(v___y_2202_);
lean_inc_ref(v___y_2201_);
lean_inc(v___y_2200_);
lean_inc_ref(v___y_2199_);
lean_inc(v___y_2198_);
lean_inc_ref(v___y_2197_);
lean_inc(v___y_2196_);
lean_inc_ref(v_inheritedTraceOptions_2226_);
v___x_2227_ = lean_apply_11(v___f_2192_, v_inheritedTraceOptions_2226_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, lean_box(0));
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; uint8_t v___x_2229_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref_known(v___x_2227_, 1);
v___x_2229_ = lean_unbox(v_a_2228_);
lean_dec(v_a_2228_);
if (v___x_2229_ == 0)
{
lean_dec(v_val_2215_);
lean_dec(v_val_2213_);
lean_dec(v_cls_2193_);
lean_dec_ref(v_rhs_2191_);
lean_dec_ref(v_lhs_2190_);
goto v___jp_2220_;
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2230_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2);
v___x_2231_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2213_);
v___x_2232_ = l_Lean_MessageData_ofExpr(v___x_2231_);
v___x_2233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2230_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
v___x_2234_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4);
v___x_2235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2233_);
lean_ctor_set(v___x_2235_, 1, v___x_2234_);
v___x_2236_ = l_Lean_indentExpr(v_lhs_2190_);
v___x_2237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2235_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
v___x_2238_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6);
v___x_2239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2237_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2215_);
v___x_2241_ = l_Lean_MessageData_ofExpr(v___x_2240_);
v___x_2242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2239_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
v___x_2243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
lean_ctor_set(v___x_2243_, 1, v___x_2234_);
v___x_2244_ = l_Lean_indentExpr(v_rhs_2191_);
v___x_2245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2243_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
v___x_2246_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2193_, v___x_2245_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_dec_ref_known(v___x_2246_, 1);
goto v___jp_2220_;
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_del_object(v___x_2217_);
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2246_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2246_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_del_object(v___x_2217_);
lean_dec(v_val_2215_);
lean_dec(v_val_2213_);
lean_dec(v_cls_2193_);
lean_dec_ref(v_rhs_2191_);
lean_dec_ref(v_lhs_2190_);
v_a_2255_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2227_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2227_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
else
{
lean_object* v_toCold_2263_; lean_object* v_options_2264_; lean_object* v_inheritedTraceOptions_2265_; uint8_t v_hasTrace_2266_; uint8_t v___x_2267_; lean_object* v___x_2268_; lean_object* v___f_2269_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; 
lean_del_object(v___x_2217_);
lean_dec(v_val_2215_);
lean_dec_ref(v___f_2192_);
v_toCold_2263_ = lean_ctor_get(v___y_2203_, 0);
v_options_2264_ = lean_ctor_get(v_toCold_2263_, 2);
v_inheritedTraceOptions_2265_ = lean_ctor_get(v_toCold_2263_, 11);
v_hasTrace_2266_ = lean_ctor_get_uint8(v_options_2264_, sizeof(void*)*1);
v___x_2267_ = 0;
v___x_2268_ = lean_box(v___x_2267_);
lean_inc(v_val_2213_);
v___f_2269_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 13, 5);
lean_closure_set(v___f_2269_, 0, v_val_2213_);
lean_closure_set(v___f_2269_, 1, v_lhs_2190_);
lean_closure_set(v___f_2269_, 2, v_rhs_2191_);
lean_closure_set(v___f_2269_, 3, v_P_2194_);
lean_closure_set(v___f_2269_, 4, v___x_2268_);
if (v_hasTrace_2266_ == 0)
{
lean_dec(v_cls_2193_);
v___y_2271_ = v___y_2199_;
v___y_2272_ = v___y_2200_;
v___y_2273_ = v___y_2201_;
v___y_2274_ = v___y_2202_;
v___y_2275_ = v___y_2203_;
v___y_2276_ = v___y_2204_;
goto v___jp_2270_;
}
else
{
lean_object* v___x_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; 
v___x_2281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2193_);
v___x_2282_ = l_Lean_Name_append(v___x_2281_, v_cls_2193_);
v___x_2283_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2265_, v_options_2264_, v___x_2282_);
lean_dec(v___x_2282_);
if (v___x_2283_ == 0)
{
lean_dec(v_cls_2193_);
v___y_2271_ = v___y_2199_;
v___y_2272_ = v___y_2200_;
v___y_2273_ = v___y_2201_;
v___y_2274_ = v___y_2202_;
v___y_2275_ = v___y_2203_;
v___y_2276_ = v___y_2204_;
goto v___jp_2270_;
}
else
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2284_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11);
lean_inc(v_val_2213_);
v___x_2285_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2213_);
v___x_2286_ = l_Lean_MessageData_ofExpr(v___x_2285_);
v___x_2287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2284_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
v___x_2288_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13);
v___x_2289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2287_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2193_, v___x_2289_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_dec_ref_known(v___x_2290_, 1);
v___y_2271_ = v___y_2199_;
v___y_2272_ = v___y_2200_;
v___y_2273_ = v___y_2201_;
v___y_2274_ = v___y_2202_;
v___y_2275_ = v___y_2203_;
v___y_2276_ = v___y_2204_;
goto v___jp_2270_;
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec_ref(v___f_2269_);
lean_dec(v_val_2213_);
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2290_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2290_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
}
v___jp_2270_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2277_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8);
v___x_2278_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9));
v___x_2279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2279_, 0, v_val_2213_);
lean_ctor_set(v___x_2279_, 1, v___x_2277_);
lean_ctor_set(v___x_2279_, 2, v___x_2278_);
v___x_2280_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___f_2269_, v___x_2279_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
return v___x_2280_;
}
}
v___jp_2220_:
{
lean_object* v___x_2221_; lean_object* v___x_2223_; 
v___x_2221_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2221_, 0, v___x_2219_);
lean_ctor_set_uint8(v___x_2221_, 1, v___x_2219_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set_tag(v___x_2217_, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2221_);
v___x_2223_ = v___x_2217_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2221_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
else
{
lean_object* v_toCold_2300_; lean_object* v_inheritedTraceOptions_2301_; lean_object* v___x_2302_; 
lean_dec(v___x_2214_);
lean_dec(v_val_2213_);
lean_dec_ref(v_P_2194_);
lean_dec_ref(v_lhs_2190_);
v_toCold_2300_ = lean_ctor_get(v___y_2203_, 0);
v_inheritedTraceOptions_2301_ = lean_ctor_get(v_toCold_2300_, 11);
lean_inc(v___y_2204_);
lean_inc_ref(v___y_2203_);
lean_inc(v___y_2202_);
lean_inc_ref(v___y_2201_);
lean_inc(v___y_2200_);
lean_inc_ref(v___y_2199_);
lean_inc(v___y_2198_);
lean_inc_ref(v___y_2197_);
lean_inc(v___y_2196_);
lean_inc_ref(v_inheritedTraceOptions_2301_);
v___x_2302_ = lean_apply_11(v___f_2192_, v_inheritedTraceOptions_2301_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, lean_box(0));
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; uint8_t v___x_2304_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v___x_2304_ = lean_unbox(v_a_2303_);
lean_dec(v_a_2303_);
if (v___x_2304_ == 0)
{
lean_dec(v_cls_2193_);
lean_dec_ref(v_rhs_2191_);
goto v___jp_2206_;
}
else
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2305_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15);
v___x_2306_ = l_Lean_indentExpr(v_rhs_2191_);
v___x_2307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2305_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2193_, v___x_2307_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_dec_ref_known(v___x_2308_, 1);
goto v___jp_2206_;
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2308_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2308_);
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
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
lean_dec(v_cls_2193_);
lean_dec_ref(v_rhs_2191_);
v_a_2317_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2302_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2302_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2317_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
}
else
{
lean_object* v_toCold_2325_; lean_object* v_inheritedTraceOptions_2326_; lean_object* v___x_2327_; 
lean_dec(v___x_2212_);
lean_dec_ref(v_P_2194_);
lean_dec_ref(v_rhs_2191_);
v_toCold_2325_ = lean_ctor_get(v___y_2203_, 0);
v_inheritedTraceOptions_2326_ = lean_ctor_get(v_toCold_2325_, 11);
lean_inc(v___y_2204_);
lean_inc_ref(v___y_2203_);
lean_inc(v___y_2202_);
lean_inc_ref(v___y_2201_);
lean_inc(v___y_2200_);
lean_inc_ref(v___y_2199_);
lean_inc(v___y_2198_);
lean_inc_ref(v___y_2197_);
lean_inc(v___y_2196_);
lean_inc_ref(v_inheritedTraceOptions_2326_);
v___x_2327_ = lean_apply_11(v___f_2192_, v_inheritedTraceOptions_2326_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, lean_box(0));
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; uint8_t v___x_2329_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2327_, 1);
v___x_2329_ = lean_unbox(v_a_2328_);
lean_dec(v_a_2328_);
if (v___x_2329_ == 0)
{
lean_dec(v_cls_2193_);
lean_dec_ref(v_lhs_2190_);
goto v___jp_2209_;
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2330_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15);
v___x_2331_ = l_Lean_indentExpr(v_lhs_2190_);
v___x_2332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2330_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
v___x_2333_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2193_, v___x_2332_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_dec_ref_known(v___x_2333_, 1);
goto v___jp_2209_;
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2333_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2333_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec(v_cls_2193_);
lean_dec_ref(v_lhs_2190_);
v_a_2342_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2327_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2327_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
v___jp_2206_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
return v___x_2208_;
}
v___jp_2209_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
return v___x_2211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___boxed(lean_object* v_lhs_2350_, lean_object* v_rhs_2351_, lean_object* v___f_2352_, lean_object* v_cls_2353_, lean_object* v_P_2354_, lean_object* v_____r_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2350_, v_rhs_2351_, v___f_2352_, v_cls_2353_, v_P_2354_, v_____r_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(lean_object* v_lhs_2367_, lean_object* v_rhs_2368_, uint8_t v___x_2369_, lean_object* v___f_2370_, lean_object* v_cls_2371_, lean_object* v_P_2372_, lean_object* v_____r_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v___x_2393_; 
lean_inc_ref(v_lhs_2367_);
v___x_2393_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2367_);
if (lean_obj_tag(v___x_2393_) == 1)
{
lean_object* v_val_2394_; lean_object* v___x_2395_; 
v_val_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_val_2394_);
lean_dec_ref_known(v___x_2393_, 1);
lean_inc_ref(v_rhs_2368_);
v___x_2395_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2368_);
if (lean_obj_tag(v___x_2395_) == 1)
{
lean_object* v_val_2396_; uint8_t v___x_2397_; 
v_val_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_val_2396_);
lean_dec_ref_known(v___x_2395_, 1);
v___x_2397_ = lean_expr_eqv(v_val_2394_, v_val_2396_);
if (v___x_2397_ == 0)
{
lean_object* v_toCold_2398_; lean_object* v_inheritedTraceOptions_2399_; lean_object* v___x_2400_; 
lean_dec_ref(v_P_2372_);
v_toCold_2398_ = lean_ctor_get(v___y_2381_, 0);
v_inheritedTraceOptions_2399_ = lean_ctor_get(v_toCold_2398_, 11);
lean_inc(v___y_2382_);
lean_inc_ref(v___y_2381_);
lean_inc(v___y_2380_);
lean_inc_ref(v___y_2379_);
lean_inc(v___y_2378_);
lean_inc_ref(v___y_2377_);
lean_inc(v___y_2376_);
lean_inc_ref(v___y_2375_);
lean_inc(v___y_2374_);
lean_inc_ref(v_inheritedTraceOptions_2399_);
v___x_2400_ = lean_apply_11(v___f_2370_, v_inheritedTraceOptions_2399_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, lean_box(0));
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; uint8_t v___x_2402_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___x_2400_, 1);
v___x_2402_ = lean_unbox(v_a_2401_);
lean_dec(v_a_2401_);
if (v___x_2402_ == 0)
{
lean_dec(v_val_2396_);
lean_dec(v_val_2394_);
lean_dec(v_cls_2371_);
lean_dec_ref(v_rhs_2368_);
lean_dec_ref(v_lhs_2367_);
goto v___jp_2384_;
}
else
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2403_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2);
v___x_2404_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2394_);
v___x_2405_ = l_Lean_MessageData_ofExpr(v___x_2404_);
v___x_2406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2403_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4);
v___x_2408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2406_);
lean_ctor_set(v___x_2408_, 1, v___x_2407_);
v___x_2409_ = l_Lean_indentExpr(v_lhs_2367_);
v___x_2410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6);
v___x_2412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2410_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2396_);
v___x_2414_ = l_Lean_MessageData_ofExpr(v___x_2413_);
v___x_2415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2412_);
lean_ctor_set(v___x_2415_, 1, v___x_2414_);
v___x_2416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
lean_ctor_set(v___x_2416_, 1, v___x_2407_);
v___x_2417_ = l_Lean_indentExpr(v_rhs_2368_);
v___x_2418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2416_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
v___x_2419_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2371_, v___x_2418_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_dec_ref_known(v___x_2419_, 1);
goto v___jp_2384_;
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2419_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2419_);
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
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec(v_val_2396_);
lean_dec(v_val_2394_);
lean_dec(v_cls_2371_);
lean_dec_ref(v_rhs_2368_);
lean_dec_ref(v_lhs_2367_);
v_a_2428_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2400_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2400_);
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
lean_object* v_toCold_2436_; lean_object* v_options_2437_; lean_object* v_inheritedTraceOptions_2438_; uint8_t v_hasTrace_2439_; lean_object* v___x_2440_; lean_object* v___f_2441_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; 
lean_dec(v_val_2396_);
lean_dec_ref(v___f_2370_);
v_toCold_2436_ = lean_ctor_get(v___y_2381_, 0);
v_options_2437_ = lean_ctor_get(v_toCold_2436_, 2);
v_inheritedTraceOptions_2438_ = lean_ctor_get(v_toCold_2436_, 11);
v_hasTrace_2439_ = lean_ctor_get_uint8(v_options_2437_, sizeof(void*)*1);
v___x_2440_ = lean_box(v___x_2369_);
lean_inc(v_val_2394_);
v___f_2441_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 13, 5);
lean_closure_set(v___f_2441_, 0, v_val_2394_);
lean_closure_set(v___f_2441_, 1, v_lhs_2367_);
lean_closure_set(v___f_2441_, 2, v_rhs_2368_);
lean_closure_set(v___f_2441_, 3, v_P_2372_);
lean_closure_set(v___f_2441_, 4, v___x_2440_);
if (v_hasTrace_2439_ == 0)
{
lean_dec(v_cls_2371_);
v___y_2443_ = v___y_2377_;
v___y_2444_ = v___y_2378_;
v___y_2445_ = v___y_2379_;
v___y_2446_ = v___y_2380_;
v___y_2447_ = v___y_2381_;
v___y_2448_ = v___y_2382_;
goto v___jp_2442_;
}
else
{
lean_object* v___x_2453_; lean_object* v___x_2454_; uint8_t v___x_2455_; 
v___x_2453_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2371_);
v___x_2454_ = l_Lean_Name_append(v___x_2453_, v_cls_2371_);
v___x_2455_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2438_, v_options_2437_, v___x_2454_);
lean_dec(v___x_2454_);
if (v___x_2455_ == 0)
{
lean_dec(v_cls_2371_);
v___y_2443_ = v___y_2377_;
v___y_2444_ = v___y_2378_;
v___y_2445_ = v___y_2379_;
v___y_2446_ = v___y_2380_;
v___y_2447_ = v___y_2381_;
v___y_2448_ = v___y_2382_;
goto v___jp_2442_;
}
else
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2456_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11);
lean_inc(v_val_2394_);
v___x_2457_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2394_);
v___x_2458_ = l_Lean_MessageData_ofExpr(v___x_2457_);
v___x_2459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2456_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
v___x_2460_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13);
v___x_2461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2459_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2371_, v___x_2461_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_dec_ref_known(v___x_2462_, 1);
v___y_2443_ = v___y_2377_;
v___y_2444_ = v___y_2378_;
v___y_2445_ = v___y_2379_;
v___y_2446_ = v___y_2380_;
v___y_2447_ = v___y_2381_;
v___y_2448_ = v___y_2382_;
goto v___jp_2442_;
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec_ref(v___f_2441_);
lean_dec(v_val_2394_);
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2462_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2462_);
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
}
v___jp_2442_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2449_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8);
v___x_2450_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9));
v___x_2451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2451_, 0, v_val_2394_);
lean_ctor_set(v___x_2451_, 1, v___x_2449_);
lean_ctor_set(v___x_2451_, 2, v___x_2450_);
v___x_2452_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___f_2441_, v___x_2451_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
return v___x_2452_;
}
}
}
else
{
lean_object* v_toCold_2471_; lean_object* v_inheritedTraceOptions_2472_; lean_object* v___x_2473_; 
lean_dec(v___x_2395_);
lean_dec(v_val_2394_);
lean_dec_ref(v_P_2372_);
lean_dec_ref(v_lhs_2367_);
v_toCold_2471_ = lean_ctor_get(v___y_2381_, 0);
v_inheritedTraceOptions_2472_ = lean_ctor_get(v_toCold_2471_, 11);
lean_inc(v___y_2382_);
lean_inc_ref(v___y_2381_);
lean_inc(v___y_2380_);
lean_inc_ref(v___y_2379_);
lean_inc(v___y_2378_);
lean_inc_ref(v___y_2377_);
lean_inc(v___y_2376_);
lean_inc_ref(v___y_2375_);
lean_inc(v___y_2374_);
lean_inc_ref(v_inheritedTraceOptions_2472_);
v___x_2473_ = lean_apply_11(v___f_2370_, v_inheritedTraceOptions_2472_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, lean_box(0));
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; uint8_t v___x_2475_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2474_);
lean_dec_ref_known(v___x_2473_, 1);
v___x_2475_ = lean_unbox(v_a_2474_);
lean_dec(v_a_2474_);
if (v___x_2475_ == 0)
{
lean_dec(v_cls_2371_);
lean_dec_ref(v_rhs_2368_);
goto v___jp_2387_;
}
else
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2476_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15);
v___x_2477_ = l_Lean_indentExpr(v_rhs_2368_);
v___x_2478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2476_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
v___x_2479_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2371_, v___x_2478_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_dec_ref_known(v___x_2479_, 1);
goto v___jp_2387_;
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2479_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2479_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
lean_dec(v_cls_2371_);
lean_dec_ref(v_rhs_2368_);
v_a_2488_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_2473_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2473_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
}
else
{
lean_object* v_toCold_2496_; lean_object* v_inheritedTraceOptions_2497_; lean_object* v___x_2498_; 
lean_dec(v___x_2393_);
lean_dec_ref(v_P_2372_);
lean_dec_ref(v_rhs_2368_);
v_toCold_2496_ = lean_ctor_get(v___y_2381_, 0);
v_inheritedTraceOptions_2497_ = lean_ctor_get(v_toCold_2496_, 11);
lean_inc(v___y_2382_);
lean_inc_ref(v___y_2381_);
lean_inc(v___y_2380_);
lean_inc_ref(v___y_2379_);
lean_inc(v___y_2378_);
lean_inc_ref(v___y_2377_);
lean_inc(v___y_2376_);
lean_inc_ref(v___y_2375_);
lean_inc(v___y_2374_);
lean_inc_ref(v_inheritedTraceOptions_2497_);
v___x_2498_ = lean_apply_11(v___f_2370_, v_inheritedTraceOptions_2497_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, lean_box(0));
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; uint8_t v___x_2500_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_a_2499_);
lean_dec_ref_known(v___x_2498_, 1);
v___x_2500_ = lean_unbox(v_a_2499_);
lean_dec(v_a_2499_);
if (v___x_2500_ == 0)
{
lean_dec(v_cls_2371_);
lean_dec_ref(v_lhs_2367_);
goto v___jp_2390_;
}
else
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2501_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15);
v___x_2502_ = l_Lean_indentExpr(v_lhs_2367_);
v___x_2503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2501_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2371_, v___x_2503_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_dec_ref_known(v___x_2504_, 1);
goto v___jp_2390_;
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2504_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec(v_cls_2371_);
lean_dec_ref(v_lhs_2367_);
v_a_2513_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2498_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2498_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
v___jp_2384_:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2385_, 0, v___x_2369_);
lean_ctor_set_uint8(v___x_2385_, 1, v___x_2369_);
v___x_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
return v___x_2386_;
}
v___jp_2387_:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2388_, 0, v___x_2369_);
lean_ctor_set_uint8(v___x_2388_, 1, v___x_2369_);
v___x_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
return v___x_2389_;
}
v___jp_2390_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2391_, 0, v___x_2369_);
lean_ctor_set_uint8(v___x_2391_, 1, v___x_2369_);
v___x_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
return v___x_2392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7___boxed(lean_object** _args){
lean_object* v_lhs_2521_ = _args[0];
lean_object* v_rhs_2522_ = _args[1];
lean_object* v___x_2523_ = _args[2];
lean_object* v___f_2524_ = _args[3];
lean_object* v_cls_2525_ = _args[4];
lean_object* v_P_2526_ = _args[5];
lean_object* v_____r_2527_ = _args[6];
lean_object* v___y_2528_ = _args[7];
lean_object* v___y_2529_ = _args[8];
lean_object* v___y_2530_ = _args[9];
lean_object* v___y_2531_ = _args[10];
lean_object* v___y_2532_ = _args[11];
lean_object* v___y_2533_ = _args[12];
lean_object* v___y_2534_ = _args[13];
lean_object* v___y_2535_ = _args[14];
lean_object* v___y_2536_ = _args[15];
lean_object* v___y_2537_ = _args[16];
_start:
{
uint8_t v___x_188797__boxed_2538_; lean_object* v_res_2539_; 
v___x_188797__boxed_2538_ = lean_unbox(v___x_2523_);
v_res_2539_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(v_lhs_2521_, v_rhs_2522_, v___x_188797__boxed_2538_, v___f_2524_, v_cls_2525_, v_P_2526_, v_____r_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
return v_res_2539_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(lean_object* v_e_2540_){
_start:
{
if (lean_obj_tag(v_e_2540_) == 0)
{
uint8_t v___x_2541_; 
v___x_2541_ = 2;
return v___x_2541_;
}
else
{
uint8_t v___x_2542_; 
v___x_2542_ = 0;
return v___x_2542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5___boxed(lean_object* v_e_2543_){
_start:
{
uint8_t v_res_2544_; lean_object* v_r_2545_; 
v_res_2544_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_e_2543_);
lean_dec_ref(v_e_2543_);
v_r_2545_ = lean_box(v_res_2544_);
return v_r_2545_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(lean_object* v_x_2546_){
_start:
{
if (lean_obj_tag(v_x_2546_) == 0)
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
v_a_2548_ = lean_ctor_get(v_x_2546_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_x_2546_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v_x_2546_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v_x_2546_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
lean_ctor_set_tag(v___x_2550_, 1);
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2548_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
v_a_2556_ = lean_ctor_get(v_x_2546_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_x_2546_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v_x_2546_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v_x_2546_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
lean_ctor_set_tag(v___x_2558_, 0);
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg___boxed(lean_object* v_x_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_2564_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(lean_object* v_opts_2567_, lean_object* v_opt_2568_){
_start:
{
lean_object* v_name_2569_; lean_object* v_defValue_2570_; lean_object* v_map_2571_; lean_object* v___x_2572_; 
v_name_2569_ = lean_ctor_get(v_opt_2568_, 0);
v_defValue_2570_ = lean_ctor_get(v_opt_2568_, 1);
v_map_2571_ = lean_ctor_get(v_opts_2567_, 0);
v___x_2572_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2571_, v_name_2569_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_inc(v_defValue_2570_);
return v_defValue_2570_;
}
else
{
lean_object* v_val_2573_; 
v_val_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_val_2573_);
lean_dec_ref_known(v___x_2572_, 1);
if (lean_obj_tag(v_val_2573_) == 3)
{
lean_object* v_v_2574_; 
v_v_2574_ = lean_ctor_get(v_val_2573_, 0);
lean_inc(v_v_2574_);
lean_dec_ref_known(v_val_2573_, 1);
return v_v_2574_;
}
else
{
lean_dec(v_val_2573_);
lean_inc(v_defValue_2570_);
return v_defValue_2570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6___boxed(lean_object* v_opts_2575_, lean_object* v_opt_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2575_, v_opt_2576_);
lean_dec_ref(v_opt_2576_);
lean_dec_ref(v_opts_2575_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(size_t v_sz_2578_, size_t v_i_2579_, lean_object* v_bs_2580_){
_start:
{
uint8_t v___x_2581_; 
v___x_2581_ = lean_usize_dec_lt(v_i_2579_, v_sz_2578_);
if (v___x_2581_ == 0)
{
return v_bs_2580_;
}
else
{
lean_object* v_v_2582_; lean_object* v_msg_2583_; lean_object* v___x_2584_; lean_object* v_bs_x27_2585_; size_t v___x_2586_; size_t v___x_2587_; lean_object* v___x_2588_; 
v_v_2582_ = lean_array_uget_borrowed(v_bs_2580_, v_i_2579_);
v_msg_2583_ = lean_ctor_get(v_v_2582_, 1);
lean_inc_ref(v_msg_2583_);
v___x_2584_ = lean_unsigned_to_nat(0u);
v_bs_x27_2585_ = lean_array_uset(v_bs_2580_, v_i_2579_, v___x_2584_);
v___x_2586_ = ((size_t)1ULL);
v___x_2587_ = lean_usize_add(v_i_2579_, v___x_2586_);
v___x_2588_ = lean_array_uset(v_bs_x27_2585_, v_i_2579_, v_msg_2583_);
v_i_2579_ = v___x_2587_;
v_bs_2580_ = v___x_2588_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2590_, lean_object* v_i_2591_, lean_object* v_bs_2592_){
_start:
{
size_t v_sz_boxed_2593_; size_t v_i_boxed_2594_; lean_object* v_res_2595_; 
v_sz_boxed_2593_ = lean_unbox_usize(v_sz_2590_);
lean_dec(v_sz_2590_);
v_i_boxed_2594_ = lean_unbox_usize(v_i_2591_);
lean_dec(v_i_2591_);
v_res_2595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_boxed_2593_, v_i_boxed_2594_, v_bs_2592_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(lean_object* v_oldTraces_2596_, lean_object* v_data_2597_, lean_object* v_ref_2598_, lean_object* v_msg_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_toCold_2605_; lean_object* v_currRecDepth_2606_; lean_object* v_ref_2607_; uint16_t v_optionFlags_2608_; uint8_t v_suppressElabErrors_2609_; uint8_t v_isRecordingDeps_2610_; lean_object* v_ref_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v_traceState_2614_; lean_object* v_traces_2615_; lean_object* v___x_2616_; size_t v_sz_2617_; size_t v___x_2618_; lean_object* v___x_2619_; lean_object* v_msg_2620_; lean_object* v___x_2621_; lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2660_; 
v_toCold_2605_ = lean_ctor_get(v___y_2602_, 0);
v_currRecDepth_2606_ = lean_ctor_get(v___y_2602_, 1);
v_ref_2607_ = lean_ctor_get(v___y_2602_, 2);
v_optionFlags_2608_ = lean_ctor_get_uint16(v___y_2602_, sizeof(void*)*3);
v_suppressElabErrors_2609_ = lean_ctor_get_uint8(v___y_2602_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2610_ = lean_ctor_get_uint8(v___y_2602_, sizeof(void*)*3 + 3);
v_ref_2611_ = l_Lean_replaceRef(v_ref_2598_, v_ref_2607_);
lean_inc(v_currRecDepth_2606_);
lean_inc_ref(v_toCold_2605_);
v___x_2612_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2612_, 0, v_toCold_2605_);
lean_ctor_set(v___x_2612_, 1, v_currRecDepth_2606_);
lean_ctor_set(v___x_2612_, 2, v_ref_2611_);
lean_ctor_set_uint16(v___x_2612_, sizeof(void*)*3, v_optionFlags_2608_);
lean_ctor_set_uint8(v___x_2612_, sizeof(void*)*3 + 2, v_suppressElabErrors_2609_);
lean_ctor_set_uint8(v___x_2612_, sizeof(void*)*3 + 3, v_isRecordingDeps_2610_);
v___x_2613_ = lean_st_ref_get(v___y_2603_);
v_traceState_2614_ = lean_ctor_get(v___x_2613_, 4);
lean_inc_ref(v_traceState_2614_);
lean_dec(v___x_2613_);
v_traces_2615_ = lean_ctor_get(v_traceState_2614_, 0);
lean_inc_ref(v_traces_2615_);
lean_dec_ref(v_traceState_2614_);
v___x_2616_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2615_);
lean_dec_ref(v_traces_2615_);
v_sz_2617_ = lean_array_size(v___x_2616_);
v___x_2618_ = ((size_t)0ULL);
v___x_2619_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_2617_, v___x_2618_, v___x_2616_);
v_msg_2620_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2620_, 0, v_data_2597_);
lean_ctor_set(v_msg_2620_, 1, v_msg_2599_);
lean_ctor_set(v_msg_2620_, 2, v___x_2619_);
v___x_2621_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2620_, v___y_2600_, v___y_2601_, v___x_2612_, v___y_2603_);
lean_dec_ref_known(v___x_2612_, 3);
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2624_ = v___x_2621_;
v_isShared_2625_ = v_isSharedCheck_2660_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2621_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2660_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2626_; lean_object* v_traceState_2627_; lean_object* v_env_2628_; lean_object* v_nextMacroScope_2629_; lean_object* v_ngen_2630_; lean_object* v_auxDeclNGen_2631_; lean_object* v_cache_2632_; lean_object* v_recordedDeps_2633_; lean_object* v_messages_2634_; lean_object* v_infoState_2635_; lean_object* v_snapshotTasks_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2659_; 
v___x_2626_ = lean_st_ref_take(v___y_2603_);
v_traceState_2627_ = lean_ctor_get(v___x_2626_, 4);
v_env_2628_ = lean_ctor_get(v___x_2626_, 0);
v_nextMacroScope_2629_ = lean_ctor_get(v___x_2626_, 1);
v_ngen_2630_ = lean_ctor_get(v___x_2626_, 2);
v_auxDeclNGen_2631_ = lean_ctor_get(v___x_2626_, 3);
v_cache_2632_ = lean_ctor_get(v___x_2626_, 5);
v_recordedDeps_2633_ = lean_ctor_get(v___x_2626_, 6);
v_messages_2634_ = lean_ctor_get(v___x_2626_, 7);
v_infoState_2635_ = lean_ctor_get(v___x_2626_, 8);
v_snapshotTasks_2636_ = lean_ctor_get(v___x_2626_, 9);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2638_ = v___x_2626_;
v_isShared_2639_ = v_isSharedCheck_2659_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_snapshotTasks_2636_);
lean_inc(v_infoState_2635_);
lean_inc(v_messages_2634_);
lean_inc(v_recordedDeps_2633_);
lean_inc(v_cache_2632_);
lean_inc(v_traceState_2627_);
lean_inc(v_auxDeclNGen_2631_);
lean_inc(v_ngen_2630_);
lean_inc(v_nextMacroScope_2629_);
lean_inc(v_env_2628_);
lean_dec(v___x_2626_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2659_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
uint64_t v_tid_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2657_; 
v_tid_2640_ = lean_ctor_get_uint64(v_traceState_2627_, sizeof(void*)*1);
v_isSharedCheck_2657_ = !lean_is_exclusive(v_traceState_2627_);
if (v_isSharedCheck_2657_ == 0)
{
lean_object* v_unused_2658_; 
v_unused_2658_ = lean_ctor_get(v_traceState_2627_, 0);
lean_dec(v_unused_2658_);
v___x_2642_ = v_traceState_2627_;
v_isShared_2643_ = v_isSharedCheck_2657_;
goto v_resetjp_2641_;
}
else
{
lean_dec(v_traceState_2627_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2657_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2648_; 
v___x_2644_ = lean_box(0);
v___x_2645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2645_, 0, v_ref_2598_);
lean_ctor_set(v___x_2645_, 1, v_a_2622_);
v___x_2646_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2596_, v___x_2645_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v___x_2646_);
v___x_2648_ = v___x_2642_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2646_);
lean_ctor_set_uint64(v_reuseFailAlloc_2656_, sizeof(void*)*1, v_tid_2640_);
v___x_2648_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
lean_object* v___x_2650_; 
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 4, v___x_2648_);
v___x_2650_ = v___x_2638_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_env_2628_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v_nextMacroScope_2629_);
lean_ctor_set(v_reuseFailAlloc_2655_, 2, v_ngen_2630_);
lean_ctor_set(v_reuseFailAlloc_2655_, 3, v_auxDeclNGen_2631_);
lean_ctor_set(v_reuseFailAlloc_2655_, 4, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2655_, 5, v_cache_2632_);
lean_ctor_set(v_reuseFailAlloc_2655_, 6, v_recordedDeps_2633_);
lean_ctor_set(v_reuseFailAlloc_2655_, 7, v_messages_2634_);
lean_ctor_set(v_reuseFailAlloc_2655_, 8, v_infoState_2635_);
lean_ctor_set(v_reuseFailAlloc_2655_, 9, v_snapshotTasks_2636_);
v___x_2650_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2651_; lean_object* v___x_2653_; 
v___x_2651_ = lean_st_ref_put(v___y_2603_, v___x_2650_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 0, v___x_2644_);
v___x_2653_ = v___x_2624_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2644_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_2661_, lean_object* v_data_2662_, lean_object* v_ref_2663_, lean_object* v_msg_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_2661_, v_data_2662_, v_ref_2663_, v_msg_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
return v_res_2670_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2672_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__0));
v___x_2673_ = l_Lean_stringToMessageData(v___x_2672_);
return v___x_2673_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2674_; double v___x_2675_; 
v___x_2674_ = lean_unsigned_to_nat(1000u);
v___x_2675_ = lean_float_of_nat(v___x_2674_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(lean_object* v_cls_2676_, uint8_t v_collapsed_2677_, lean_object* v_tag_2678_, lean_object* v_opts_2679_, uint8_t v_clsEnabled_2680_, lean_object* v_oldTraces_2681_, lean_object* v_msg_2682_, lean_object* v_resStartStop_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v_fst_2694_; lean_object* v_snd_2695_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v_data_2699_; lean_object* v_fst_2710_; lean_object* v_snd_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; lean_object* v___y_2715_; lean_object* v_a_2716_; uint8_t v___y_2731_; double v___y_2763_; 
v_fst_2694_ = lean_ctor_get(v_resStartStop_2683_, 0);
lean_inc(v_fst_2694_);
v_snd_2695_ = lean_ctor_get(v_resStartStop_2683_, 1);
lean_inc(v_snd_2695_);
lean_dec_ref(v_resStartStop_2683_);
v_fst_2710_ = lean_ctor_get(v_snd_2695_, 0);
lean_inc(v_fst_2710_);
v_snd_2711_ = lean_ctor_get(v_snd_2695_, 1);
lean_inc(v_snd_2711_);
lean_dec(v_snd_2695_);
v___x_2712_ = l_Lean_trace_profiler;
v___x_2713_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_2679_, v___x_2712_);
if (v___x_2713_ == 0)
{
v___y_2731_ = v___x_2713_;
goto v___jp_2730_;
}
else
{
lean_object* v___x_2768_; uint8_t v___x_2769_; 
v___x_2768_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2769_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_2679_, v___x_2768_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; lean_object* v___x_2771_; double v___x_2772_; double v___x_2773_; double v___x_2774_; 
v___x_2770_ = l_Lean_trace_profiler_threshold;
v___x_2771_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2679_, v___x_2770_);
v___x_2772_ = lean_float_of_nat(v___x_2771_);
v___x_2773_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2);
v___x_2774_ = lean_float_div(v___x_2772_, v___x_2773_);
v___y_2763_ = v___x_2774_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_2775_; lean_object* v___x_2776_; double v___x_2777_; 
v___x_2775_ = l_Lean_trace_profiler_threshold;
v___x_2776_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2679_, v___x_2775_);
v___x_2777_ = lean_float_of_nat(v___x_2776_);
v___y_2763_ = v___x_2777_;
goto v___jp_2762_;
}
}
v___jp_2696_:
{
lean_object* v___x_2700_; 
lean_inc(v___y_2698_);
v___x_2700_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_2681_, v_data_2699_, v___y_2698_, v___y_2697_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v___x_2701_; 
lean_dec_ref_known(v___x_2700_, 1);
v___x_2701_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_fst_2694_);
return v___x_2701_;
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_dec(v_fst_2694_);
v_a_2702_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2700_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2700_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_2714_:
{
uint8_t v_result_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; double v___x_2720_; lean_object* v_data_2721_; 
v_result_2717_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_fst_2694_);
v___x_2718_ = lean_box(v_result_2717_);
v___x_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
v___x_2720_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2678_);
lean_inc_ref(v___x_2719_);
lean_inc(v_cls_2676_);
v_data_2721_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2721_, 0, v_cls_2676_);
lean_ctor_set(v_data_2721_, 1, v___x_2719_);
lean_ctor_set(v_data_2721_, 2, v_tag_2678_);
lean_ctor_set_float(v_data_2721_, sizeof(void*)*3, v___x_2720_);
lean_ctor_set_float(v_data_2721_, sizeof(void*)*3 + 8, v___x_2720_);
lean_ctor_set_uint8(v_data_2721_, sizeof(void*)*3 + 16, v_collapsed_2677_);
if (v___x_2713_ == 0)
{
lean_dec_ref_known(v___x_2719_, 1);
lean_dec(v_snd_2711_);
lean_dec(v_fst_2710_);
lean_dec_ref(v_tag_2678_);
lean_dec(v_cls_2676_);
v___y_2697_ = v_a_2716_;
v___y_2698_ = v___y_2715_;
v_data_2699_ = v_data_2721_;
goto v___jp_2696_;
}
else
{
lean_object* v_data_2722_; double v___x_2723_; double v___x_2724_; 
lean_dec_ref_known(v_data_2721_, 3);
v_data_2722_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2722_, 0, v_cls_2676_);
lean_ctor_set(v_data_2722_, 1, v___x_2719_);
lean_ctor_set(v_data_2722_, 2, v_tag_2678_);
v___x_2723_ = lean_unbox_float(v_fst_2710_);
lean_dec(v_fst_2710_);
lean_ctor_set_float(v_data_2722_, sizeof(void*)*3, v___x_2723_);
v___x_2724_ = lean_unbox_float(v_snd_2711_);
lean_dec(v_snd_2711_);
lean_ctor_set_float(v_data_2722_, sizeof(void*)*3 + 8, v___x_2724_);
lean_ctor_set_uint8(v_data_2722_, sizeof(void*)*3 + 16, v_collapsed_2677_);
v___y_2697_ = v_a_2716_;
v___y_2698_ = v___y_2715_;
v_data_2699_ = v_data_2722_;
goto v___jp_2696_;
}
}
v___jp_2725_:
{
lean_object* v_ref_2726_; lean_object* v___x_2727_; 
v_ref_2726_ = lean_ctor_get(v___y_2691_, 2);
lean_inc(v___y_2692_);
lean_inc_ref(v___y_2691_);
lean_inc(v___y_2690_);
lean_inc_ref(v___y_2689_);
lean_inc(v___y_2688_);
lean_inc_ref(v___y_2687_);
lean_inc(v___y_2686_);
lean_inc_ref(v___y_2685_);
lean_inc(v___y_2684_);
lean_inc(v_fst_2694_);
v___x_2727_ = lean_apply_11(v_msg_2682_, v_fst_2694_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, lean_box(0));
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; 
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_a_2728_);
lean_dec_ref_known(v___x_2727_, 1);
v___y_2715_ = v_ref_2726_;
v_a_2716_ = v_a_2728_;
goto v___jp_2714_;
}
else
{
lean_object* v___x_2729_; 
lean_dec_ref_known(v___x_2727_, 1);
v___x_2729_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1);
v___y_2715_ = v_ref_2726_;
v_a_2716_ = v___x_2729_;
goto v___jp_2714_;
}
}
v___jp_2730_:
{
if (v_clsEnabled_2680_ == 0)
{
if (v___y_2731_ == 0)
{
lean_object* v___x_2732_; lean_object* v_traceState_2733_; lean_object* v_env_2734_; lean_object* v_nextMacroScope_2735_; lean_object* v_ngen_2736_; lean_object* v_auxDeclNGen_2737_; lean_object* v_cache_2738_; lean_object* v_recordedDeps_2739_; lean_object* v_messages_2740_; lean_object* v_infoState_2741_; lean_object* v_snapshotTasks_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2761_; 
lean_dec(v_snd_2711_);
lean_dec(v_fst_2710_);
lean_dec_ref(v_msg_2682_);
lean_dec_ref(v_tag_2678_);
lean_dec(v_cls_2676_);
v___x_2732_ = lean_st_ref_take(v___y_2692_);
v_traceState_2733_ = lean_ctor_get(v___x_2732_, 4);
v_env_2734_ = lean_ctor_get(v___x_2732_, 0);
v_nextMacroScope_2735_ = lean_ctor_get(v___x_2732_, 1);
v_ngen_2736_ = lean_ctor_get(v___x_2732_, 2);
v_auxDeclNGen_2737_ = lean_ctor_get(v___x_2732_, 3);
v_cache_2738_ = lean_ctor_get(v___x_2732_, 5);
v_recordedDeps_2739_ = lean_ctor_get(v___x_2732_, 6);
v_messages_2740_ = lean_ctor_get(v___x_2732_, 7);
v_infoState_2741_ = lean_ctor_get(v___x_2732_, 8);
v_snapshotTasks_2742_ = lean_ctor_get(v___x_2732_, 9);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2744_ = v___x_2732_;
v_isShared_2745_ = v_isSharedCheck_2761_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_snapshotTasks_2742_);
lean_inc(v_infoState_2741_);
lean_inc(v_messages_2740_);
lean_inc(v_recordedDeps_2739_);
lean_inc(v_cache_2738_);
lean_inc(v_traceState_2733_);
lean_inc(v_auxDeclNGen_2737_);
lean_inc(v_ngen_2736_);
lean_inc(v_nextMacroScope_2735_);
lean_inc(v_env_2734_);
lean_dec(v___x_2732_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2761_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
uint64_t v_tid_2746_; lean_object* v_traces_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2760_; 
v_tid_2746_ = lean_ctor_get_uint64(v_traceState_2733_, sizeof(void*)*1);
v_traces_2747_ = lean_ctor_get(v_traceState_2733_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v_traceState_2733_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2749_ = v_traceState_2733_;
v_isShared_2750_ = v_isSharedCheck_2760_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_traces_2747_);
lean_dec(v_traceState_2733_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2760_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2751_; lean_object* v___x_2753_; 
v___x_2751_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2681_, v_traces_2747_);
lean_dec_ref(v_traces_2747_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2751_);
v___x_2753_ = v___x_2749_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2751_);
lean_ctor_set_uint64(v_reuseFailAlloc_2759_, sizeof(void*)*1, v_tid_2746_);
v___x_2753_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
lean_object* v___x_2755_; 
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 4, v___x_2753_);
v___x_2755_ = v___x_2744_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_env_2734_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v_nextMacroScope_2735_);
lean_ctor_set(v_reuseFailAlloc_2758_, 2, v_ngen_2736_);
lean_ctor_set(v_reuseFailAlloc_2758_, 3, v_auxDeclNGen_2737_);
lean_ctor_set(v_reuseFailAlloc_2758_, 4, v___x_2753_);
lean_ctor_set(v_reuseFailAlloc_2758_, 5, v_cache_2738_);
lean_ctor_set(v_reuseFailAlloc_2758_, 6, v_recordedDeps_2739_);
lean_ctor_set(v_reuseFailAlloc_2758_, 7, v_messages_2740_);
lean_ctor_set(v_reuseFailAlloc_2758_, 8, v_infoState_2741_);
lean_ctor_set(v_reuseFailAlloc_2758_, 9, v_snapshotTasks_2742_);
v___x_2755_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2756_ = lean_st_ref_put(v___y_2692_, v___x_2755_);
v___x_2757_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_fst_2694_);
return v___x_2757_;
}
}
}
}
}
else
{
goto v___jp_2725_;
}
}
else
{
goto v___jp_2725_;
}
}
v___jp_2762_:
{
double v___x_2764_; double v___x_2765_; double v___x_2766_; uint8_t v___x_2767_; 
v___x_2764_ = lean_unbox_float(v_snd_2711_);
v___x_2765_ = lean_unbox_float(v_fst_2710_);
v___x_2766_ = lean_float_sub(v___x_2764_, v___x_2765_);
v___x_2767_ = lean_float_decLt(v___y_2763_, v___x_2766_);
v___y_2731_ = v___x_2767_;
goto v___jp_2730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___boxed(lean_object** _args){
lean_object* v_cls_2778_ = _args[0];
lean_object* v_collapsed_2779_ = _args[1];
lean_object* v_tag_2780_ = _args[2];
lean_object* v_opts_2781_ = _args[3];
lean_object* v_clsEnabled_2782_ = _args[4];
lean_object* v_oldTraces_2783_ = _args[5];
lean_object* v_msg_2784_ = _args[6];
lean_object* v_resStartStop_2785_ = _args[7];
lean_object* v___y_2786_ = _args[8];
lean_object* v___y_2787_ = _args[9];
lean_object* v___y_2788_ = _args[10];
lean_object* v___y_2789_ = _args[11];
lean_object* v___y_2790_ = _args[12];
lean_object* v___y_2791_ = _args[13];
lean_object* v___y_2792_ = _args[14];
lean_object* v___y_2793_ = _args[15];
lean_object* v___y_2794_ = _args[16];
lean_object* v___y_2795_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2796_; uint8_t v_clsEnabled_boxed_2797_; lean_object* v_res_2798_; 
v_collapsed_boxed_2796_ = lean_unbox(v_collapsed_2779_);
v_clsEnabled_boxed_2797_ = lean_unbox(v_clsEnabled_2782_);
v_res_2798_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_2778_, v_collapsed_boxed_2796_, v_tag_2780_, v_opts_2781_, v_clsEnabled_boxed_2797_, v_oldTraces_2783_, v_msg_2784_, v_resStartStop_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v_opts_2781_);
return v_res_2798_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2(void){
_start:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1));
v___x_2803_ = l_Lean_stringToMessageData(v___x_2802_);
return v___x_2803_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4(void){
_start:
{
lean_object* v___x_2805_; double v___x_2806_; 
v___x_2805_ = lean_unsigned_to_nat(1000000000u);
v___x_2806_ = lean_float_of_nat(v___x_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(lean_object* v_P_2807_, lean_object* v_lhs_2808_, lean_object* v_rhs_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_){
_start:
{
uint8_t v___y_2821_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v_toCold_2843_; lean_object* v_options_2844_; lean_object* v_inheritedTraceOptions_2845_; uint8_t v_hasTrace_2846_; lean_object* v_cls_2847_; lean_object* v___f_2848_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; uint8_t v_____do__lift_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; 
v_toCold_2843_ = lean_ctor_get(v_a_2817_, 0);
v_options_2844_ = lean_ctor_get(v_toCold_2843_, 2);
v_inheritedTraceOptions_2845_ = lean_ctor_get(v_toCold_2843_, 11);
v_hasTrace_2846_ = lean_ctor_get_uint8(v_options_2844_, sizeof(void*)*1);
v_cls_2847_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___f_2848_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
if (v_hasTrace_2846_ == 0)
{
lean_object* v___x_2976_; lean_object* v_a_2977_; uint8_t v___x_2978_; 
v___x_2976_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2847_, v_inheritedTraceOptions_2845_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
v_a_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc(v_a_2977_);
lean_dec_ref(v___x_2976_);
v___x_2978_ = lean_unbox(v_a_2977_);
lean_dec(v_a_2977_);
v_____do__lift_2953_ = v___x_2978_;
v___y_2954_ = v_a_2810_;
v___y_2955_ = v_a_2811_;
v___y_2956_ = v_a_2812_;
v___y_2957_ = v_a_2813_;
v___y_2958_ = v_a_2814_;
v___y_2959_ = v_a_2815_;
v___y_2960_ = v_a_2816_;
v___y_2961_ = v_a_2817_;
v___y_2962_ = v_a_2818_;
goto v___jp_2952_;
}
else
{
lean_object* v___f_2979_; uint8_t v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; uint8_t v___x_2983_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v_a_2987_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v_a_2999_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v_a_3017_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v_a_3032_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; 
v___f_2979_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3));
v___x_2980_ = 0;
v___x_2981_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_2982_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_2983_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2845_, v_options_2844_, v___x_2982_);
if (v___x_2983_ == 0)
{
lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3080_ = l_Lean_trace_profiler;
v___x_3081_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_2844_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; lean_object* v_a_3083_; uint8_t v___x_3084_; 
v___x_3082_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2847_, v_inheritedTraceOptions_2845_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3083_);
lean_dec_ref(v___x_3082_);
v___x_3084_ = lean_unbox(v_a_3083_);
lean_dec(v_a_3083_);
v_____do__lift_2953_ = v___x_3084_;
v___y_2954_ = v_a_2810_;
v___y_2955_ = v_a_2811_;
v___y_2956_ = v_a_2812_;
v___y_2957_ = v_a_2813_;
v___y_2958_ = v_a_2814_;
v___y_2959_ = v_a_2815_;
v___y_2960_ = v_a_2816_;
v___y_2961_ = v_a_2817_;
v___y_2962_ = v_a_2818_;
goto v___jp_2952_;
}
else
{
goto v___jp_3047_;
}
}
else
{
goto v___jp_3047_;
}
v___jp_2984_:
{
lean_object* v___x_2988_; double v___x_2989_; double v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2988_ = lean_io_get_num_heartbeats();
v___x_2989_ = lean_float_of_nat(v___y_2986_);
v___x_2990_ = lean_float_of_nat(v___x_2988_);
v___x_2991_ = lean_box_float(v___x_2989_);
v___x_2992_ = lean_box_float(v___x_2990_);
v___x_2993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2991_);
lean_ctor_set(v___x_2993_, 1, v___x_2992_);
v___x_2994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2994_, 0, v_a_2987_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
v___x_2995_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_2847_, v___x_2980_, v___x_2981_, v_options_2844_, v___x_2983_, v___y_2985_, v___f_2979_, v___x_2994_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
return v___x_2995_;
}
v___jp_2996_:
{
lean_object* v___x_3000_; 
v___x_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3000_, 0, v_a_2999_);
v___y_2985_ = v___y_2997_;
v___y_2986_ = v___y_2998_;
v_a_2987_ = v___x_3000_;
goto v___jp_2984_;
}
v___jp_3001_:
{
if (lean_obj_tag(v___y_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
v_a_3005_ = lean_ctor_get(v___y_3004_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___y_3004_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___y_3004_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___y_3004_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
lean_ctor_set_tag(v___x_3007_, 1);
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
v___y_2985_ = v___y_3002_;
v___y_2986_ = v___y_3003_;
v_a_2987_ = v___x_3010_;
goto v___jp_2984_;
}
}
}
else
{
lean_object* v_a_3013_; 
v_a_3013_ = lean_ctor_get(v___y_3004_, 0);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___y_3004_, 1);
v___y_2997_ = v___y_3002_;
v___y_2998_ = v___y_3003_;
v_a_2999_ = v_a_3013_;
goto v___jp_2996_;
}
}
v___jp_3014_:
{
lean_object* v___x_3018_; double v___x_3019_; double v___x_3020_; double v___x_3021_; double v___x_3022_; double v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3018_ = lean_io_mono_nanos_now();
v___x_3019_ = lean_float_of_nat(v___y_3016_);
v___x_3020_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4);
v___x_3021_ = lean_float_div(v___x_3019_, v___x_3020_);
v___x_3022_ = lean_float_of_nat(v___x_3018_);
v___x_3023_ = lean_float_div(v___x_3022_, v___x_3020_);
v___x_3024_ = lean_box_float(v___x_3021_);
v___x_3025_ = lean_box_float(v___x_3023_);
v___x_3026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3024_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
v___x_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3027_, 0, v_a_3017_);
lean_ctor_set(v___x_3027_, 1, v___x_3026_);
v___x_3028_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_2847_, v___x_2980_, v___x_2981_, v_options_2844_, v___x_2983_, v___y_3015_, v___f_2979_, v___x_3027_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
return v___x_3028_;
}
v___jp_3029_:
{
lean_object* v___x_3033_; 
v___x_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3033_, 0, v_a_3032_);
v___y_3015_ = v___y_3030_;
v___y_3016_ = v___y_3031_;
v_a_3017_ = v___x_3033_;
goto v___jp_3014_;
}
v___jp_3034_:
{
if (lean_obj_tag(v___y_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
v_a_3038_ = lean_ctor_get(v___y_3037_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___y_3037_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___y_3037_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___y_3037_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
lean_ctor_set_tag(v___x_3040_, 1);
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
v___y_3015_ = v___y_3035_;
v___y_3016_ = v___y_3036_;
v_a_3017_ = v___x_3043_;
goto v___jp_3014_;
}
}
}
else
{
lean_object* v_a_3046_; 
v_a_3046_ = lean_ctor_get(v___y_3037_, 0);
lean_inc(v_a_3046_);
lean_dec_ref_known(v___y_3037_, 1);
v___y_3030_ = v___y_3035_;
v___y_3031_ = v___y_3036_;
v_a_3032_ = v_a_3046_;
goto v___jp_3029_;
}
}
v___jp_3047_:
{
lean_object* v___x_3048_; lean_object* v_a_3049_; lean_object* v___x_3050_; uint8_t v___x_3051_; 
v___x_3048_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v_a_2818_);
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref(v___x_3048_);
v___x_3050_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3051_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_2844_, v___x_3050_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v_a_3054_; uint8_t v___x_3055_; 
v___x_3052_ = lean_io_mono_nanos_now();
v___x_3053_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2847_, v_inheritedTraceOptions_2845_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref(v___x_3053_);
v___x_3055_ = lean_unbox(v_a_3054_);
lean_dec(v_a_3054_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = lean_box(0);
v___x_3057_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(v_lhs_2808_, v_rhs_2809_, v___x_3051_, v___f_2848_, v_cls_2847_, v_P_2807_, v___x_3056_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
v___y_3035_ = v_a_3049_;
v___y_3036_ = v___x_3052_;
v___y_3037_ = v___x_3057_;
goto v___jp_3034_;
}
else
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3058_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2809_);
lean_inc_ref(v_lhs_2808_);
lean_inc_ref(v_P_2807_);
v___x_3059_ = l_Lean_mkAppB(v_P_2807_, v_lhs_2808_, v_rhs_2809_);
v___x_3060_ = l_Lean_indentExpr(v___x_3059_);
v___x_3061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3058_);
lean_ctor_set(v___x_3061_, 1, v___x_3060_);
v___x_3062_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2847_, v___x_3061_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v_a_3063_; lean_object* v___x_3064_; 
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_a_3063_);
lean_dec_ref_known(v___x_3062_, 1);
v___x_3064_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(v_lhs_2808_, v_rhs_2809_, v___x_3051_, v___f_2848_, v_cls_2847_, v_P_2807_, v_a_3063_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
v___y_3035_ = v_a_3049_;
v___y_3036_ = v___x_3052_;
v___y_3037_ = v___x_3064_;
goto v___jp_3034_;
}
else
{
lean_object* v_a_3065_; 
lean_dec_ref(v_rhs_2809_);
lean_dec_ref(v_lhs_2808_);
lean_dec_ref(v_P_2807_);
v_a_3065_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_a_3065_);
lean_dec_ref_known(v___x_3062_, 1);
v___y_3030_ = v_a_3049_;
v___y_3031_ = v___x_3052_;
v_a_3032_ = v_a_3065_;
goto v___jp_3029_;
}
}
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v_a_3068_; uint8_t v___x_3069_; 
v___x_3066_ = lean_io_get_num_heartbeats();
v___x_3067_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2847_, v_inheritedTraceOptions_2845_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref(v___x_3067_);
v___x_3069_ = lean_unbox(v_a_3068_);
lean_dec(v_a_3068_);
if (v___x_3069_ == 0)
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = lean_box(0);
v___x_3071_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2808_, v_rhs_2809_, v___f_2848_, v_cls_2847_, v_P_2807_, v___x_3070_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
v___y_3002_ = v_a_3049_;
v___y_3003_ = v___x_3066_;
v___y_3004_ = v___x_3071_;
goto v___jp_3001_;
}
else
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3072_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2809_);
lean_inc_ref(v_lhs_2808_);
lean_inc_ref(v_P_2807_);
v___x_3073_ = l_Lean_mkAppB(v_P_2807_, v_lhs_2808_, v_rhs_2809_);
v___x_3074_ = l_Lean_indentExpr(v___x_3073_);
v___x_3075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3072_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
v___x_3076_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2847_, v___x_3075_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_a_3077_; lean_object* v___x_3078_; 
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_a_3077_);
lean_dec_ref_known(v___x_3076_, 1);
v___x_3078_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2808_, v_rhs_2809_, v___f_2848_, v_cls_2847_, v_P_2807_, v_a_3077_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
v___y_3002_ = v_a_3049_;
v___y_3003_ = v___x_3066_;
v___y_3004_ = v___x_3078_;
goto v___jp_3001_;
}
else
{
lean_object* v_a_3079_; 
lean_dec_ref(v_rhs_2809_);
lean_dec_ref(v_lhs_2808_);
lean_dec_ref(v_P_2807_);
v_a_3079_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_a_3079_);
lean_dec_ref_known(v___x_3076_, 1);
v___y_2997_ = v_a_3049_;
v___y_2998_ = v___x_3066_;
v_a_2999_ = v_a_3079_;
goto v___jp_2996_;
}
}
}
}
}
v___jp_2820_:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2822_, 0, v___y_2821_);
lean_ctor_set_uint8(v___x_2822_, 1, v___y_2821_);
v___x_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
return v___x_2823_;
}
v___jp_2824_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
return v___x_2826_;
}
v___jp_2827_:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
return v___x_2829_;
}
v___jp_2830_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2839_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8);
v___x_2840_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9));
v___x_2841_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2841_, 0, v___y_2832_);
lean_ctor_set(v___x_2841_, 1, v___x_2839_);
lean_ctor_set(v___x_2841_, 2, v___x_2840_);
v___x_2842_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___y_2831_, v___x_2841_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
return v___x_2842_;
}
v___jp_2849_:
{
lean_object* v___x_2859_; 
lean_inc_ref(v_lhs_2808_);
v___x_2859_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2808_);
if (lean_obj_tag(v___x_2859_) == 1)
{
lean_object* v_val_2860_; lean_object* v___x_2861_; 
v_val_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_val_2860_);
lean_dec_ref_known(v___x_2859_, 1);
lean_inc_ref(v_rhs_2809_);
v___x_2861_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2809_);
if (lean_obj_tag(v___x_2861_) == 1)
{
lean_object* v_val_2862_; uint8_t v___x_2863_; 
v_val_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_val_2862_);
lean_dec_ref_known(v___x_2861_, 1);
v___x_2863_ = lean_expr_eqv(v_val_2860_, v_val_2862_);
if (v___x_2863_ == 0)
{
lean_object* v_toCold_2864_; lean_object* v_inheritedTraceOptions_2865_; lean_object* v___x_2866_; lean_object* v_a_2867_; uint8_t v___x_2868_; 
lean_dec_ref(v_P_2807_);
v_toCold_2864_ = lean_ctor_get(v___y_2857_, 0);
v_inheritedTraceOptions_2865_ = lean_ctor_get(v_toCold_2864_, 11);
v___x_2866_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2847_, v_inheritedTraceOptions_2865_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref(v___x_2866_);
v___x_2868_ = lean_unbox(v_a_2867_);
lean_dec(v_a_2867_);
if (v___x_2868_ == 0)
{
lean_dec(v_val_2862_);
lean_dec(v_val_2860_);
lean_dec_ref(v_rhs_2809_);
lean_dec_ref(v_lhs_2808_);
v___y_2821_ = v___x_2863_;
goto v___jp_2820_;
}
else
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2869_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2);
v___x_2870_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2860_);
v___x_2871_ = l_Lean_MessageData_ofExpr(v___x_2870_);
v___x_2872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2869_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4);
v___x_2874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2872_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___x_2875_ = l_Lean_indentExpr(v_lhs_2808_);
v___x_2876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2874_);
lean_ctor_set(v___x_2876_, 1, v___x_2875_);
v___x_2877_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6);
v___x_2878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2876_);
lean_ctor_set(v___x_2878_, 1, v___x_2877_);
v___x_2879_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2862_);
v___x_2880_ = l_Lean_MessageData_ofExpr(v___x_2879_);
v___x_2881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2878_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
lean_ctor_set(v___x_2882_, 1, v___x_2873_);
v___x_2883_ = l_Lean_indentExpr(v_rhs_2809_);
v___x_2884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2882_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
v___x_2885_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2847_, v___x_2884_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_dec_ref_known(v___x_2885_, 1);
v___y_2821_ = v___x_2863_;
goto v___jp_2820_;
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2885_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2885_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
}
else
{
lean_object* v_toCold_2894_; lean_object* v_options_2895_; lean_object* v_inheritedTraceOptions_2896_; uint8_t v_hasTrace_2897_; uint8_t v___x_2898_; lean_object* v___x_2899_; lean_object* v___f_2900_; 
lean_dec(v_val_2862_);
v_toCold_2894_ = lean_ctor_get(v___y_2857_, 0);
v_options_2895_ = lean_ctor_get(v_toCold_2894_, 2);
v_inheritedTraceOptions_2896_ = lean_ctor_get(v_toCold_2894_, 11);
v_hasTrace_2897_ = lean_ctor_get_uint8(v_options_2895_, sizeof(void*)*1);
v___x_2898_ = 0;
v___x_2899_ = lean_box(v___x_2898_);
lean_inc(v_val_2860_);
v___f_2900_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 13, 5);
lean_closure_set(v___f_2900_, 0, v_val_2860_);
lean_closure_set(v___f_2900_, 1, v_lhs_2808_);
lean_closure_set(v___f_2900_, 2, v_rhs_2809_);
lean_closure_set(v___f_2900_, 3, v_P_2807_);
lean_closure_set(v___f_2900_, 4, v___x_2899_);
if (v_hasTrace_2897_ == 0)
{
v___y_2831_ = v___f_2900_;
v___y_2832_ = v_val_2860_;
v___y_2833_ = v___y_2853_;
v___y_2834_ = v___y_2854_;
v___y_2835_ = v___y_2855_;
v___y_2836_ = v___y_2856_;
v___y_2837_ = v___y_2857_;
v___y_2838_ = v___y_2858_;
goto v___jp_2830_;
}
else
{
lean_object* v___x_2901_; uint8_t v___x_2902_; 
v___x_2901_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_2902_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2896_, v_options_2895_, v___x_2901_);
if (v___x_2902_ == 0)
{
v___y_2831_ = v___f_2900_;
v___y_2832_ = v_val_2860_;
v___y_2833_ = v___y_2853_;
v___y_2834_ = v___y_2854_;
v___y_2835_ = v___y_2855_;
v___y_2836_ = v___y_2856_;
v___y_2837_ = v___y_2857_;
v___y_2838_ = v___y_2858_;
goto v___jp_2830_;
}
else
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2903_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11);
lean_inc(v_val_2860_);
v___x_2904_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2860_);
v___x_2905_ = l_Lean_MessageData_ofExpr(v___x_2904_);
v___x_2906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2903_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13);
v___x_2908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2906_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
v___x_2909_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2847_, v___x_2908_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_dec_ref_known(v___x_2909_, 1);
v___y_2831_ = v___f_2900_;
v___y_2832_ = v_val_2860_;
v___y_2833_ = v___y_2853_;
v___y_2834_ = v___y_2854_;
v___y_2835_ = v___y_2855_;
v___y_2836_ = v___y_2856_;
v___y_2837_ = v___y_2857_;
v___y_2838_ = v___y_2858_;
goto v___jp_2830_;
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_dec_ref(v___f_2900_);
lean_dec(v_val_2860_);
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2909_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2909_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_2918_; lean_object* v_inheritedTraceOptions_2919_; lean_object* v___x_2920_; lean_object* v_a_2921_; uint8_t v___x_2922_; 
lean_dec(v___x_2861_);
lean_dec(v_val_2860_);
lean_dec_ref(v_lhs_2808_);
lean_dec_ref(v_P_2807_);
v_toCold_2918_ = lean_ctor_get(v___y_2857_, 0);
v_inheritedTraceOptions_2919_ = lean_ctor_get(v_toCold_2918_, 11);
v___x_2920_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2847_, v_inheritedTraceOptions_2919_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref(v___x_2920_);
v___x_2922_ = lean_unbox(v_a_2921_);
lean_dec(v_a_2921_);
if (v___x_2922_ == 0)
{
lean_dec_ref(v_rhs_2809_);
goto v___jp_2827_;
}
else
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2923_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15);
v___x_2924_ = l_Lean_indentExpr(v_rhs_2809_);
v___x_2925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2923_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
v___x_2926_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2847_, v___x_2925_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_dec_ref_known(v___x_2926_, 1);
goto v___jp_2827_;
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2926_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2926_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_2935_; lean_object* v_inheritedTraceOptions_2936_; lean_object* v___x_2937_; lean_object* v_a_2938_; uint8_t v___x_2939_; 
lean_dec(v___x_2859_);
lean_dec_ref(v_rhs_2809_);
lean_dec_ref(v_P_2807_);
v_toCold_2935_ = lean_ctor_get(v___y_2857_, 0);
v_inheritedTraceOptions_2936_ = lean_ctor_get(v_toCold_2935_, 11);
v___x_2937_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2847_, v_inheritedTraceOptions_2936_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2938_);
lean_dec_ref(v___x_2937_);
v___x_2939_ = lean_unbox(v_a_2938_);
lean_dec(v_a_2938_);
if (v___x_2939_ == 0)
{
lean_dec_ref(v_lhs_2808_);
goto v___jp_2824_;
}
else
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2940_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15);
v___x_2941_ = l_Lean_indentExpr(v_lhs_2808_);
v___x_2942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2940_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
v___x_2943_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2847_, v___x_2942_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_dec_ref_known(v___x_2943_, 1);
goto v___jp_2824_;
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2943_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2943_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
}
}
v___jp_2952_:
{
if (v_____do__lift_2953_ == 0)
{
v___y_2850_ = v___y_2954_;
v___y_2851_ = v___y_2955_;
v___y_2852_ = v___y_2956_;
v___y_2853_ = v___y_2957_;
v___y_2854_ = v___y_2958_;
v___y_2855_ = v___y_2959_;
v___y_2856_ = v___y_2960_;
v___y_2857_ = v___y_2961_;
v___y_2858_ = v___y_2962_;
goto v___jp_2849_;
}
else
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2963_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2809_);
lean_inc_ref(v_lhs_2808_);
lean_inc_ref(v_P_2807_);
v___x_2964_ = l_Lean_mkAppB(v_P_2807_, v_lhs_2808_, v_rhs_2809_);
v___x_2965_ = l_Lean_indentExpr(v___x_2964_);
v___x_2966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2963_);
lean_ctor_set(v___x_2966_, 1, v___x_2965_);
v___x_2967_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2847_, v___x_2966_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_dec_ref_known(v___x_2967_, 1);
v___y_2850_ = v___y_2954_;
v___y_2851_ = v___y_2955_;
v___y_2852_ = v___y_2956_;
v___y_2853_ = v___y_2957_;
v___y_2854_ = v___y_2958_;
v___y_2855_ = v___y_2959_;
v___y_2856_ = v___y_2960_;
v___y_2857_ = v___y_2961_;
v___y_2858_ = v___y_2962_;
goto v___jp_2849_;
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
lean_dec_ref(v_rhs_2809_);
lean_dec_ref(v_lhs_2808_);
lean_dec_ref(v_P_2807_);
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2967_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2967_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___boxed(lean_object* v_P_3085_, lean_object* v_lhs_3086_, lean_object* v_rhs_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v_P_3085_, v_lhs_3086_, v_rhs_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_);
lean_dec(v_a_3096_);
lean_dec_ref(v_a_3095_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
lean_dec(v_a_3092_);
lean_dec_ref(v_a_3091_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(lean_object* v_cls_3099_, lean_object* v_msg_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v___x_3111_; 
v___x_3111_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3099_, v_msg_3100_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object* v_cls_3112_, lean_object* v_msg_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(v_cls_3112_, v_msg_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3114_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(lean_object* v_00_u03b1_3125_, lean_object* v_x_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_3126_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___boxed(lean_object* v_00_u03b1_3138_, lean_object* v_x_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(v_00_u03b1_3138_, v_x_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(lean_object* v_oldTraces_3151_, lean_object* v_data_3152_, lean_object* v_ref_3153_, lean_object* v_msg_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v___x_3165_; 
v___x_3165_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_3151_, v_data_3152_, v_ref_3153_, v_msg_3154_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___boxed(lean_object* v_oldTraces_3166_, lean_object* v_data_3167_, lean_object* v_ref_3168_, lean_object* v_msg_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v_res_3180_; 
v_res_3180_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(v_oldTraces_3166_, v_data_3167_, v_ref_3168_, v_msg_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(lean_object* v_x_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3192_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_3193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3192_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0___boxed(lean_object* v_x_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v_x_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(lean_object* v_arg_3211_, lean_object* v_arg_3212_, lean_object* v_arg_3213_, lean_object* v_arg_3214_, lean_object* v_____r_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v___x_3226_; 
lean_inc_ref(v_arg_3211_);
v___x_3226_ = l_Lean_Meta_getDecLevel(v_arg_3211_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_a_3227_);
lean_dec_ref_known(v___x_3226_, 1);
v___x_3228_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2));
v___x_3229_ = lean_box(0);
v___x_3230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3230_, 0, v_a_3227_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
v___x_3231_ = l_Lean_Expr_const___override(v___x_3228_, v___x_3230_);
v___x_3232_ = l_Lean_mkAppB(v___x_3231_, v_arg_3211_, v_arg_3212_);
v___x_3233_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3232_, v_arg_3213_, v_arg_3214_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
return v___x_3233_;
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec_ref(v_arg_3214_);
lean_dec_ref(v_arg_3213_);
lean_dec_ref(v_arg_3212_);
lean_dec_ref(v_arg_3211_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___boxed(lean_object* v_arg_3242_, lean_object* v_arg_3243_, lean_object* v_arg_3244_, lean_object* v_arg_3245_, lean_object* v_____r_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3242_, v_arg_3243_, v_arg_3244_, v_arg_3245_, v_____r_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(lean_object* v_arg_3261_, lean_object* v_arg_3262_, lean_object* v_arg_3263_, lean_object* v_____r_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v___x_3275_; 
lean_inc_ref(v_arg_3261_);
v___x_3275_ = l_Lean_Meta_getLevel(v_arg_3261_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v_a_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
lean_inc(v_a_3276_);
lean_dec_ref_known(v___x_3275_, 1);
v___x_3277_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1));
v___x_3278_ = lean_box(0);
v___x_3279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3279_, 0, v_a_3276_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
v___x_3280_ = l_Lean_Expr_const___override(v___x_3277_, v___x_3279_);
v___x_3281_ = l_Lean_Expr_app___override(v___x_3280_, v_arg_3261_);
v___x_3282_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3281_, v_arg_3262_, v_arg_3263_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
return v___x_3282_;
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec_ref(v_arg_3263_);
lean_dec_ref(v_arg_3262_);
lean_dec_ref(v_arg_3261_);
v_a_3283_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3275_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3275_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___boxed(lean_object* v_arg_3291_, lean_object* v_arg_3292_, lean_object* v_arg_3293_, lean_object* v_____r_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3291_, v_arg_3292_, v_arg_3293_, v_____r_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
return v_res_3305_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1(void){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3307_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0));
v___x_3308_ = l_Lean_stringToMessageData(v___x_3307_);
return v___x_3308_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2(void){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = l_Lean_checkEmoji;
v___x_3310_ = l_Lean_stringToMessageData(v___x_3309_);
return v___x_3310_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3(void){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3311_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2);
v___x_3312_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1);
v___x_3313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
lean_ctor_set(v___x_3313_, 1, v___x_3311_);
return v___x_3313_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5(void){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3315_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4));
v___x_3316_ = l_Lean_stringToMessageData(v___x_3315_);
return v___x_3316_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6(void){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3317_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5);
v___x_3318_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3);
v___x_3319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3318_);
lean_ctor_set(v___x_3319_, 1, v___x_3317_);
return v___x_3319_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7));
v___x_3322_ = l_Lean_stringToMessageData(v___x_3321_);
return v___x_3322_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9(void){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3323_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8);
v___x_3324_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3);
v___x_3325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
lean_ctor_set(v___x_3325_, 1, v___x_3323_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(lean_object* v_e_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_){
_start:
{
lean_object* v___y_3338_; lean_object* v___x_3370_; 
v___x_3370_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3326_, v_a_3333_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_a_3371_);
lean_dec_ref_known(v___x_3370_, 1);
v___x_3372_ = l_Lean_Expr_cleanupAnnotations(v_a_3371_);
v___x_3373_ = l_Lean_Expr_isApp(v___x_3372_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
lean_dec_ref(v___x_3372_);
v___x_3374_ = lean_box(0);
v___x_3375_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3374_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
v___y_3338_ = v___x_3375_;
goto v___jp_3337_;
}
else
{
lean_object* v_arg_3376_; lean_object* v___x_3377_; uint8_t v___x_3378_; 
v_arg_3376_ = lean_ctor_get(v___x_3372_, 1);
lean_inc_ref(v_arg_3376_);
v___x_3377_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3372_);
v___x_3378_ = l_Lean_Expr_isApp(v___x_3377_);
if (v___x_3378_ == 0)
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
lean_dec_ref(v___x_3377_);
lean_dec_ref(v_arg_3376_);
v___x_3379_ = lean_box(0);
v___x_3380_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3379_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
v___y_3338_ = v___x_3380_;
goto v___jp_3337_;
}
else
{
lean_object* v_arg_3381_; lean_object* v___x_3382_; uint8_t v___x_3383_; 
v_arg_3381_ = lean_ctor_get(v___x_3377_, 1);
lean_inc_ref(v_arg_3381_);
v___x_3382_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3377_);
v___x_3383_ = l_Lean_Expr_isApp(v___x_3382_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
lean_dec_ref(v___x_3382_);
lean_dec_ref(v_arg_3381_);
lean_dec_ref(v_arg_3376_);
v___x_3384_ = lean_box(0);
v___x_3385_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3384_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
v___y_3338_ = v___x_3385_;
goto v___jp_3337_;
}
else
{
lean_object* v_arg_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; uint8_t v___x_3389_; 
v_arg_3386_ = lean_ctor_get(v___x_3382_, 1);
lean_inc_ref(v_arg_3386_);
v___x_3387_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3382_);
v___x_3388_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1));
v___x_3389_ = l_Lean_Expr_isConstOf(v___x_3387_, v___x_3388_);
if (v___x_3389_ == 0)
{
uint8_t v___x_3390_; 
v___x_3390_ = l_Lean_Expr_isApp(v___x_3387_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
lean_dec_ref(v___x_3387_);
lean_dec_ref(v_arg_3386_);
lean_dec_ref(v_arg_3381_);
lean_dec_ref(v_arg_3376_);
v___x_3391_ = lean_box(0);
v___x_3392_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3391_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
v___y_3338_ = v___x_3392_;
goto v___jp_3337_;
}
else
{
lean_object* v_arg_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; uint8_t v___x_3396_; 
v_arg_3393_ = lean_ctor_get(v___x_3387_, 1);
lean_inc_ref(v_arg_3393_);
v___x_3394_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3387_);
v___x_3395_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2));
v___x_3396_ = l_Lean_Expr_isConstOf(v___x_3394_, v___x_3395_);
lean_dec_ref(v___x_3394_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
lean_dec_ref(v_arg_3393_);
lean_dec_ref(v_arg_3386_);
lean_dec_ref(v_arg_3381_);
lean_dec_ref(v_arg_3376_);
v___x_3397_ = lean_box(0);
v___x_3398_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3397_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
v___y_3338_ = v___x_3398_;
goto v___jp_3337_;
}
else
{
lean_object* v_toCold_3399_; lean_object* v_options_3400_; lean_object* v_inheritedTraceOptions_3401_; uint8_t v_hasTrace_3402_; 
v_toCold_3399_ = lean_ctor_get(v_a_3334_, 0);
v_options_3400_ = lean_ctor_get(v_toCold_3399_, 2);
v_inheritedTraceOptions_3401_ = lean_ctor_get(v_toCold_3399_, 11);
v_hasTrace_3402_ = lean_ctor_get_uint8(v_options_3400_, sizeof(void*)*1);
if (v_hasTrace_3402_ == 0)
{
goto v___jp_3403_;
}
else
{
lean_object* v___x_3406_; lean_object* v___x_3407_; uint8_t v___x_3408_; 
v___x_3406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3407_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3408_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3401_, v_options_3400_, v___x_3407_);
if (v___x_3408_ == 0)
{
goto v___jp_3403_;
}
else
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6);
v___x_3410_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3406_, v___x_3409_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; lean_object* v___x_3412_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_a_3411_);
lean_dec_ref_known(v___x_3410_, 1);
v___x_3412_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3393_, v_arg_3386_, v_arg_3381_, v_arg_3376_, v_a_3411_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
v___y_3338_ = v___x_3412_;
goto v___jp_3337_;
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_dec_ref(v_arg_3393_);
lean_dec_ref(v_arg_3386_);
lean_dec_ref(v_arg_3381_);
lean_dec_ref(v_arg_3376_);
v_a_3413_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3410_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3410_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
}
v___jp_3403_:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3404_ = lean_box(0);
v___x_3405_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3393_, v_arg_3386_, v_arg_3381_, v_arg_3376_, v___x_3404_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
v___y_3338_ = v___x_3405_;
goto v___jp_3337_;
}
}
}
}
else
{
lean_object* v_toCold_3421_; lean_object* v_options_3422_; lean_object* v_inheritedTraceOptions_3423_; uint8_t v_hasTrace_3424_; 
lean_dec_ref(v___x_3387_);
v_toCold_3421_ = lean_ctor_get(v_a_3334_, 0);
v_options_3422_ = lean_ctor_get(v_toCold_3421_, 2);
v_inheritedTraceOptions_3423_ = lean_ctor_get(v_toCold_3421_, 11);
v_hasTrace_3424_ = lean_ctor_get_uint8(v_options_3422_, sizeof(void*)*1);
if (v_hasTrace_3424_ == 0)
{
goto v___jp_3425_;
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; 
v___x_3428_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3429_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3430_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3423_, v_options_3422_, v___x_3429_);
if (v___x_3430_ == 0)
{
goto v___jp_3425_;
}
else
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3431_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9);
v___x_3432_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3428_, v___x_3431_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___x_3434_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc(v_a_3433_);
lean_dec_ref_known(v___x_3432_, 1);
v___x_3434_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3386_, v_arg_3381_, v_arg_3376_, v_a_3433_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
v___y_3338_ = v___x_3434_;
goto v___jp_3337_;
}
else
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
lean_dec_ref(v_arg_3386_);
lean_dec_ref(v_arg_3381_);
lean_dec_ref(v_arg_3376_);
v_a_3435_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3432_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3432_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
}
v___jp_3425_:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3426_ = lean_box(0);
v___x_3427_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3386_, v_arg_3381_, v_arg_3376_, v___x_3426_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
v___y_3338_ = v___x_3427_;
goto v___jp_3337_;
}
}
}
}
}
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
v_a_3443_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v___x_3370_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3370_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
v___jp_3337_:
{
if (lean_obj_tag(v___y_3338_) == 0)
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3369_; 
v_a_3339_ = lean_ctor_get(v___y_3338_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___y_3338_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3341_ = v___y_3338_;
v_isShared_3342_ = v_isSharedCheck_3369_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___y_3338_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3369_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
if (lean_obj_tag(v_a_3339_) == 0)
{
uint8_t v_contextDependent_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3354_; 
v_contextDependent_3343_ = lean_ctor_get_uint8(v_a_3339_, 1);
v_isSharedCheck_3354_ = !lean_is_exclusive(v_a_3339_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3345_ = v_a_3339_;
v_isShared_3346_ = v_isSharedCheck_3354_;
goto v_resetjp_3344_;
}
else
{
lean_dec(v_a_3339_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3354_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
uint8_t v___x_3347_; lean_object* v___x_3349_; 
v___x_3347_ = 1;
if (v_isShared_3346_ == 0)
{
v___x_3349_ = v___x_3345_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_3353_, 1, v_contextDependent_3343_);
v___x_3349_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
lean_object* v___x_3351_; 
lean_ctor_set_uint8(v___x_3349_, 0, v___x_3347_);
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 0, v___x_3349_);
v___x_3351_ = v___x_3341_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3349_);
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
else
{
lean_object* v_e_x27_3355_; lean_object* v_proof_3356_; uint8_t v_contextDependent_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3368_; 
v_e_x27_3355_ = lean_ctor_get(v_a_3339_, 0);
v_proof_3356_ = lean_ctor_get(v_a_3339_, 1);
v_contextDependent_3357_ = lean_ctor_get_uint8(v_a_3339_, sizeof(void*)*2 + 1);
v_isSharedCheck_3368_ = !lean_is_exclusive(v_a_3339_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3359_ = v_a_3339_;
v_isShared_3360_ = v_isSharedCheck_3368_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_proof_3356_);
lean_inc(v_e_x27_3355_);
lean_dec(v_a_3339_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3368_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
uint8_t v___x_3361_; lean_object* v___x_3363_; 
v___x_3361_ = 1;
if (v_isShared_3360_ == 0)
{
v___x_3363_ = v___x_3359_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_e_x27_3355_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_proof_3356_);
lean_ctor_set_uint8(v_reuseFailAlloc_3367_, sizeof(void*)*2 + 1, v_contextDependent_3357_);
v___x_3363_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3365_; 
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*2, v___x_3361_);
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 0, v___x_3363_);
v___x_3365_ = v___x_3341_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3363_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
}
}
}
else
{
return v___y_3338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed(lean_object* v_e_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(v_e_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
lean_dec(v_a_3460_);
lean_dec_ref(v_a_3459_);
lean_dec(v_a_3458_);
lean_dec_ref(v_a_3457_);
lean_dec(v_a_3456_);
lean_dec_ref(v_a_3455_);
lean_dec(v_a_3454_);
lean_dec_ref(v_a_3453_);
lean_dec(v_a_3452_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(lean_object* v_x_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
lean_object* v___x_3476_; 
lean_inc(v___y_3470_);
lean_inc_ref(v___y_3469_);
lean_inc(v___y_3468_);
lean_inc_ref(v___y_3467_);
lean_inc(v___y_3466_);
lean_inc(v___y_3465_);
lean_inc_ref(v___y_3464_);
v___x_3476_ = lean_apply_12(v_x_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, lean_box(0));
return v___x_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed(lean_object* v_x_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(v_x_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object* v_mvarId_3491_, lean_object* v_x_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
lean_object* v___f_3505_; lean_object* v___x_3506_; 
lean_inc(v___y_3499_);
lean_inc_ref(v___y_3498_);
lean_inc(v___y_3497_);
lean_inc_ref(v___y_3496_);
lean_inc(v___y_3495_);
lean_inc(v___y_3494_);
lean_inc_ref(v___y_3493_);
v___f_3505_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_3505_, 0, v_x_3492_);
lean_closure_set(v___f_3505_, 1, v___y_3493_);
lean_closure_set(v___f_3505_, 2, v___y_3494_);
lean_closure_set(v___f_3505_, 3, v___y_3495_);
lean_closure_set(v___f_3505_, 4, v___y_3496_);
lean_closure_set(v___f_3505_, 5, v___y_3497_);
lean_closure_set(v___f_3505_, 6, v___y_3498_);
lean_closure_set(v___f_3505_, 7, v___y_3499_);
v___x_3506_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3491_, v___f_3505_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
if (lean_obj_tag(v___x_3506_) == 0)
{
return v___x_3506_;
}
else
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3514_; 
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3509_ = v___x_3506_;
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3506_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object* v_mvarId_3515_, lean_object* v_x_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_mvarId_3515_, v_x_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(lean_object* v_00_u03b1_3530_, lean_object* v_mvarId_3531_, lean_object* v_x_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_mvarId_3531_, v_x_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object* v_00_u03b1_3546_, lean_object* v_mvarId_3547_, lean_object* v_x_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(v_00_u03b1_3546_, v_mvarId_3547_, v_x_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0(lean_object* v_x_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3573_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0___boxed(lean_object* v_x_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0(v_x_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v_x_3575_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(lean_object* v_snd_3587_, lean_object* v_a_3588_, lean_object* v___x_3589_, lean_object* v_____r_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3603_ = lean_array_push(v_snd_3587_, v_a_3588_);
v___x_3604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3589_);
lean_ctor_set(v___x_3604_, 1, v___x_3603_);
v___x_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3604_);
v___x_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1___boxed(lean_object* v_snd_3607_, lean_object* v_a_3608_, lean_object* v___x_3609_, lean_object* v_____r_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(v_snd_3607_, v_a_3608_, v___x_3609_, v_____r_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object* v_cls_3624_, lean_object* v_msg_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
lean_object* v_ref_3631_; lean_object* v___x_3632_; lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3678_; 
v_ref_3631_ = lean_ctor_get(v___y_3628_, 2);
v___x_3632_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3635_ = v___x_3632_;
v_isShared_3636_ = v_isSharedCheck_3678_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3632_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3678_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3637_; lean_object* v_traceState_3638_; lean_object* v_env_3639_; lean_object* v_nextMacroScope_3640_; lean_object* v_ngen_3641_; lean_object* v_auxDeclNGen_3642_; lean_object* v_cache_3643_; lean_object* v_recordedDeps_3644_; lean_object* v_messages_3645_; lean_object* v_infoState_3646_; lean_object* v_snapshotTasks_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3677_; 
v___x_3637_ = lean_st_ref_take(v___y_3629_);
v_traceState_3638_ = lean_ctor_get(v___x_3637_, 4);
v_env_3639_ = lean_ctor_get(v___x_3637_, 0);
v_nextMacroScope_3640_ = lean_ctor_get(v___x_3637_, 1);
v_ngen_3641_ = lean_ctor_get(v___x_3637_, 2);
v_auxDeclNGen_3642_ = lean_ctor_get(v___x_3637_, 3);
v_cache_3643_ = lean_ctor_get(v___x_3637_, 5);
v_recordedDeps_3644_ = lean_ctor_get(v___x_3637_, 6);
v_messages_3645_ = lean_ctor_get(v___x_3637_, 7);
v_infoState_3646_ = lean_ctor_get(v___x_3637_, 8);
v_snapshotTasks_3647_ = lean_ctor_get(v___x_3637_, 9);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3649_ = v___x_3637_;
v_isShared_3650_ = v_isSharedCheck_3677_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_snapshotTasks_3647_);
lean_inc(v_infoState_3646_);
lean_inc(v_messages_3645_);
lean_inc(v_recordedDeps_3644_);
lean_inc(v_cache_3643_);
lean_inc(v_traceState_3638_);
lean_inc(v_auxDeclNGen_3642_);
lean_inc(v_ngen_3641_);
lean_inc(v_nextMacroScope_3640_);
lean_inc(v_env_3639_);
lean_dec(v___x_3637_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3677_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
uint64_t v_tid_3651_; lean_object* v_traces_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3676_; 
v_tid_3651_ = lean_ctor_get_uint64(v_traceState_3638_, sizeof(void*)*1);
v_traces_3652_ = lean_ctor_get(v_traceState_3638_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v_traceState_3638_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3654_ = v_traceState_3638_;
v_isShared_3655_ = v_isSharedCheck_3676_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_traces_3652_);
lean_dec(v_traceState_3638_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3676_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; double v___x_3658_; uint8_t v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3667_; 
v___x_3656_ = lean_box(0);
v___x_3657_ = lean_box(0);
v___x_3658_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_3659_ = 0;
v___x_3660_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_3661_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3661_, 0, v_cls_3624_);
lean_ctor_set(v___x_3661_, 1, v___x_3657_);
lean_ctor_set(v___x_3661_, 2, v___x_3660_);
lean_ctor_set_float(v___x_3661_, sizeof(void*)*3, v___x_3658_);
lean_ctor_set_float(v___x_3661_, sizeof(void*)*3 + 8, v___x_3658_);
lean_ctor_set_uint8(v___x_3661_, sizeof(void*)*3 + 16, v___x_3659_);
v___x_3662_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_3663_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3661_);
lean_ctor_set(v___x_3663_, 1, v_a_3633_);
lean_ctor_set(v___x_3663_, 2, v___x_3662_);
lean_inc(v_ref_3631_);
v___x_3664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3664_, 0, v_ref_3631_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
v___x_3665_ = l_Lean_PersistentArray_push___redArg(v_traces_3652_, v___x_3664_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 0, v___x_3665_);
v___x_3667_ = v___x_3654_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3665_);
lean_ctor_set_uint64(v_reuseFailAlloc_3675_, sizeof(void*)*1, v_tid_3651_);
v___x_3667_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
lean_object* v___x_3669_; 
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 4, v___x_3667_);
v___x_3669_ = v___x_3649_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_env_3639_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v_nextMacroScope_3640_);
lean_ctor_set(v_reuseFailAlloc_3674_, 2, v_ngen_3641_);
lean_ctor_set(v_reuseFailAlloc_3674_, 3, v_auxDeclNGen_3642_);
lean_ctor_set(v_reuseFailAlloc_3674_, 4, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3674_, 5, v_cache_3643_);
lean_ctor_set(v_reuseFailAlloc_3674_, 6, v_recordedDeps_3644_);
lean_ctor_set(v_reuseFailAlloc_3674_, 7, v_messages_3645_);
lean_ctor_set(v_reuseFailAlloc_3674_, 8, v_infoState_3646_);
lean_ctor_set(v_reuseFailAlloc_3674_, 9, v_snapshotTasks_3647_);
v___x_3669_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
lean_object* v___x_3670_; lean_object* v___x_3672_; 
v___x_3670_ = lean_st_ref_put(v___y_3629_, v___x_3669_);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 0, v___x_3656_);
v___x_3672_ = v___x_3635_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3656_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object* v_cls_3679_, lean_object* v_msg_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_cls_3679_, v_msg_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_);
lean_dec(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec(v___y_3682_);
lean_dec_ref(v___y_3681_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(uint8_t v___x_3687_, lean_object* v___f_3688_, lean_object* v_____r_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v___x_3702_; lean_object* v_caches_3703_; lean_object* v_typeAnalysis_3704_; lean_object* v_target_3705_; lean_object* v_hypotheses_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3716_; 
v___x_3702_ = lean_st_ref_take(v___y_3691_);
v_caches_3703_ = lean_ctor_get(v___x_3702_, 0);
v_typeAnalysis_3704_ = lean_ctor_get(v___x_3702_, 1);
v_target_3705_ = lean_ctor_get(v___x_3702_, 2);
v_hypotheses_3706_ = lean_ctor_get(v___x_3702_, 3);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3708_ = v___x_3702_;
v_isShared_3709_ = v_isSharedCheck_3716_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_hypotheses_3706_);
lean_inc(v_target_3705_);
lean_inc(v_typeAnalysis_3704_);
lean_inc(v_caches_3703_);
lean_dec(v___x_3702_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3716_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3710_; lean_object* v___x_3712_; 
v___x_3710_ = lean_box(0);
if (v_isShared_3709_ == 0)
{
v___x_3712_ = v___x_3708_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_caches_3703_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_typeAnalysis_3704_);
lean_ctor_set(v_reuseFailAlloc_3715_, 2, v_target_3705_);
lean_ctor_set(v_reuseFailAlloc_3715_, 3, v_hypotheses_3706_);
v___x_3712_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; 
lean_ctor_set_uint8(v___x_3712_, sizeof(void*)*4, v___x_3687_);
v___x_3713_ = lean_st_ref_put(v___y_3691_, v___x_3712_);
lean_inc(v___y_3700_);
lean_inc_ref(v___y_3699_);
lean_inc(v___y_3698_);
lean_inc_ref(v___y_3697_);
lean_inc(v___y_3696_);
lean_inc_ref(v___y_3695_);
lean_inc(v___y_3694_);
lean_inc_ref(v___y_3693_);
lean_inc(v___y_3692_);
lean_inc(v___y_3691_);
lean_inc_ref(v___y_3690_);
v___x_3714_ = lean_apply_13(v___f_3688_, v___x_3710_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, lean_box(0));
return v___x_3714_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2___boxed(lean_object* v___x_3717_, lean_object* v___f_3718_, lean_object* v_____r_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
uint8_t v___x_10092__boxed_3732_; lean_object* v_res_3733_; 
v___x_10092__boxed_3732_ = lean_unbox(v___x_3717_);
v_res_3733_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_10092__boxed_3732_, v___f_3718_, v_____r_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
lean_dec(v___y_3730_);
lean_dec_ref(v___y_3729_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_dec(v___y_3722_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
return v_res_3733_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3735_; lean_object* v___f_3736_; lean_object* v_methods_3737_; 
v___x_3735_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed), 11, 0);
v___f_3736_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__0));
v_methods_3737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_methods_3737_, 0, v___f_3736_);
lean_ctor_set(v_methods_3737_, 1, v___x_3735_);
return v_methods_3737_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3739_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__2));
v___x_3740_ = l_Lean_stringToMessageData(v___x_3739_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object* v_upperBound_3741_, lean_object* v___x_3742_, lean_object* v_config_3743_, lean_object* v_a_3744_, lean_object* v_b_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v___y_3759_; uint8_t v___x_3781_; 
v___x_3781_ = lean_nat_dec_lt(v_a_3744_, v_upperBound_3741_);
if (v___x_3781_ == 0)
{
lean_object* v___x_3782_; 
lean_dec(v_a_3744_);
lean_dec_ref(v_config_3743_);
v___x_3782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3782_, 0, v_b_3745_);
return v___x_3782_;
}
else
{
lean_object* v_snd_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3857_; 
v_snd_3783_ = lean_ctor_get(v_b_3745_, 1);
v_isSharedCheck_3857_ = !lean_is_exclusive(v_b_3745_);
if (v_isSharedCheck_3857_ == 0)
{
lean_object* v_unused_3858_; 
v_unused_3858_ = lean_ctor_get(v_b_3745_, 0);
lean_dec(v_unused_3858_);
v___x_3785_ = v_b_3745_;
v_isShared_3786_ = v_isSharedCheck_3857_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_snd_3783_);
lean_dec(v_b_3745_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3857_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
uint8_t v___x_3787_; lean_object* v_methods_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3787_ = 1;
v_methods_3788_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1);
v___x_3789_ = lean_box(0);
v___x_3790_ = lean_array_fget_borrowed(v___x_3742_, v_a_3744_);
lean_inc(v___x_3790_);
lean_inc_ref(v_config_3743_);
v___x_3791_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v___x_3787_, v_methods_3788_, v_config_3743_, v___x_3790_, v___y_3747_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3792_; lean_object* v_type_3793_; lean_object* v_value_3794_; uint8_t v___x_3795_; 
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
lean_dec_ref_known(v___x_3791_, 1);
v_type_3793_ = lean_ctor_get(v_a_3792_, 1);
v_value_3794_ = lean_ctor_get(v_a_3792_, 2);
lean_inc_ref(v_type_3793_);
v___x_3795_ = l_Lean_Expr_isFalse(v_type_3793_);
if (v___x_3795_ == 0)
{
lean_object* v_type_3796_; lean_object* v___f_3797_; uint8_t v___x_3798_; 
lean_del_object(v___x_3785_);
v_type_3796_ = lean_ctor_get(v___x_3790_, 1);
lean_inc(v_a_3792_);
lean_inc(v_snd_3783_);
v___f_3797_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1___boxed), 16, 3);
lean_closure_set(v___f_3797_, 0, v_snd_3783_);
lean_closure_set(v___f_3797_, 1, v_a_3792_);
lean_closure_set(v___f_3797_, 2, v___x_3789_);
v___x_3798_ = lean_expr_eqv(v_type_3796_, v_type_3793_);
if (v___x_3798_ == 0)
{
lean_object* v_toCold_3799_; lean_object* v_options_3800_; lean_object* v_inheritedTraceOptions_3801_; uint8_t v_hasTrace_3802_; 
lean_inc_ref(v_type_3793_);
lean_dec(v_a_3792_);
lean_dec(v_snd_3783_);
v_toCold_3799_ = lean_ctor_get(v___y_3755_, 0);
v_options_3800_ = lean_ctor_get(v_toCold_3799_, 2);
v_inheritedTraceOptions_3801_ = lean_ctor_get(v_toCold_3799_, 11);
v_hasTrace_3802_ = lean_ctor_get_uint8(v_options_3800_, sizeof(void*)*1);
if (v_hasTrace_3802_ == 0)
{
lean_dec_ref(v_type_3793_);
goto v___jp_3803_;
}
else
{
lean_object* v___x_3806_; lean_object* v___x_3807_; uint8_t v___x_3808_; 
v___x_3806_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3807_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3808_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3801_, v_options_3800_, v___x_3807_);
if (v___x_3808_ == 0)
{
lean_dec_ref(v_type_3793_);
goto v___jp_3803_;
}
else
{
lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
lean_inc_ref(v_type_3796_);
v___x_3809_ = l_Lean_MessageData_ofExpr(v_type_3796_);
v___x_3810_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3);
v___x_3811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3809_);
lean_ctor_set(v___x_3811_, 1, v___x_3810_);
v___x_3812_ = l_Lean_MessageData_ofExpr(v_type_3793_);
v___x_3813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3811_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
v___x_3814_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v___x_3806_, v___x_3813_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v_a_3815_; lean_object* v___x_3816_; 
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
lean_inc(v_a_3815_);
lean_dec_ref_known(v___x_3814_, 1);
v___x_3816_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_3781_, v___f_3797_, v_a_3815_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
v___y_3759_ = v___x_3816_;
goto v___jp_3758_;
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
lean_dec_ref(v___f_3797_);
lean_dec(v_a_3744_);
lean_dec_ref(v_config_3743_);
v_a_3817_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3814_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3814_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
}
v___jp_3803_:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3804_ = lean_box(0);
v___x_3805_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_3781_, v___f_3797_, v___x_3804_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
v___y_3759_ = v___x_3805_;
goto v___jp_3758_;
}
}
else
{
lean_object* v___x_3825_; lean_object* v___x_3826_; 
lean_dec_ref(v___f_3797_);
v___x_3825_ = lean_box(0);
v___x_3826_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(v_snd_3783_, v_a_3792_, v___x_3789_, v___x_3825_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
v___y_3759_ = v___x_3826_;
goto v___jp_3758_;
}
}
else
{
lean_object* v___x_3827_; 
lean_inc_ref(v_value_3794_);
lean_dec(v_a_3792_);
lean_dec(v_a_3744_);
lean_dec_ref(v_config_3743_);
v___x_3827_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_3794_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3839_; 
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3839_ == 0)
{
lean_object* v_unused_3840_; 
v_unused_3840_ = lean_ctor_get(v___x_3827_, 0);
lean_dec(v_unused_3840_);
v___x_3829_ = v___x_3827_;
v_isShared_3830_ = v_isSharedCheck_3839_;
goto v_resetjp_3828_;
}
else
{
lean_dec(v___x_3827_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3839_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3834_; 
v___x_3831_ = lean_box(v___x_3781_);
v___x_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 0, v___x_3832_);
v___x_3834_ = v___x_3785_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3838_, 1, v_snd_3783_);
v___x_3834_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
lean_object* v___x_3836_; 
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 0, v___x_3834_);
v___x_3836_ = v___x_3829_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___x_3834_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
}
else
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
lean_del_object(v___x_3785_);
lean_dec(v_snd_3783_);
v_a_3841_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3843_ = v___x_3827_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3827_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
lean_del_object(v___x_3785_);
lean_dec(v_snd_3783_);
lean_dec(v_a_3744_);
lean_dec_ref(v_config_3743_);
v_a_3849_ = lean_ctor_get(v___x_3791_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3791_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3791_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3791_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
}
v___jp_3758_:
{
if (lean_obj_tag(v___y_3759_) == 0)
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3772_; 
v_a_3760_ = lean_ctor_get(v___y_3759_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___y_3759_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3762_ = v___y_3759_;
v_isShared_3763_ = v_isSharedCheck_3772_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___y_3759_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3772_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
if (lean_obj_tag(v_a_3760_) == 0)
{
lean_object* v_a_3764_; lean_object* v___x_3766_; 
lean_dec(v_a_3744_);
lean_dec_ref(v_config_3743_);
v_a_3764_ = lean_ctor_get(v_a_3760_, 0);
lean_inc(v_a_3764_);
lean_dec_ref_known(v_a_3760_, 1);
if (v_isShared_3763_ == 0)
{
lean_ctor_set(v___x_3762_, 0, v_a_3764_);
v___x_3766_ = v___x_3762_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3764_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
lean_del_object(v___x_3762_);
v_a_3768_ = lean_ctor_get(v_a_3760_, 0);
lean_inc(v_a_3768_);
lean_dec_ref_known(v_a_3760_, 1);
v___x_3769_ = lean_unsigned_to_nat(1u);
v___x_3770_ = lean_nat_add(v_a_3744_, v___x_3769_);
lean_dec(v_a_3744_);
v_a_3744_ = v___x_3770_;
v_b_3745_ = v_a_3768_;
goto _start;
}
}
}
else
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
lean_dec(v_a_3744_);
lean_dec_ref(v_config_3743_);
v_a_3773_ = lean_ctor_get(v___y_3759_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___y_3759_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___y_3759_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___y_3759_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3778_; 
if (v_isShared_3776_ == 0)
{
v___x_3778_ = v___x_3775_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3773_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_3859_ = _args[0];
lean_object* v___x_3860_ = _args[1];
lean_object* v_config_3861_ = _args[2];
lean_object* v_a_3862_ = _args[3];
lean_object* v_b_3863_ = _args[4];
lean_object* v___y_3864_ = _args[5];
lean_object* v___y_3865_ = _args[6];
lean_object* v___y_3866_ = _args[7];
lean_object* v___y_3867_ = _args[8];
lean_object* v___y_3868_ = _args[9];
lean_object* v___y_3869_ = _args[10];
lean_object* v___y_3870_ = _args[11];
lean_object* v___y_3871_ = _args[12];
lean_object* v___y_3872_ = _args[13];
lean_object* v___y_3873_ = _args[14];
lean_object* v___y_3874_ = _args[15];
lean_object* v___y_3875_ = _args[16];
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_upperBound_3859_, v___x_3860_, v_config_3861_, v_a_3862_, v_b_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec_ref(v___x_3860_);
lean_dec(v_upperBound_3859_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(lean_object* v_config_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_){
_start:
{
lean_object* v___x_3890_; lean_object* v_hypotheses_3891_; lean_object* v___x_3892_; lean_object* v_newHyps_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3890_ = lean_st_ref_get(v___y_3879_);
v_hypotheses_3891_ = lean_ctor_get(v___x_3890_, 3);
lean_inc_ref(v_hypotheses_3891_);
lean_dec(v___x_3890_);
v___x_3892_ = lean_array_get_size(v_hypotheses_3891_);
v_newHyps_3893_ = lean_mk_empty_array_with_capacity(v___x_3892_);
v___x_3894_ = lean_unsigned_to_nat(0u);
v___x_3895_ = lean_box(0);
v___x_3896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3895_);
lean_ctor_set(v___x_3896_, 1, v_newHyps_3893_);
v___x_3897_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v___x_3892_, v_hypotheses_3891_, v_config_3877_, v___x_3894_, v___x_3896_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
lean_dec_ref(v_hypotheses_3891_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3927_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3900_ = v___x_3897_;
v_isShared_3901_ = v_isSharedCheck_3927_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3897_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3927_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v_fst_3902_; 
v_fst_3902_ = lean_ctor_get(v_a_3898_, 0);
if (lean_obj_tag(v_fst_3902_) == 0)
{
lean_object* v_snd_3903_; lean_object* v___x_3904_; lean_object* v_caches_3905_; lean_object* v_typeAnalysis_3906_; lean_object* v_target_3907_; uint8_t v_didChange_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3921_; 
v_snd_3903_ = lean_ctor_get(v_a_3898_, 1);
lean_inc(v_snd_3903_);
lean_dec(v_a_3898_);
v___x_3904_ = lean_st_ref_take(v___y_3879_);
v_caches_3905_ = lean_ctor_get(v___x_3904_, 0);
v_typeAnalysis_3906_ = lean_ctor_get(v___x_3904_, 1);
v_target_3907_ = lean_ctor_get(v___x_3904_, 2);
v_didChange_3908_ = lean_ctor_get_uint8(v___x_3904_, sizeof(void*)*4);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3921_ == 0)
{
lean_object* v_unused_3922_; 
v_unused_3922_ = lean_ctor_get(v___x_3904_, 3);
lean_dec(v_unused_3922_);
v___x_3910_ = v___x_3904_;
v_isShared_3911_ = v_isSharedCheck_3921_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_target_3907_);
lean_inc(v_typeAnalysis_3906_);
lean_inc(v_caches_3905_);
lean_dec(v___x_3904_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3921_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 3, v_snd_3903_);
v___x_3913_ = v___x_3910_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_caches_3905_);
lean_ctor_set(v_reuseFailAlloc_3920_, 1, v_typeAnalysis_3906_);
lean_ctor_set(v_reuseFailAlloc_3920_, 2, v_target_3907_);
lean_ctor_set(v_reuseFailAlloc_3920_, 3, v_snd_3903_);
lean_ctor_set_uint8(v_reuseFailAlloc_3920_, sizeof(void*)*4, v_didChange_3908_);
v___x_3913_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
lean_object* v___x_3914_; uint8_t v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3918_; 
v___x_3914_ = lean_st_ref_put(v___y_3879_, v___x_3913_);
v___x_3915_ = 0;
v___x_3916_ = lean_box(v___x_3915_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v___x_3916_);
v___x_3918_ = v___x_3900_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3916_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
else
{
lean_object* v_val_3923_; lean_object* v___x_3925_; 
lean_inc_ref(v_fst_3902_);
lean_dec(v_a_3898_);
v_val_3923_ = lean_ctor_get(v_fst_3902_, 0);
lean_inc(v_val_3923_);
lean_dec_ref_known(v_fst_3902_, 1);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v_val_3923_);
v___x_3925_ = v___x_3900_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_val_3923_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
v_a_3928_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3897_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3897_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed(lean_object* v_config_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v_res_3949_; 
v_res_3949_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(v_config_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
lean_object* v_config_3962_; lean_object* v_maxSteps_3963_; lean_object* v___x_3964_; lean_object* v_config_3965_; lean_object* v___f_3966_; lean_object* v___x_3967_; lean_object* v_target_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v_config_3962_ = lean_ctor_get(v___y_3950_, 0);
v_maxSteps_3963_ = lean_ctor_get(v_config_3962_, 1);
v___x_3964_ = lean_unsigned_to_nat(2u);
lean_inc(v_maxSteps_3963_);
v_config_3965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_config_3965_, 0, v_maxSteps_3963_);
lean_ctor_set(v_config_3965_, 1, v___x_3964_);
v___f_3966_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed), 13, 1);
lean_closure_set(v___f_3966_, 0, v_config_3965_);
v___x_3967_ = lean_st_ref_get(v___y_3951_);
v_target_3968_ = lean_ctor_get(v___x_3967_, 2);
lean_inc_ref(v_target_3968_);
lean_dec(v___x_3967_);
v___x_3969_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_3968_);
lean_dec_ref(v_target_3968_);
v___x_3970_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v___x_3969_, v___f_3966_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___boxed(lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(lean_object* v_cls_3992_, lean_object* v_msg_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_cls_3992_, v_msg_3993_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___boxed(lean_object* v_cls_4007_, lean_object* v_msg_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(v_cls_4007_, v_msg_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___y_4015_);
lean_dec_ref(v___y_4014_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec(v___y_4011_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(lean_object* v_upperBound_4022_, lean_object* v___x_4023_, lean_object* v_config_4024_, lean_object* v_inst_4025_, lean_object* v_R_4026_, lean_object* v_a_4027_, lean_object* v_b_4028_, lean_object* v_c_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_upperBound_4022_, v___x_4023_, v_config_4024_, v_a_4027_, v_b_4028_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_4043_ = _args[0];
lean_object* v___x_4044_ = _args[1];
lean_object* v_config_4045_ = _args[2];
lean_object* v_inst_4046_ = _args[3];
lean_object* v_R_4047_ = _args[4];
lean_object* v_a_4048_ = _args[5];
lean_object* v_b_4049_ = _args[6];
lean_object* v_c_4050_ = _args[7];
lean_object* v___y_4051_ = _args[8];
lean_object* v___y_4052_ = _args[9];
lean_object* v___y_4053_ = _args[10];
lean_object* v___y_4054_ = _args[11];
lean_object* v___y_4055_ = _args[12];
lean_object* v___y_4056_ = _args[13];
lean_object* v___y_4057_ = _args[14];
lean_object* v___y_4058_ = _args[15];
lean_object* v___y_4059_ = _args[16];
lean_object* v___y_4060_ = _args[17];
lean_object* v___y_4061_ = _args[18];
lean_object* v___y_4062_ = _args[19];
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(v_upperBound_4043_, v___x_4044_, v_config_4045_, v_inst_4046_, v_R_4047_, v_a_4048_, v_b_4049_, v_c_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
lean_dec(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec(v___y_4053_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec_ref(v___x_4044_);
lean_dec(v_upperBound_4043_);
return v_res_4063_;
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
