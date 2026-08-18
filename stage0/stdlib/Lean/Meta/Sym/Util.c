// Lean compiler output
// Module: Lean.Meta.Sym.Util
// Imports: public import Lean.Meta.Sym.SymM public import Lean.Meta.Transform import Lean.Util.ForEachExpr
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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l_Lean_Level_isAlreadyNormalizedCheap(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_preprocessExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Meta.Sym.Util"};
static const lean_object* l_Lean_Meta_Sym_preprocessExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_preprocessExpr___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_preprocessExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Meta.Sym.preprocessExpr"};
static const lean_object* l_Lean_Meta_Sym_preprocessExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_preprocessExpr___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_preprocessExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 110, .m_capacity = 110, .m_length = 109, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Sym.Util.949373316._hygCtx._hyg.9.0 ).enforceUnfoldReducible\n  "};
static const lean_object* l_Lean_Meta_Sym_preprocessExpr___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_preprocessExpr___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Sym_preprocessExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_preprocessExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "term is not in the maximally shared table"};
static const lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1;
static const lean_string_object l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "] "};
static const lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_checkMaxShared___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_checkMaxShared___closed__0;
static lean_once_cell_t l_Lean_Expr_checkMaxShared___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_checkMaxShared___closed__1;
static lean_once_cell_t l_Lean_Expr_checkMaxShared___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_checkMaxShared___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_normalizeLevels___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_normalizeLevels___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0;
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__1;
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_normalizeLevels___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_normalizeLevels___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_normalizeLevels___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_normalizeLevels___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_normalizeLevels___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_normalizeLevels___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_normalizeLevels___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_normalizeLevels___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_607__overap_11_; lean_object* v___x_12_; 
v___x_10_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0___closed__0);
v___x_607__overap_11_ = lean_panic_fn_borrowed(v___x_10_, v_msg_2_);
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_12_ = lean_apply_7(v___x_607__overap_11_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, lean_box(0));
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0___boxed(lean_object* v_msg_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0(v_msg_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___redArg(lean_object* v_e_22_, lean_object* v___y_23_){
_start:
{
uint8_t v___x_25_; 
v___x_25_ = l_Lean_Expr_hasMVar(v_e_22_);
if (v___x_25_ == 0)
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v_e_22_);
return v___x_26_;
}
else
{
lean_object* v___x_27_; lean_object* v_mctx_28_; lean_object* v___x_29_; lean_object* v_fst_30_; lean_object* v_snd_31_; lean_object* v___x_32_; lean_object* v_cache_33_; lean_object* v_zetaDeltaFVarIds_34_; lean_object* v_postponed_35_; lean_object* v_diag_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_45_; 
v___x_27_ = lean_st_ref_get(v___y_23_);
v_mctx_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc_ref(v_mctx_28_);
lean_dec(v___x_27_);
v___x_29_ = l_Lean_instantiateMVarsCore(v_mctx_28_, v_e_22_);
v_fst_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc(v_fst_30_);
v_snd_31_ = lean_ctor_get(v___x_29_, 1);
lean_inc(v_snd_31_);
lean_dec_ref(v___x_29_);
v___x_32_ = lean_st_ref_take(v___y_23_);
v_cache_33_ = lean_ctor_get(v___x_32_, 1);
v_zetaDeltaFVarIds_34_ = lean_ctor_get(v___x_32_, 2);
v_postponed_35_ = lean_ctor_get(v___x_32_, 3);
v_diag_36_ = lean_ctor_get(v___x_32_, 4);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_45_ == 0)
{
lean_object* v_unused_46_; 
v_unused_46_ = lean_ctor_get(v___x_32_, 0);
lean_dec(v_unused_46_);
v___x_38_ = v___x_32_;
v_isShared_39_ = v_isSharedCheck_45_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_diag_36_);
lean_inc(v_postponed_35_);
lean_inc(v_zetaDeltaFVarIds_34_);
lean_inc(v_cache_33_);
lean_dec(v___x_32_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_45_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 0, v_snd_31_);
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_snd_31_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_cache_33_);
lean_ctor_set(v_reuseFailAlloc_44_, 2, v_zetaDeltaFVarIds_34_);
lean_ctor_set(v_reuseFailAlloc_44_, 3, v_postponed_35_);
lean_ctor_set(v_reuseFailAlloc_44_, 4, v_diag_36_);
v___x_41_ = v_reuseFailAlloc_44_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_st_ref_put(v___y_23_, v___x_41_);
v___x_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_43_, 0, v_fst_30_);
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___redArg___boxed(lean_object* v_e_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___redArg(v_e_47_, v___y_48_);
lean_dec(v___y_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1(lean_object* v_e_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___redArg(v_e_51_, v___y_55_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___boxed(lean_object* v_e_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1(v_e_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
return v_res_68_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_preprocessExpr___closed__3(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_72_ = ((lean_object*)(l_Lean_Meta_Sym_preprocessExpr___closed__2));
v___x_73_ = lean_unsigned_to_nat(2u);
v___x_74_ = lean_unsigned_to_nat(20u);
v___x_75_ = ((lean_object*)(l_Lean_Meta_Sym_preprocessExpr___closed__1));
v___x_76_ = ((lean_object*)(l_Lean_Meta_Sym_preprocessExpr___closed__0));
v___x_77_ = l_mkPanicMessageWithDecl(v___x_76_, v___x_75_, v___x_74_, v___x_73_, v___x_72_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessExpr(lean_object* v_e_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_79_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; uint8_t v_enforceUnfoldReducible_88_; 
v_a_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_a_87_);
lean_dec_ref_known(v___x_86_, 1);
v_enforceUnfoldReducible_88_ = lean_ctor_get_uint8(v_a_87_, 1);
lean_dec(v_a_87_);
if (v_enforceUnfoldReducible_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec_ref(v_e_78_);
v___x_89_ = lean_obj_once(&l_Lean_Meta_Sym_preprocessExpr___closed__3, &l_Lean_Meta_Sym_preprocessExpr___closed__3_once, _init_l_Lean_Meta_Sym_preprocessExpr___closed__3);
v___x_90_ = l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0(v___x_89_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; lean_object* v_a_92_; lean_object* v___x_93_; 
v___x_91_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___redArg(v_e_78_, v_a_82_);
v_a_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_a_92_);
lean_dec_ref(v___x_91_);
v___x_93_ = l_Lean_Meta_Sym_shareCommon(v_a_92_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_);
return v___x_93_;
}
}
else
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_101_; 
lean_dec_ref(v_e_78_);
v_a_94_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_101_ == 0)
{
v___x_96_ = v___x_86_;
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_86_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_94_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessExpr___boxed(lean_object* v_e_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Meta_Sym_preprocessExpr(v_e_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_111_, lean_object* v_x_112_, lean_object* v_x_113_, lean_object* v_x_114_){
_start:
{
lean_object* v_ks_115_; lean_object* v_vs_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_140_; 
v_ks_115_ = lean_ctor_get(v_x_111_, 0);
v_vs_116_ = lean_ctor_get(v_x_111_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v_x_111_);
if (v_isSharedCheck_140_ == 0)
{
v___x_118_ = v_x_111_;
v_isShared_119_ = v_isSharedCheck_140_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_vs_116_);
lean_inc(v_ks_115_);
lean_dec(v_x_111_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_140_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = lean_array_get_size(v_ks_115_);
v___x_121_ = lean_nat_dec_lt(v_x_112_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_125_; 
lean_dec(v_x_112_);
v___x_122_ = lean_array_push(v_ks_115_, v_x_113_);
v___x_123_ = lean_array_push(v_vs_116_, v_x_114_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v___x_123_);
lean_ctor_set(v___x_118_, 0, v___x_122_);
v___x_125_ = v___x_118_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v___x_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
else
{
lean_object* v_k_x27_127_; uint8_t v___x_128_; 
v_k_x27_127_ = lean_array_fget_borrowed(v_ks_115_, v_x_112_);
v___x_128_ = l_Lean_instBEqFVarId_beq(v_x_113_, v_k_x27_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_130_; 
if (v_isShared_119_ == 0)
{
v___x_130_ = v___x_118_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_ks_115_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_vs_116_);
v___x_130_ = v_reuseFailAlloc_134_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(1u);
v___x_132_ = lean_nat_add(v_x_112_, v___x_131_);
lean_dec(v_x_112_);
v_x_111_ = v___x_130_;
v_x_112_ = v___x_132_;
goto _start;
}
}
else
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_135_ = lean_array_fset(v_ks_115_, v_x_112_, v_x_113_);
v___x_136_ = lean_array_fset(v_vs_116_, v_x_112_, v_x_114_);
lean_dec(v_x_112_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v___x_136_);
lean_ctor_set(v___x_118_, 0, v___x_135_);
v___x_138_ = v___x_118_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(lean_object* v_n_141_, lean_object* v_k_142_, lean_object* v_v_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(v_n_141_, v___x_144_, v_k_142_, v_v_143_);
return v___x_145_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(lean_object* v_x_147_, size_t v_x_148_, size_t v_x_149_, lean_object* v_x_150_, lean_object* v_x_151_){
_start:
{
if (lean_obj_tag(v_x_147_) == 0)
{
lean_object* v_es_152_; size_t v___x_153_; size_t v___x_154_; lean_object* v_j_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v_es_152_ = lean_ctor_get(v_x_147_, 0);
v___x_153_ = ((size_t)31ULL);
v___x_154_ = lean_usize_land(v_x_148_, v___x_153_);
v_j_155_ = lean_usize_to_nat(v___x_154_);
v___x_156_ = lean_array_get_size(v_es_152_);
v___x_157_ = lean_nat_dec_lt(v_j_155_, v___x_156_);
if (v___x_157_ == 0)
{
lean_dec(v_j_155_);
lean_dec(v_x_151_);
lean_dec(v_x_150_);
return v_x_147_;
}
else
{
lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_196_; 
lean_inc_ref(v_es_152_);
v_isSharedCheck_196_ = !lean_is_exclusive(v_x_147_);
if (v_isSharedCheck_196_ == 0)
{
lean_object* v_unused_197_; 
v_unused_197_ = lean_ctor_get(v_x_147_, 0);
lean_dec(v_unused_197_);
v___x_159_ = v_x_147_;
v_isShared_160_ = v_isSharedCheck_196_;
goto v_resetjp_158_;
}
else
{
lean_dec(v_x_147_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_196_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v_v_161_; lean_object* v___x_162_; lean_object* v_xs_x27_163_; lean_object* v___y_165_; 
v_v_161_ = lean_array_fget(v_es_152_, v_j_155_);
v___x_162_ = lean_box(0);
v_xs_x27_163_ = lean_array_fset(v_es_152_, v_j_155_, v___x_162_);
switch(lean_obj_tag(v_v_161_))
{
case 0:
{
lean_object* v_key_170_; lean_object* v_val_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_181_; 
v_key_170_ = lean_ctor_get(v_v_161_, 0);
v_val_171_ = lean_ctor_get(v_v_161_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v_v_161_);
if (v_isSharedCheck_181_ == 0)
{
v___x_173_ = v_v_161_;
v_isShared_174_ = v_isSharedCheck_181_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_val_171_);
lean_inc(v_key_170_);
lean_dec(v_v_161_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_181_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
uint8_t v___x_175_; 
v___x_175_ = l_Lean_instBEqFVarId_beq(v_x_150_, v_key_170_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_del_object(v___x_173_);
v___x_176_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_170_, v_val_171_, v_x_150_, v_x_151_);
v___x_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
v___y_165_ = v___x_177_;
goto v___jp_164_;
}
else
{
lean_object* v___x_179_; 
lean_dec(v_val_171_);
lean_dec(v_key_170_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 1, v_x_151_);
lean_ctor_set(v___x_173_, 0, v_x_150_);
v___x_179_ = v___x_173_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_x_150_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v_x_151_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
v___y_165_ = v___x_179_;
goto v___jp_164_;
}
}
}
}
case 1:
{
lean_object* v_node_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_194_; 
v_node_182_ = lean_ctor_get(v_v_161_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v_v_161_);
if (v_isSharedCheck_194_ == 0)
{
v___x_184_ = v_v_161_;
v_isShared_185_ = v_isSharedCheck_194_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_node_182_);
lean_dec(v_v_161_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_194_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
size_t v___x_186_; size_t v___x_187_; size_t v___x_188_; size_t v___x_189_; lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_186_ = ((size_t)5ULL);
v___x_187_ = lean_usize_shift_right(v_x_148_, v___x_186_);
v___x_188_ = ((size_t)1ULL);
v___x_189_ = lean_usize_add(v_x_149_, v___x_188_);
v___x_190_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_node_182_, v___x_187_, v___x_189_, v_x_150_, v_x_151_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v___x_190_);
v___x_192_ = v___x_184_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
v___y_165_ = v___x_192_;
goto v___jp_164_;
}
}
}
default: 
{
lean_object* v___x_195_; 
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v_x_150_);
lean_ctor_set(v___x_195_, 1, v_x_151_);
v___y_165_ = v___x_195_;
goto v___jp_164_;
}
}
v___jp_164_:
{
lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_166_ = lean_array_fset(v_xs_x27_163_, v_j_155_, v___y_165_);
lean_dec(v_j_155_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_166_);
v___x_168_ = v___x_159_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
}
else
{
lean_object* v_ks_198_; lean_object* v_vs_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_219_; 
v_ks_198_ = lean_ctor_get(v_x_147_, 0);
v_vs_199_ = lean_ctor_get(v_x_147_, 1);
v_isSharedCheck_219_ = !lean_is_exclusive(v_x_147_);
if (v_isSharedCheck_219_ == 0)
{
v___x_201_ = v_x_147_;
v_isShared_202_ = v_isSharedCheck_219_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_vs_199_);
lean_inc(v_ks_198_);
lean_dec(v_x_147_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_219_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_ks_198_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_vs_199_);
v___x_204_ = v_reuseFailAlloc_218_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v_newNode_205_; uint8_t v___y_207_; size_t v___x_213_; uint8_t v___x_214_; 
v_newNode_205_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(v___x_204_, v_x_150_, v_x_151_);
v___x_213_ = ((size_t)7ULL);
v___x_214_ = lean_usize_dec_le(v___x_213_, v_x_149_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_215_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_205_);
v___x_216_ = lean_unsigned_to_nat(4u);
v___x_217_ = lean_nat_dec_lt(v___x_215_, v___x_216_);
lean_dec(v___x_215_);
v___y_207_ = v___x_217_;
goto v___jp_206_;
}
else
{
v___y_207_ = v___x_214_;
goto v___jp_206_;
}
v___jp_206_:
{
if (v___y_207_ == 0)
{
lean_object* v_ks_208_; lean_object* v_vs_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_ks_208_ = lean_ctor_get(v_newNode_205_, 0);
lean_inc_ref(v_ks_208_);
v_vs_209_ = lean_ctor_get(v_newNode_205_, 1);
lean_inc_ref(v_vs_209_);
lean_dec_ref(v_newNode_205_);
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0);
v___x_212_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_x_149_, v_ks_208_, v_vs_209_, v___x_210_, v___x_211_);
lean_dec_ref(v_vs_209_);
lean_dec_ref(v_ks_208_);
return v___x_212_;
}
else
{
return v_newNode_205_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(size_t v_depth_220_, lean_object* v_keys_221_, lean_object* v_vals_222_, lean_object* v_i_223_, lean_object* v_entries_224_){
_start:
{
lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_225_ = lean_array_get_size(v_keys_221_);
v___x_226_ = lean_nat_dec_lt(v_i_223_, v___x_225_);
if (v___x_226_ == 0)
{
lean_dec(v_i_223_);
return v_entries_224_;
}
else
{
lean_object* v_k_227_; lean_object* v_v_228_; uint64_t v___x_229_; size_t v_h_230_; size_t v___x_231_; lean_object* v___x_232_; size_t v___x_233_; size_t v___x_234_; size_t v___x_235_; size_t v_h_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_k_227_ = lean_array_fget_borrowed(v_keys_221_, v_i_223_);
v_v_228_ = lean_array_fget_borrowed(v_vals_222_, v_i_223_);
v___x_229_ = l_Lean_instHashableFVarId_hash(v_k_227_);
v_h_230_ = lean_uint64_to_usize(v___x_229_);
v___x_231_ = ((size_t)5ULL);
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = ((size_t)1ULL);
v___x_234_ = lean_usize_sub(v_depth_220_, v___x_233_);
v___x_235_ = lean_usize_mul(v___x_231_, v___x_234_);
v_h_236_ = lean_usize_shift_right(v_h_230_, v___x_235_);
v___x_237_ = lean_nat_add(v_i_223_, v___x_232_);
lean_dec(v_i_223_);
lean_inc(v_v_228_);
lean_inc(v_k_227_);
v___x_238_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_entries_224_, v_h_236_, v_depth_220_, v_k_227_, v_v_228_);
v_i_223_ = v___x_237_;
v_entries_224_ = v___x_238_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_240_, lean_object* v_keys_241_, lean_object* v_vals_242_, lean_object* v_i_243_, lean_object* v_entries_244_){
_start:
{
size_t v_depth_boxed_245_; lean_object* v_res_246_; 
v_depth_boxed_245_ = lean_unbox_usize(v_depth_240_);
lean_dec(v_depth_240_);
v_res_246_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_depth_boxed_245_, v_keys_241_, v_vals_242_, v_i_243_, v_entries_244_);
lean_dec_ref(v_vals_242_);
lean_dec_ref(v_keys_241_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___boxed(lean_object* v_x_247_, lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_x_251_){
_start:
{
size_t v_x_9221__boxed_252_; size_t v_x_9222__boxed_253_; lean_object* v_res_254_; 
v_x_9221__boxed_252_ = lean_unbox_usize(v_x_248_);
lean_dec(v_x_248_);
v_x_9222__boxed_253_ = lean_unbox_usize(v_x_249_);
lean_dec(v_x_249_);
v_res_254_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_247_, v_x_9221__boxed_252_, v_x_9222__boxed_253_, v_x_250_, v_x_251_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(lean_object* v_x_255_, lean_object* v_x_256_, lean_object* v_x_257_){
_start:
{
uint64_t v___x_258_; size_t v___x_259_; size_t v___x_260_; lean_object* v___x_261_; 
v___x_258_ = l_Lean_instHashableFVarId_hash(v_x_256_);
v___x_259_ = lean_uint64_to_usize(v___x_258_);
v___x_260_ = ((size_t)1ULL);
v___x_261_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_255_, v___x_259_, v___x_260_, v_x_256_, v_x_257_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(lean_object* v_as_262_, size_t v_sz_263_, size_t v_i_264_, lean_object* v_b_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
uint8_t v___x_273_; 
v___x_273_ = lean_usize_dec_lt(v_i_264_, v_sz_263_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v_b_265_);
return v___x_274_;
}
else
{
lean_object* v_snd_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_380_; 
v_snd_275_ = lean_ctor_get(v_b_265_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v_b_265_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; 
v_unused_381_ = lean_ctor_get(v_b_265_, 0);
lean_dec(v_unused_381_);
v___x_277_ = v_b_265_;
v_isShared_278_ = v_isSharedCheck_380_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_snd_275_);
lean_dec(v_b_265_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_380_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_279_; lean_object* v_a_281_; lean_object* v_a_288_; 
v___x_279_ = lean_box(0);
v_a_288_ = lean_array_uget(v_as_262_, v_i_264_);
if (lean_obj_tag(v_a_288_) == 0)
{
v_a_281_ = v_snd_275_;
goto v___jp_280_;
}
else
{
lean_object* v_snd_289_; lean_object* v_val_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_379_; 
v_snd_289_ = lean_ctor_get(v_snd_275_, 1);
lean_inc(v_snd_289_);
v_val_290_ = lean_ctor_get(v_a_288_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v_a_288_);
if (v_isSharedCheck_379_ == 0)
{
v___x_292_ = v_a_288_;
v_isShared_293_ = v_isSharedCheck_379_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_val_290_);
lean_dec(v_a_288_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_379_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v_fst_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_377_; 
v_fst_294_ = lean_ctor_get(v_snd_275_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v_snd_275_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; 
v_unused_378_ = lean_ctor_get(v_snd_275_, 1);
lean_dec(v_unused_378_);
v___x_296_ = v_snd_275_;
v_isShared_297_ = v_isSharedCheck_377_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_fst_294_);
lean_dec(v_snd_275_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_377_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v_fst_298_; lean_object* v_snd_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_376_; 
v_fst_298_ = lean_ctor_get(v_snd_289_, 0);
v_snd_299_ = lean_ctor_get(v_snd_289_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v_snd_289_);
if (v_isSharedCheck_376_ == 0)
{
v___x_301_ = v_snd_289_;
v_isShared_302_ = v_isSharedCheck_376_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_snd_299_);
lean_inc(v_fst_298_);
lean_dec(v_snd_289_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_376_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v_decl_304_; 
if (lean_obj_tag(v_val_290_) == 0)
{
lean_object* v_fvarId_319_; lean_object* v_userName_320_; lean_object* v_type_321_; uint8_t v_bi_322_; uint8_t v_kind_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_340_; 
v_fvarId_319_ = lean_ctor_get(v_val_290_, 1);
v_userName_320_ = lean_ctor_get(v_val_290_, 2);
v_type_321_ = lean_ctor_get(v_val_290_, 3);
v_bi_322_ = lean_ctor_get_uint8(v_val_290_, sizeof(void*)*4);
v_kind_323_ = lean_ctor_get_uint8(v_val_290_, sizeof(void*)*4 + 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v_val_290_);
if (v_isSharedCheck_340_ == 0)
{
lean_object* v_unused_341_; 
v_unused_341_ = lean_ctor_get(v_val_290_, 0);
lean_dec(v_unused_341_);
v___x_325_ = v_val_290_;
v_isShared_326_ = v_isSharedCheck_340_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_type_321_);
lean_inc(v_userName_320_);
lean_inc(v_fvarId_319_);
lean_dec(v_val_290_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_340_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Meta_Sym_preprocessExpr(v_type_321_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; lean_object* v___x_330_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_328_);
lean_dec_ref_known(v___x_327_, 1);
lean_inc(v_snd_299_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 3, v_a_328_);
lean_ctor_set(v___x_325_, 0, v_snd_299_);
v___x_330_ = v___x_325_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_snd_299_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_fvarId_319_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v_userName_320_);
lean_ctor_set(v_reuseFailAlloc_331_, 3, v_a_328_);
lean_ctor_set_uint8(v_reuseFailAlloc_331_, sizeof(void*)*4, v_bi_322_);
lean_ctor_set_uint8(v_reuseFailAlloc_331_, sizeof(void*)*4 + 1, v_kind_323_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
v_decl_304_ = v___x_330_;
goto v___jp_303_;
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
lean_del_object(v___x_325_);
lean_dec(v_userName_320_);
lean_dec(v_fvarId_319_);
lean_del_object(v___x_301_);
lean_dec(v_snd_299_);
lean_dec(v_fst_298_);
lean_del_object(v___x_296_);
lean_dec(v_fst_294_);
lean_del_object(v___x_292_);
lean_del_object(v___x_277_);
v_a_332_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_327_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_327_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
}
else
{
lean_object* v_fvarId_342_; lean_object* v_userName_343_; lean_object* v_type_344_; lean_object* v_value_345_; uint8_t v_nondep_346_; uint8_t v_kind_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_374_; 
v_fvarId_342_ = lean_ctor_get(v_val_290_, 1);
v_userName_343_ = lean_ctor_get(v_val_290_, 2);
v_type_344_ = lean_ctor_get(v_val_290_, 3);
v_value_345_ = lean_ctor_get(v_val_290_, 4);
v_nondep_346_ = lean_ctor_get_uint8(v_val_290_, sizeof(void*)*5);
v_kind_347_ = lean_ctor_get_uint8(v_val_290_, sizeof(void*)*5 + 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v_val_290_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; 
v_unused_375_ = lean_ctor_get(v_val_290_, 0);
lean_dec(v_unused_375_);
v___x_349_ = v_val_290_;
v_isShared_350_ = v_isSharedCheck_374_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_value_345_);
lean_inc(v_type_344_);
lean_inc(v_userName_343_);
lean_inc(v_fvarId_342_);
lean_dec(v_val_290_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_374_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_Meta_Sym_preprocessExpr(v_type_344_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_353_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref_known(v___x_351_, 1);
v___x_353_ = l_Lean_Meta_Sym_preprocessExpr(v_value_345_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; lean_object* v___x_356_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_a_354_);
lean_dec_ref_known(v___x_353_, 1);
lean_inc(v_snd_299_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 4, v_a_354_);
lean_ctor_set(v___x_349_, 3, v_a_352_);
lean_ctor_set(v___x_349_, 0, v_snd_299_);
v___x_356_ = v___x_349_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_snd_299_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_fvarId_342_);
lean_ctor_set(v_reuseFailAlloc_357_, 2, v_userName_343_);
lean_ctor_set(v_reuseFailAlloc_357_, 3, v_a_352_);
lean_ctor_set(v_reuseFailAlloc_357_, 4, v_a_354_);
lean_ctor_set_uint8(v_reuseFailAlloc_357_, sizeof(void*)*5, v_nondep_346_);
lean_ctor_set_uint8(v_reuseFailAlloc_357_, sizeof(void*)*5 + 1, v_kind_347_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
v_decl_304_ = v___x_356_;
goto v___jp_303_;
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec(v_a_352_);
lean_del_object(v___x_349_);
lean_dec(v_userName_343_);
lean_dec(v_fvarId_342_);
lean_del_object(v___x_301_);
lean_dec(v_snd_299_);
lean_dec(v_fst_298_);
lean_del_object(v___x_296_);
lean_dec(v_fst_294_);
lean_del_object(v___x_292_);
lean_del_object(v___x_277_);
v_a_358_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_353_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_353_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_del_object(v___x_349_);
lean_dec_ref(v_value_345_);
lean_dec(v_userName_343_);
lean_dec(v_fvarId_342_);
lean_del_object(v___x_301_);
lean_dec(v_snd_299_);
lean_dec(v_fst_298_);
lean_del_object(v___x_296_);
lean_dec(v_fst_294_);
lean_del_object(v___x_292_);
lean_del_object(v___x_277_);
v_a_366_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_351_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_351_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
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
v___jp_303_:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_305_ = lean_unsigned_to_nat(1u);
v___x_306_ = lean_nat_add(v_snd_299_, v___x_305_);
lean_dec(v_snd_299_);
lean_inc_ref(v_decl_304_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v_decl_304_);
v___x_308_ = v___x_292_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_decl_304_);
v___x_308_ = v_reuseFailAlloc_318_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_309_ = l_Lean_PersistentArray_push___redArg(v_fst_298_, v___x_308_);
v___x_310_ = l_Lean_LocalDecl_fvarId(v_decl_304_);
v___x_311_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_294_, v___x_310_, v_decl_304_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v___x_306_);
lean_ctor_set(v___x_301_, 0, v___x_309_);
v___x_313_ = v___x_301_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v___x_306_);
v___x_313_ = v_reuseFailAlloc_317_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_315_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 1, v___x_313_);
lean_ctor_set(v___x_296_, 0, v___x_311_);
v___x_315_ = v___x_296_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
v_a_281_ = v___x_315_;
goto v___jp_280_;
}
}
}
}
}
}
}
}
v___jp_280_:
{
lean_object* v___x_283_; 
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 1, v_a_281_);
lean_ctor_set(v___x_277_, 0, v___x_279_);
v___x_283_ = v___x_277_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_a_281_);
v___x_283_ = v_reuseFailAlloc_287_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
size_t v___x_284_; size_t v___x_285_; 
v___x_284_ = ((size_t)1ULL);
v___x_285_ = lean_usize_add(v_i_264_, v___x_284_);
v_i_264_ = v___x_285_;
v_b_265_ = v___x_283_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_as_382_, lean_object* v_sz_383_, lean_object* v_i_384_, lean_object* v_b_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
size_t v_sz_boxed_393_; size_t v_i_boxed_394_; lean_object* v_res_395_; 
v_sz_boxed_393_ = lean_unbox_usize(v_sz_383_);
lean_dec(v_sz_383_);
v_i_boxed_394_ = lean_unbox_usize(v_i_384_);
lean_dec(v_i_384_);
v_res_395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(v_as_382_, v_sz_boxed_393_, v_i_boxed_394_, v_b_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec_ref(v_as_382_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(lean_object* v_as_396_, size_t v_sz_397_, size_t v_i_398_, lean_object* v_b_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
uint8_t v___x_407_; 
v___x_407_ = lean_usize_dec_lt(v_i_398_, v_sz_397_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v_b_399_);
return v___x_408_;
}
else
{
lean_object* v_snd_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_514_; 
v_snd_409_ = lean_ctor_get(v_b_399_, 1);
v_isSharedCheck_514_ = !lean_is_exclusive(v_b_399_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; 
v_unused_515_ = lean_ctor_get(v_b_399_, 0);
lean_dec(v_unused_515_);
v___x_411_ = v_b_399_;
v_isShared_412_ = v_isSharedCheck_514_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_snd_409_);
lean_dec(v_b_399_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_514_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v_a_415_; lean_object* v_a_422_; 
v___x_413_ = lean_box(0);
v_a_422_ = lean_array_uget(v_as_396_, v_i_398_);
if (lean_obj_tag(v_a_422_) == 0)
{
v_a_415_ = v_snd_409_;
goto v___jp_414_;
}
else
{
lean_object* v_snd_423_; lean_object* v_val_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_513_; 
v_snd_423_ = lean_ctor_get(v_snd_409_, 1);
lean_inc(v_snd_423_);
v_val_424_ = lean_ctor_get(v_a_422_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v_a_422_);
if (v_isSharedCheck_513_ == 0)
{
v___x_426_ = v_a_422_;
v_isShared_427_ = v_isSharedCheck_513_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_val_424_);
lean_dec(v_a_422_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_513_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v_fst_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_511_; 
v_fst_428_ = lean_ctor_get(v_snd_409_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v_snd_409_);
if (v_isSharedCheck_511_ == 0)
{
lean_object* v_unused_512_; 
v_unused_512_ = lean_ctor_get(v_snd_409_, 1);
lean_dec(v_unused_512_);
v___x_430_ = v_snd_409_;
v_isShared_431_ = v_isSharedCheck_511_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_fst_428_);
lean_dec(v_snd_409_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_511_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v_fst_432_; lean_object* v_snd_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_510_; 
v_fst_432_ = lean_ctor_get(v_snd_423_, 0);
v_snd_433_ = lean_ctor_get(v_snd_423_, 1);
v_isSharedCheck_510_ = !lean_is_exclusive(v_snd_423_);
if (v_isSharedCheck_510_ == 0)
{
v___x_435_ = v_snd_423_;
v_isShared_436_ = v_isSharedCheck_510_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_snd_433_);
lean_inc(v_fst_432_);
lean_dec(v_snd_423_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_510_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v_decl_438_; 
if (lean_obj_tag(v_val_424_) == 0)
{
lean_object* v_fvarId_453_; lean_object* v_userName_454_; lean_object* v_type_455_; uint8_t v_bi_456_; uint8_t v_kind_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_474_; 
v_fvarId_453_ = lean_ctor_get(v_val_424_, 1);
v_userName_454_ = lean_ctor_get(v_val_424_, 2);
v_type_455_ = lean_ctor_get(v_val_424_, 3);
v_bi_456_ = lean_ctor_get_uint8(v_val_424_, sizeof(void*)*4);
v_kind_457_ = lean_ctor_get_uint8(v_val_424_, sizeof(void*)*4 + 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_val_424_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; 
v_unused_475_ = lean_ctor_get(v_val_424_, 0);
lean_dec(v_unused_475_);
v___x_459_ = v_val_424_;
v_isShared_460_ = v_isSharedCheck_474_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_type_455_);
lean_inc(v_userName_454_);
lean_inc(v_fvarId_453_);
lean_dec(v_val_424_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_474_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Meta_Sym_preprocessExpr(v_type_455_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_464_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_461_, 1);
lean_inc(v_snd_433_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 3, v_a_462_);
lean_ctor_set(v___x_459_, 0, v_snd_433_);
v___x_464_ = v___x_459_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_snd_433_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_fvarId_453_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v_userName_454_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v_a_462_);
lean_ctor_set_uint8(v_reuseFailAlloc_465_, sizeof(void*)*4, v_bi_456_);
lean_ctor_set_uint8(v_reuseFailAlloc_465_, sizeof(void*)*4 + 1, v_kind_457_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
v_decl_438_ = v___x_464_;
goto v___jp_437_;
}
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_del_object(v___x_459_);
lean_dec(v_userName_454_);
lean_dec(v_fvarId_453_);
lean_del_object(v___x_435_);
lean_dec(v_snd_433_);
lean_dec(v_fst_432_);
lean_del_object(v___x_430_);
lean_dec(v_fst_428_);
lean_del_object(v___x_426_);
lean_del_object(v___x_411_);
v_a_466_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_461_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_461_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
else
{
lean_object* v_fvarId_476_; lean_object* v_userName_477_; lean_object* v_type_478_; lean_object* v_value_479_; uint8_t v_nondep_480_; uint8_t v_kind_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_508_; 
v_fvarId_476_ = lean_ctor_get(v_val_424_, 1);
v_userName_477_ = lean_ctor_get(v_val_424_, 2);
v_type_478_ = lean_ctor_get(v_val_424_, 3);
v_value_479_ = lean_ctor_get(v_val_424_, 4);
v_nondep_480_ = lean_ctor_get_uint8(v_val_424_, sizeof(void*)*5);
v_kind_481_ = lean_ctor_get_uint8(v_val_424_, sizeof(void*)*5 + 1);
v_isSharedCheck_508_ = !lean_is_exclusive(v_val_424_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; 
v_unused_509_ = lean_ctor_get(v_val_424_, 0);
lean_dec(v_unused_509_);
v___x_483_ = v_val_424_;
v_isShared_484_ = v_isSharedCheck_508_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_value_479_);
lean_inc(v_type_478_);
lean_inc(v_userName_477_);
lean_inc(v_fvarId_476_);
lean_dec(v_val_424_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_508_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_Meta_Sym_preprocessExpr(v_type_478_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_487_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_485_, 1);
v___x_487_ = l_Lean_Meta_Sym_preprocessExpr(v_value_479_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_490_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_a_488_);
lean_dec_ref_known(v___x_487_, 1);
lean_inc(v_snd_433_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 4, v_a_488_);
lean_ctor_set(v___x_483_, 3, v_a_486_);
lean_ctor_set(v___x_483_, 0, v_snd_433_);
v___x_490_ = v___x_483_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_snd_433_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_fvarId_476_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_userName_477_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v_a_486_);
lean_ctor_set(v_reuseFailAlloc_491_, 4, v_a_488_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*5, v_nondep_480_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*5 + 1, v_kind_481_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
v_decl_438_ = v___x_490_;
goto v___jp_437_;
}
}
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
lean_dec(v_a_486_);
lean_del_object(v___x_483_);
lean_dec(v_userName_477_);
lean_dec(v_fvarId_476_);
lean_del_object(v___x_435_);
lean_dec(v_snd_433_);
lean_dec(v_fst_432_);
lean_del_object(v___x_430_);
lean_dec(v_fst_428_);
lean_del_object(v___x_426_);
lean_del_object(v___x_411_);
v_a_492_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_487_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_487_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_del_object(v___x_483_);
lean_dec_ref(v_value_479_);
lean_dec(v_userName_477_);
lean_dec(v_fvarId_476_);
lean_del_object(v___x_435_);
lean_dec(v_snd_433_);
lean_dec(v_fst_432_);
lean_del_object(v___x_430_);
lean_dec(v_fst_428_);
lean_del_object(v___x_426_);
lean_del_object(v___x_411_);
v_a_500_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_485_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_485_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
v___jp_437_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_439_ = lean_unsigned_to_nat(1u);
v___x_440_ = lean_nat_add(v_snd_433_, v___x_439_);
lean_dec(v_snd_433_);
lean_inc_ref(v_decl_438_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v_decl_438_);
v___x_442_ = v___x_426_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_decl_438_);
v___x_442_ = v_reuseFailAlloc_452_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_443_ = l_Lean_PersistentArray_push___redArg(v_fst_432_, v___x_442_);
v___x_444_ = l_Lean_LocalDecl_fvarId(v_decl_438_);
v___x_445_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_428_, v___x_444_, v_decl_438_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_440_);
lean_ctor_set(v___x_435_, 0, v___x_443_);
v___x_447_ = v___x_435_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v___x_440_);
v___x_447_ = v_reuseFailAlloc_451_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_449_; 
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v___x_447_);
lean_ctor_set(v___x_430_, 0, v___x_445_);
v___x_449_ = v___x_430_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
v_a_415_ = v___x_449_;
goto v___jp_414_;
}
}
}
}
}
}
}
}
v___jp_414_:
{
lean_object* v___x_417_; 
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 1, v_a_415_);
lean_ctor_set(v___x_411_, 0, v___x_413_);
v___x_417_ = v___x_411_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_a_415_);
v___x_417_ = v_reuseFailAlloc_421_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
size_t v___x_418_; size_t v___x_419_; lean_object* v___x_420_; 
v___x_418_ = ((size_t)1ULL);
v___x_419_ = lean_usize_add(v_i_398_, v___x_418_);
v___x_420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(v_as_396_, v_sz_397_, v___x_419_, v___x_417_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
return v___x_420_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6___boxed(lean_object* v_as_516_, lean_object* v_sz_517_, lean_object* v_i_518_, lean_object* v_b_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
size_t v_sz_boxed_527_; size_t v_i_boxed_528_; lean_object* v_res_529_; 
v_sz_boxed_527_ = lean_unbox_usize(v_sz_517_);
lean_dec(v_sz_517_);
v_i_boxed_528_ = lean_unbox_usize(v_i_518_);
lean_dec(v_i_518_);
v_res_529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(v_as_516_, v_sz_boxed_527_, v_i_boxed_528_, v_b_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec_ref(v_as_516_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(lean_object* v_init_530_, lean_object* v_n_531_, lean_object* v_b_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
if (lean_obj_tag(v_n_531_) == 0)
{
lean_object* v_cs_540_; lean_object* v___x_541_; lean_object* v___x_542_; size_t v_sz_543_; size_t v___x_544_; lean_object* v___x_545_; 
v_cs_540_ = lean_ctor_get(v_n_531_, 0);
v___x_541_ = lean_box(0);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v_b_532_);
v_sz_543_ = lean_array_size(v_cs_540_);
v___x_544_ = ((size_t)0ULL);
v___x_545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(v_init_530_, v_cs_540_, v_sz_543_, v___x_544_, v___x_542_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_560_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_560_ == 0)
{
v___x_548_ = v___x_545_;
v_isShared_549_ = v_isSharedCheck_560_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_545_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_560_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v_fst_550_; 
v_fst_550_ = lean_ctor_get(v_a_546_, 0);
if (lean_obj_tag(v_fst_550_) == 0)
{
lean_object* v_snd_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
v_snd_551_ = lean_ctor_get(v_a_546_, 1);
lean_inc(v_snd_551_);
lean_dec(v_a_546_);
v___x_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_552_, 0, v_snd_551_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_552_);
v___x_554_ = v___x_548_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
else
{
lean_object* v_val_556_; lean_object* v___x_558_; 
lean_inc_ref(v_fst_550_);
lean_dec(v_a_546_);
v_val_556_ = lean_ctor_get(v_fst_550_, 0);
lean_inc(v_val_556_);
lean_dec_ref_known(v_fst_550_, 1);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v_val_556_);
v___x_558_ = v___x_548_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_val_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
v_a_561_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_545_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_545_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
else
{
lean_object* v_vs_569_; lean_object* v___x_570_; lean_object* v___x_571_; size_t v_sz_572_; size_t v___x_573_; lean_object* v___x_574_; 
v_vs_569_ = lean_ctor_get(v_n_531_, 0);
v___x_570_ = lean_box(0);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v_b_532_);
v_sz_572_ = lean_array_size(v_vs_569_);
v___x_573_ = ((size_t)0ULL);
v___x_574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(v_vs_569_, v_sz_572_, v___x_573_, v___x_571_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_589_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_589_ == 0)
{
v___x_577_ = v___x_574_;
v_isShared_578_ = v_isSharedCheck_589_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_589_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v_fst_579_; 
v_fst_579_ = lean_ctor_get(v_a_575_, 0);
if (lean_obj_tag(v_fst_579_) == 0)
{
lean_object* v_snd_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
v_snd_580_ = lean_ctor_get(v_a_575_, 1);
lean_inc(v_snd_580_);
lean_dec(v_a_575_);
v___x_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_581_, 0, v_snd_580_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_581_);
v___x_583_ = v___x_577_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
else
{
lean_object* v_val_585_; lean_object* v___x_587_; 
lean_inc_ref(v_fst_579_);
lean_dec(v_a_575_);
v_val_585_ = lean_ctor_get(v_fst_579_, 0);
lean_inc(v_val_585_);
lean_dec_ref_known(v_fst_579_, 1);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v_val_585_);
v___x_587_ = v___x_577_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_val_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
v_a_590_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_574_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_574_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(lean_object* v_init_598_, lean_object* v_as_599_, size_t v_sz_600_, size_t v_i_601_, lean_object* v_b_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
uint8_t v___x_610_; 
v___x_610_ = lean_usize_dec_lt(v_i_601_, v_sz_600_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; 
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v_b_602_);
return v___x_611_;
}
else
{
lean_object* v_snd_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_646_; 
v_snd_612_ = lean_ctor_get(v_b_602_, 1);
v_isSharedCheck_646_ = !lean_is_exclusive(v_b_602_);
if (v_isSharedCheck_646_ == 0)
{
lean_object* v_unused_647_; 
v_unused_647_ = lean_ctor_get(v_b_602_, 0);
lean_dec(v_unused_647_);
v___x_614_ = v_b_602_;
v_isShared_615_ = v_isSharedCheck_646_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_snd_612_);
lean_dec(v_b_602_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_646_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_a_616_; lean_object* v___x_617_; 
v_a_616_ = lean_array_uget_borrowed(v_as_599_, v_i_601_);
lean_inc(v_snd_612_);
v___x_617_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_598_, v_a_616_, v_snd_612_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_637_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_637_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_637_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_637_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
if (lean_obj_tag(v_a_618_) == 0)
{
lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_622_, 0, v_a_618_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_622_);
v___x_624_ = v___x_614_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_snd_612_);
v___x_624_ = v_reuseFailAlloc_628_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_626_; 
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_624_);
v___x_626_ = v___x_620_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
lean_del_object(v___x_620_);
lean_dec(v_snd_612_);
v_a_629_ = lean_ctor_get(v_a_618_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v_a_618_, 1);
v___x_630_ = lean_box(0);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v_a_629_);
lean_ctor_set(v___x_614_, 0, v___x_630_);
v___x_632_ = v___x_614_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_a_629_);
v___x_632_ = v_reuseFailAlloc_636_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
size_t v___x_633_; size_t v___x_634_; 
v___x_633_ = ((size_t)1ULL);
v___x_634_ = lean_usize_add(v_i_601_, v___x_633_);
v_i_601_ = v___x_634_;
v_b_602_ = v___x_632_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_del_object(v___x_614_);
lean_dec(v_snd_612_);
v_a_638_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_617_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_617_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5___boxed(lean_object* v_init_648_, lean_object* v_as_649_, lean_object* v_sz_650_, lean_object* v_i_651_, lean_object* v_b_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
size_t v_sz_boxed_660_; size_t v_i_boxed_661_; lean_object* v_res_662_; 
v_sz_boxed_660_ = lean_unbox_usize(v_sz_650_);
lean_dec(v_sz_650_);
v_i_boxed_661_ = lean_unbox_usize(v_i_651_);
lean_dec(v_i_651_);
v_res_662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(v_init_648_, v_as_649_, v_sz_boxed_660_, v_i_boxed_661_, v_b_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec_ref(v_as_649_);
lean_dec_ref(v_init_648_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2___boxed(lean_object* v_init_663_, lean_object* v_n_664_, lean_object* v_b_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_663_, v_n_664_, v_b_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec_ref(v_n_664_);
lean_dec_ref(v_init_663_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(lean_object* v_as_674_, size_t v_sz_675_, size_t v_i_676_, lean_object* v_b_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
uint8_t v___x_685_; 
v___x_685_ = lean_usize_dec_lt(v_i_676_, v_sz_675_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; 
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v_b_677_);
return v___x_686_;
}
else
{
lean_object* v_snd_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_792_; 
v_snd_687_ = lean_ctor_get(v_b_677_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v_b_677_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v_b_677_, 0);
lean_dec(v_unused_793_);
v___x_689_ = v_b_677_;
v_isShared_690_ = v_isSharedCheck_792_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_snd_687_);
lean_dec(v_b_677_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_792_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v_a_693_; lean_object* v_a_700_; 
v___x_691_ = lean_box(0);
v_a_700_ = lean_array_uget(v_as_674_, v_i_676_);
if (lean_obj_tag(v_a_700_) == 0)
{
v_a_693_ = v_snd_687_;
goto v___jp_692_;
}
else
{
lean_object* v_snd_701_; lean_object* v_val_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_791_; 
v_snd_701_ = lean_ctor_get(v_snd_687_, 1);
lean_inc(v_snd_701_);
v_val_702_ = lean_ctor_get(v_a_700_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v_a_700_);
if (v_isSharedCheck_791_ == 0)
{
v___x_704_ = v_a_700_;
v_isShared_705_ = v_isSharedCheck_791_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_val_702_);
lean_dec(v_a_700_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_791_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v_fst_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_789_; 
v_fst_706_ = lean_ctor_get(v_snd_687_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v_snd_687_);
if (v_isSharedCheck_789_ == 0)
{
lean_object* v_unused_790_; 
v_unused_790_ = lean_ctor_get(v_snd_687_, 1);
lean_dec(v_unused_790_);
v___x_708_ = v_snd_687_;
v_isShared_709_ = v_isSharedCheck_789_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_fst_706_);
lean_dec(v_snd_687_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_789_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v_fst_710_; lean_object* v_snd_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_788_; 
v_fst_710_ = lean_ctor_get(v_snd_701_, 0);
v_snd_711_ = lean_ctor_get(v_snd_701_, 1);
v_isSharedCheck_788_ = !lean_is_exclusive(v_snd_701_);
if (v_isSharedCheck_788_ == 0)
{
v___x_713_ = v_snd_701_;
v_isShared_714_ = v_isSharedCheck_788_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_snd_711_);
lean_inc(v_fst_710_);
lean_dec(v_snd_701_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_788_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v_decl_716_; 
if (lean_obj_tag(v_val_702_) == 0)
{
lean_object* v_fvarId_731_; lean_object* v_userName_732_; lean_object* v_type_733_; uint8_t v_bi_734_; uint8_t v_kind_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_752_; 
v_fvarId_731_ = lean_ctor_get(v_val_702_, 1);
v_userName_732_ = lean_ctor_get(v_val_702_, 2);
v_type_733_ = lean_ctor_get(v_val_702_, 3);
v_bi_734_ = lean_ctor_get_uint8(v_val_702_, sizeof(void*)*4);
v_kind_735_ = lean_ctor_get_uint8(v_val_702_, sizeof(void*)*4 + 1);
v_isSharedCheck_752_ = !lean_is_exclusive(v_val_702_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; 
v_unused_753_ = lean_ctor_get(v_val_702_, 0);
lean_dec(v_unused_753_);
v___x_737_ = v_val_702_;
v_isShared_738_ = v_isSharedCheck_752_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_type_733_);
lean_inc(v_userName_732_);
lean_inc(v_fvarId_731_);
lean_dec(v_val_702_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_752_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Meta_Sym_preprocessExpr(v_type_733_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_742_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
lean_dec_ref_known(v___x_739_, 1);
lean_inc(v_snd_711_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 3, v_a_740_);
lean_ctor_set(v___x_737_, 0, v_snd_711_);
v___x_742_ = v___x_737_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_snd_711_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_fvarId_731_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v_userName_732_);
lean_ctor_set(v_reuseFailAlloc_743_, 3, v_a_740_);
lean_ctor_set_uint8(v_reuseFailAlloc_743_, sizeof(void*)*4, v_bi_734_);
lean_ctor_set_uint8(v_reuseFailAlloc_743_, sizeof(void*)*4 + 1, v_kind_735_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
v_decl_716_ = v___x_742_;
goto v___jp_715_;
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_del_object(v___x_737_);
lean_dec(v_userName_732_);
lean_dec(v_fvarId_731_);
lean_del_object(v___x_713_);
lean_dec(v_snd_711_);
lean_dec(v_fst_710_);
lean_del_object(v___x_708_);
lean_dec(v_fst_706_);
lean_del_object(v___x_704_);
lean_del_object(v___x_689_);
v_a_744_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_739_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_739_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
else
{
lean_object* v_fvarId_754_; lean_object* v_userName_755_; lean_object* v_type_756_; lean_object* v_value_757_; uint8_t v_nondep_758_; uint8_t v_kind_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_786_; 
v_fvarId_754_ = lean_ctor_get(v_val_702_, 1);
v_userName_755_ = lean_ctor_get(v_val_702_, 2);
v_type_756_ = lean_ctor_get(v_val_702_, 3);
v_value_757_ = lean_ctor_get(v_val_702_, 4);
v_nondep_758_ = lean_ctor_get_uint8(v_val_702_, sizeof(void*)*5);
v_kind_759_ = lean_ctor_get_uint8(v_val_702_, sizeof(void*)*5 + 1);
v_isSharedCheck_786_ = !lean_is_exclusive(v_val_702_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; 
v_unused_787_ = lean_ctor_get(v_val_702_, 0);
lean_dec(v_unused_787_);
v___x_761_ = v_val_702_;
v_isShared_762_ = v_isSharedCheck_786_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_value_757_);
lean_inc(v_type_756_);
lean_inc(v_userName_755_);
lean_inc(v_fvarId_754_);
lean_dec(v_val_702_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_786_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_Meta_Sym_preprocessExpr(v_type_756_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_765_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___x_765_ = l_Lean_Meta_Sym_preprocessExpr(v_value_757_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
lean_inc(v_snd_711_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 4, v_a_766_);
lean_ctor_set(v___x_761_, 3, v_a_764_);
lean_ctor_set(v___x_761_, 0, v_snd_711_);
v___x_768_ = v___x_761_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_snd_711_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_fvarId_754_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v_userName_755_);
lean_ctor_set(v_reuseFailAlloc_769_, 3, v_a_764_);
lean_ctor_set(v_reuseFailAlloc_769_, 4, v_a_766_);
lean_ctor_set_uint8(v_reuseFailAlloc_769_, sizeof(void*)*5, v_nondep_758_);
lean_ctor_set_uint8(v_reuseFailAlloc_769_, sizeof(void*)*5 + 1, v_kind_759_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
v_decl_716_ = v___x_768_;
goto v___jp_715_;
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec(v_a_764_);
lean_del_object(v___x_761_);
lean_dec(v_userName_755_);
lean_dec(v_fvarId_754_);
lean_del_object(v___x_713_);
lean_dec(v_snd_711_);
lean_dec(v_fst_710_);
lean_del_object(v___x_708_);
lean_dec(v_fst_706_);
lean_del_object(v___x_704_);
lean_del_object(v___x_689_);
v_a_770_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_765_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_765_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_del_object(v___x_761_);
lean_dec_ref(v_value_757_);
lean_dec(v_userName_755_);
lean_dec(v_fvarId_754_);
lean_del_object(v___x_713_);
lean_dec(v_snd_711_);
lean_dec(v_fst_710_);
lean_del_object(v___x_708_);
lean_dec(v_fst_706_);
lean_del_object(v___x_704_);
lean_del_object(v___x_689_);
v_a_778_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_763_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_763_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
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
v___jp_715_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_717_ = lean_unsigned_to_nat(1u);
v___x_718_ = lean_nat_add(v_snd_711_, v___x_717_);
lean_dec(v_snd_711_);
lean_inc_ref(v_decl_716_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v_decl_716_);
v___x_720_ = v___x_704_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_decl_716_);
v___x_720_ = v_reuseFailAlloc_730_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_721_ = l_Lean_PersistentArray_push___redArg(v_fst_710_, v___x_720_);
v___x_722_ = l_Lean_LocalDecl_fvarId(v_decl_716_);
v___x_723_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_706_, v___x_722_, v_decl_716_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 1, v___x_718_);
lean_ctor_set(v___x_713_, 0, v___x_721_);
v___x_725_ = v___x_713_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___x_718_);
v___x_725_ = v_reuseFailAlloc_729_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_727_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v___x_725_);
lean_ctor_set(v___x_708_, 0, v___x_723_);
v___x_727_ = v___x_708_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
v_a_693_ = v___x_727_;
goto v___jp_692_;
}
}
}
}
}
}
}
}
v___jp_692_:
{
lean_object* v___x_695_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v_a_693_);
lean_ctor_set(v___x_689_, 0, v___x_691_);
v___x_695_ = v___x_689_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_691_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_a_693_);
v___x_695_ = v_reuseFailAlloc_699_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
size_t v___x_696_; size_t v___x_697_; 
v___x_696_ = ((size_t)1ULL);
v___x_697_ = lean_usize_add(v_i_676_, v___x_696_);
v_i_676_ = v___x_697_;
v_b_677_ = v___x_695_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8___boxed(lean_object* v_as_794_, lean_object* v_sz_795_, lean_object* v_i_796_, lean_object* v_b_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
size_t v_sz_boxed_805_; size_t v_i_boxed_806_; lean_object* v_res_807_; 
v_sz_boxed_805_ = lean_unbox_usize(v_sz_795_);
lean_dec(v_sz_795_);
v_i_boxed_806_ = lean_unbox_usize(v_i_796_);
lean_dec(v_i_796_);
v_res_807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(v_as_794_, v_sz_boxed_805_, v_i_boxed_806_, v_b_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec_ref(v_as_794_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(lean_object* v_as_808_, size_t v_sz_809_, size_t v_i_810_, lean_object* v_b_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
uint8_t v___x_819_; 
v___x_819_ = lean_usize_dec_lt(v_i_810_, v_sz_809_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; 
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v_b_811_);
return v___x_820_;
}
else
{
lean_object* v_snd_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_926_; 
v_snd_821_ = lean_ctor_get(v_b_811_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v_b_811_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v_b_811_, 0);
lean_dec(v_unused_927_);
v___x_823_ = v_b_811_;
v_isShared_824_ = v_isSharedCheck_926_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_snd_821_);
lean_dec(v_b_811_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_926_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v_a_827_; lean_object* v_a_834_; 
v___x_825_ = lean_box(0);
v_a_834_ = lean_array_uget(v_as_808_, v_i_810_);
if (lean_obj_tag(v_a_834_) == 0)
{
v_a_827_ = v_snd_821_;
goto v___jp_826_;
}
else
{
lean_object* v_snd_835_; lean_object* v_val_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_925_; 
v_snd_835_ = lean_ctor_get(v_snd_821_, 1);
lean_inc(v_snd_835_);
v_val_836_ = lean_ctor_get(v_a_834_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v_a_834_);
if (v_isSharedCheck_925_ == 0)
{
v___x_838_ = v_a_834_;
v_isShared_839_ = v_isSharedCheck_925_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_val_836_);
lean_dec(v_a_834_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_925_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v_fst_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_923_; 
v_fst_840_ = lean_ctor_get(v_snd_821_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v_snd_821_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; 
v_unused_924_ = lean_ctor_get(v_snd_821_, 1);
lean_dec(v_unused_924_);
v___x_842_ = v_snd_821_;
v_isShared_843_ = v_isSharedCheck_923_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_fst_840_);
lean_dec(v_snd_821_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_923_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v_fst_844_; lean_object* v_snd_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_922_; 
v_fst_844_ = lean_ctor_get(v_snd_835_, 0);
v_snd_845_ = lean_ctor_get(v_snd_835_, 1);
v_isSharedCheck_922_ = !lean_is_exclusive(v_snd_835_);
if (v_isSharedCheck_922_ == 0)
{
v___x_847_ = v_snd_835_;
v_isShared_848_ = v_isSharedCheck_922_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_snd_845_);
lean_inc(v_fst_844_);
lean_dec(v_snd_835_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_922_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_decl_850_; 
if (lean_obj_tag(v_val_836_) == 0)
{
lean_object* v_fvarId_865_; lean_object* v_userName_866_; lean_object* v_type_867_; uint8_t v_bi_868_; uint8_t v_kind_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_886_; 
v_fvarId_865_ = lean_ctor_get(v_val_836_, 1);
v_userName_866_ = lean_ctor_get(v_val_836_, 2);
v_type_867_ = lean_ctor_get(v_val_836_, 3);
v_bi_868_ = lean_ctor_get_uint8(v_val_836_, sizeof(void*)*4);
v_kind_869_ = lean_ctor_get_uint8(v_val_836_, sizeof(void*)*4 + 1);
v_isSharedCheck_886_ = !lean_is_exclusive(v_val_836_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; 
v_unused_887_ = lean_ctor_get(v_val_836_, 0);
lean_dec(v_unused_887_);
v___x_871_ = v_val_836_;
v_isShared_872_ = v_isSharedCheck_886_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_type_867_);
lean_inc(v_userName_866_);
lean_inc(v_fvarId_865_);
lean_dec(v_val_836_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_886_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_Meta_Sym_preprocessExpr(v_type_867_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_876_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref_known(v___x_873_, 1);
lean_inc(v_snd_845_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 3, v_a_874_);
lean_ctor_set(v___x_871_, 0, v_snd_845_);
v___x_876_ = v___x_871_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_snd_845_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_fvarId_865_);
lean_ctor_set(v_reuseFailAlloc_877_, 2, v_userName_866_);
lean_ctor_set(v_reuseFailAlloc_877_, 3, v_a_874_);
lean_ctor_set_uint8(v_reuseFailAlloc_877_, sizeof(void*)*4, v_bi_868_);
lean_ctor_set_uint8(v_reuseFailAlloc_877_, sizeof(void*)*4 + 1, v_kind_869_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
v_decl_850_ = v___x_876_;
goto v___jp_849_;
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_del_object(v___x_871_);
lean_dec(v_userName_866_);
lean_dec(v_fvarId_865_);
lean_del_object(v___x_847_);
lean_dec(v_snd_845_);
lean_dec(v_fst_844_);
lean_del_object(v___x_842_);
lean_dec(v_fst_840_);
lean_del_object(v___x_838_);
lean_del_object(v___x_823_);
v_a_878_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_873_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_873_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
else
{
lean_object* v_fvarId_888_; lean_object* v_userName_889_; lean_object* v_type_890_; lean_object* v_value_891_; uint8_t v_nondep_892_; uint8_t v_kind_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_920_; 
v_fvarId_888_ = lean_ctor_get(v_val_836_, 1);
v_userName_889_ = lean_ctor_get(v_val_836_, 2);
v_type_890_ = lean_ctor_get(v_val_836_, 3);
v_value_891_ = lean_ctor_get(v_val_836_, 4);
v_nondep_892_ = lean_ctor_get_uint8(v_val_836_, sizeof(void*)*5);
v_kind_893_ = lean_ctor_get_uint8(v_val_836_, sizeof(void*)*5 + 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_val_836_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; 
v_unused_921_ = lean_ctor_get(v_val_836_, 0);
lean_dec(v_unused_921_);
v___x_895_ = v_val_836_;
v_isShared_896_ = v_isSharedCheck_920_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_value_891_);
lean_inc(v_type_890_);
lean_inc(v_userName_889_);
lean_inc(v_fvarId_888_);
lean_dec(v_val_836_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_920_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_Meta_Sym_preprocessExpr(v_type_890_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_899_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_897_, 1);
v___x_899_ = l_Lean_Meta_Sym_preprocessExpr(v_value_891_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_902_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
lean_inc(v_snd_845_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 4, v_a_900_);
lean_ctor_set(v___x_895_, 3, v_a_898_);
lean_ctor_set(v___x_895_, 0, v_snd_845_);
v___x_902_ = v___x_895_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_snd_845_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_fvarId_888_);
lean_ctor_set(v_reuseFailAlloc_903_, 2, v_userName_889_);
lean_ctor_set(v_reuseFailAlloc_903_, 3, v_a_898_);
lean_ctor_set(v_reuseFailAlloc_903_, 4, v_a_900_);
lean_ctor_set_uint8(v_reuseFailAlloc_903_, sizeof(void*)*5, v_nondep_892_);
lean_ctor_set_uint8(v_reuseFailAlloc_903_, sizeof(void*)*5 + 1, v_kind_893_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
v_decl_850_ = v___x_902_;
goto v___jp_849_;
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec(v_a_898_);
lean_del_object(v___x_895_);
lean_dec(v_userName_889_);
lean_dec(v_fvarId_888_);
lean_del_object(v___x_847_);
lean_dec(v_snd_845_);
lean_dec(v_fst_844_);
lean_del_object(v___x_842_);
lean_dec(v_fst_840_);
lean_del_object(v___x_838_);
lean_del_object(v___x_823_);
v_a_904_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_899_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_899_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_del_object(v___x_895_);
lean_dec_ref(v_value_891_);
lean_dec(v_userName_889_);
lean_dec(v_fvarId_888_);
lean_del_object(v___x_847_);
lean_dec(v_snd_845_);
lean_dec(v_fst_844_);
lean_del_object(v___x_842_);
lean_dec(v_fst_840_);
lean_del_object(v___x_838_);
lean_del_object(v___x_823_);
v_a_912_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_897_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_897_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
v___jp_849_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_851_ = lean_unsigned_to_nat(1u);
v___x_852_ = lean_nat_add(v_snd_845_, v___x_851_);
lean_dec(v_snd_845_);
lean_inc_ref(v_decl_850_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v_decl_850_);
v___x_854_ = v___x_838_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_decl_850_);
v___x_854_ = v_reuseFailAlloc_864_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_855_ = l_Lean_PersistentArray_push___redArg(v_fst_844_, v___x_854_);
v___x_856_ = l_Lean_LocalDecl_fvarId(v_decl_850_);
v___x_857_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_840_, v___x_856_, v_decl_850_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v___x_852_);
lean_ctor_set(v___x_847_, 0, v___x_855_);
v___x_859_ = v___x_847_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_852_);
v___x_859_ = v_reuseFailAlloc_863_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_861_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v___x_859_);
lean_ctor_set(v___x_842_, 0, v___x_857_);
v___x_861_ = v___x_842_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
v_a_827_ = v___x_861_;
goto v___jp_826_;
}
}
}
}
}
}
}
}
v___jp_826_:
{
lean_object* v___x_829_; 
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v_a_827_);
lean_ctor_set(v___x_823_, 0, v___x_825_);
v___x_829_ = v___x_823_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_a_827_);
v___x_829_ = v_reuseFailAlloc_833_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
size_t v___x_830_; size_t v___x_831_; lean_object* v___x_832_; 
v___x_830_ = ((size_t)1ULL);
v___x_831_ = lean_usize_add(v_i_810_, v___x_830_);
v___x_832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(v_as_808_, v_sz_809_, v___x_831_, v___x_829_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
return v___x_832_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3___boxed(lean_object* v_as_928_, lean_object* v_sz_929_, lean_object* v_i_930_, lean_object* v_b_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
size_t v_sz_boxed_939_; size_t v_i_boxed_940_; lean_object* v_res_941_; 
v_sz_boxed_939_ = lean_unbox_usize(v_sz_929_);
lean_dec(v_sz_929_);
v_i_boxed_940_ = lean_unbox_usize(v_i_930_);
lean_dec(v_i_930_);
v_res_941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(v_as_928_, v_sz_boxed_939_, v_i_boxed_940_, v_b_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_as_928_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(lean_object* v_t_942_, lean_object* v_init_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_root_951_; lean_object* v_tail_952_; lean_object* v___x_953_; 
v_root_951_ = lean_ctor_get(v_t_942_, 0);
v_tail_952_ = lean_ctor_get(v_t_942_, 1);
lean_inc_ref(v_init_943_);
v___x_953_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_943_, v_root_951_, v_init_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec_ref(v_init_943_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_990_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_990_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_990_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_990_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
if (lean_obj_tag(v_a_954_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_960_; 
v_a_958_ = lean_ctor_get(v_a_954_, 0);
lean_inc(v_a_958_);
lean_dec_ref_known(v_a_954_, 1);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v_a_958_);
v___x_960_ = v___x_956_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_958_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_963_; lean_object* v___x_964_; size_t v_sz_965_; size_t v___x_966_; lean_object* v___x_967_; 
lean_del_object(v___x_956_);
v_a_962_ = lean_ctor_get(v_a_954_, 0);
lean_inc(v_a_962_);
lean_dec_ref_known(v_a_954_, 1);
v___x_963_ = lean_box(0);
v___x_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v_a_962_);
v_sz_965_ = lean_array_size(v_tail_952_);
v___x_966_ = ((size_t)0ULL);
v___x_967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(v_tail_952_, v_sz_965_, v___x_966_, v___x_964_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_981_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_981_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_981_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_981_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v_fst_972_; 
v_fst_972_ = lean_ctor_get(v_a_968_, 0);
if (lean_obj_tag(v_fst_972_) == 0)
{
lean_object* v_snd_973_; lean_object* v___x_975_; 
v_snd_973_ = lean_ctor_get(v_a_968_, 1);
lean_inc(v_snd_973_);
lean_dec(v_a_968_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v_snd_973_);
v___x_975_ = v___x_970_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_snd_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
else
{
lean_object* v_val_977_; lean_object* v___x_979_; 
lean_inc_ref(v_fst_972_);
lean_dec(v_a_968_);
v_val_977_ = lean_ctor_get(v_fst_972_, 0);
lean_inc(v_val_977_);
lean_dec_ref_known(v_fst_972_, 1);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v_val_977_);
v___x_979_ = v___x_970_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_val_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
v_a_982_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_967_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_967_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
v_a_991_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_953_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_953_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1___boxed(lean_object* v_t_999_, lean_object* v_init_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(v_t_999_, v_init_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec_ref(v_t_999_);
return v_res_1008_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = lean_unsigned_to_nat(32u);
v___x_1010_ = lean_mk_empty_array_with_capacity(v___x_1009_);
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1(void){
_start:
{
size_t v___x_1012_; lean_object* v_index_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v_decls_1017_; 
v___x_1012_ = ((size_t)5ULL);
v_index_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = lean_unsigned_to_nat(32u);
v___x_1015_ = lean_mk_empty_array_with_capacity(v___x_1014_);
v___x_1016_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0);
v_decls_1017_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_decls_1017_, 0, v___x_1016_);
lean_ctor_set(v_decls_1017_, 1, v___x_1015_);
lean_ctor_set(v_decls_1017_, 2, v_index_1013_);
lean_ctor_set(v_decls_1017_, 3, v_index_1013_);
lean_ctor_set_usize(v_decls_1017_, 4, v___x_1012_);
return v_decls_1017_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2(void){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1018_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3(void){
_start:
{
lean_object* v___x_1019_; lean_object* v_fvarIdToDecl_1020_; 
v___x_1019_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2);
v_fvarIdToDecl_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fvarIdToDecl_1020_, 0, v___x_1019_);
return v_fvarIdToDecl_1020_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4(void){
_start:
{
lean_object* v_index_1021_; lean_object* v_decls_1022_; lean_object* v___x_1023_; 
v_index_1021_ = lean_unsigned_to_nat(0u);
v_decls_1022_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1);
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v_decls_1022_);
lean_ctor_set(v___x_1023_, 1, v_index_1021_);
return v___x_1023_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5(void){
_start:
{
lean_object* v___x_1024_; lean_object* v_fvarIdToDecl_1025_; lean_object* v___x_1026_; 
v___x_1024_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4);
v_fvarIdToDecl_1025_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3);
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v_fvarIdToDecl_1025_);
lean_ctor_set(v___x_1026_, 1, v___x_1024_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(lean_object* v_lctx_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_decls_1035_; lean_object* v_auxDeclToFullName_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1064_; 
v_decls_1035_ = lean_ctor_get(v_lctx_1027_, 1);
v_auxDeclToFullName_1036_ = lean_ctor_get(v_lctx_1027_, 2);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_lctx_1027_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v_lctx_1027_, 0);
lean_dec(v_unused_1065_);
v___x_1038_ = v_lctx_1027_;
v_isShared_1039_ = v_isSharedCheck_1064_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_auxDeclToFullName_1036_);
lean_inc(v_decls_1035_);
lean_dec(v_lctx_1027_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1064_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5);
v___x_1041_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(v_decls_1035_, v___x_1040_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
lean_dec_ref(v_decls_1035_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1055_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1055_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1055_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v_snd_1046_; lean_object* v_fst_1047_; lean_object* v_fst_1048_; lean_object* v___x_1050_; 
v_snd_1046_ = lean_ctor_get(v_a_1042_, 1);
lean_inc(v_snd_1046_);
v_fst_1047_ = lean_ctor_get(v_a_1042_, 0);
lean_inc(v_fst_1047_);
lean_dec(v_a_1042_);
v_fst_1048_ = lean_ctor_get(v_snd_1046_, 0);
lean_inc(v_fst_1048_);
lean_dec(v_snd_1046_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 1, v_fst_1048_);
lean_ctor_set(v___x_1038_, 0, v_fst_1047_);
v___x_1050_ = v___x_1038_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_fst_1047_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_fst_1048_);
lean_ctor_set(v_reuseFailAlloc_1054_, 2, v_auxDeclToFullName_1036_);
v___x_1050_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1052_; 
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1050_);
v___x_1052_ = v___x_1044_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1050_);
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
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_del_object(v___x_1038_);
lean_dec(v_auxDeclToFullName_1036_);
v_a_1056_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1041_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1041_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___boxed(lean_object* v_lctx_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(v_lctx_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0(lean_object* v_00_u03b2_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_x_1076_, v_x_1077_, v_x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(lean_object* v_00_u03b2_1080_, lean_object* v_x_1081_, size_t v_x_1082_, size_t v_x_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_1081_, v_x_1082_, v_x_1083_, v_x_1084_, v_x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1087_, lean_object* v_x_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
size_t v_x_10724__boxed_1093_; size_t v_x_10725__boxed_1094_; lean_object* v_res_1095_; 
v_x_10724__boxed_1093_ = lean_unbox_usize(v_x_1089_);
lean_dec(v_x_1089_);
v_x_10725__boxed_1094_ = lean_unbox_usize(v_x_1090_);
lean_dec(v_x_1090_);
v_res_1095_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(v_00_u03b2_1087_, v_x_1088_, v_x_10724__boxed_1093_, v_x_10725__boxed_1094_, v_x_1091_, v_x_1092_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1096_, lean_object* v_n_1097_, lean_object* v_k_1098_, lean_object* v_v_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(v_n_1097_, v_k_1098_, v_v_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1101_, size_t v_depth_1102_, lean_object* v_keys_1103_, lean_object* v_vals_1104_, lean_object* v_heq_1105_, lean_object* v_i_1106_, lean_object* v_entries_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_depth_1102_, v_keys_1103_, v_vals_1104_, v_i_1106_, v_entries_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1109_, lean_object* v_depth_1110_, lean_object* v_keys_1111_, lean_object* v_vals_1112_, lean_object* v_heq_1113_, lean_object* v_i_1114_, lean_object* v_entries_1115_){
_start:
{
size_t v_depth_boxed_1116_; lean_object* v_res_1117_; 
v_depth_boxed_1116_ = lean_unbox_usize(v_depth_1110_);
lean_dec(v_depth_1110_);
v_res_1117_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(v_00_u03b2_1109_, v_depth_boxed_1116_, v_keys_1111_, v_vals_1112_, v_heq_1113_, v_i_1114_, v_entries_1115_);
lean_dec_ref(v_vals_1112_);
lean_dec_ref(v_keys_1111_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1118_, lean_object* v_x_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1119_, v_x_1120_, v_x_1121_, v_x_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1124_, lean_object* v_x_1125_, lean_object* v_x_1126_, lean_object* v_x_1127_){
_start:
{
lean_object* v_ks_1128_; lean_object* v_vs_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1153_; 
v_ks_1128_ = lean_ctor_get(v_x_1124_, 0);
v_vs_1129_ = lean_ctor_get(v_x_1124_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_x_1124_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1131_ = v_x_1124_;
v_isShared_1132_ = v_isSharedCheck_1153_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_vs_1129_);
lean_inc(v_ks_1128_);
lean_dec(v_x_1124_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1153_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = lean_array_get_size(v_ks_1128_);
v___x_1134_ = lean_nat_dec_lt(v_x_1125_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
lean_dec(v_x_1125_);
v___x_1135_ = lean_array_push(v_ks_1128_, v_x_1126_);
v___x_1136_ = lean_array_push(v_vs_1129_, v_x_1127_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 1, v___x_1136_);
lean_ctor_set(v___x_1131_, 0, v___x_1135_);
v___x_1138_ = v___x_1131_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
else
{
lean_object* v_k_x27_1140_; uint8_t v___x_1141_; 
v_k_x27_1140_ = lean_array_fget_borrowed(v_ks_1128_, v_x_1125_);
v___x_1141_ = l_Lean_instBEqMVarId_beq(v_x_1126_, v_k_x27_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1143_; 
if (v_isShared_1132_ == 0)
{
v___x_1143_ = v___x_1131_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_ks_1128_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_vs_1129_);
v___x_1143_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_unsigned_to_nat(1u);
v___x_1145_ = lean_nat_add(v_x_1125_, v___x_1144_);
lean_dec(v_x_1125_);
v_x_1124_ = v___x_1143_;
v_x_1125_ = v___x_1145_;
goto _start;
}
}
else
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1148_ = lean_array_fset(v_ks_1128_, v_x_1125_, v_x_1126_);
v___x_1149_ = lean_array_fset(v_vs_1129_, v_x_1125_, v_x_1127_);
lean_dec(v_x_1125_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 1, v___x_1149_);
lean_ctor_set(v___x_1131_, 0, v___x_1148_);
v___x_1151_ = v___x_1131_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1148_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1154_, lean_object* v_k_1155_, lean_object* v_v_1156_){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_unsigned_to_nat(0u);
v___x_1158_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1154_, v___x_1157_, v_k_1155_, v_v_1156_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1159_, size_t v_x_1160_, size_t v_x_1161_, lean_object* v_x_1162_, lean_object* v_x_1163_){
_start:
{
if (lean_obj_tag(v_x_1159_) == 0)
{
lean_object* v_es_1164_; size_t v___x_1165_; size_t v___x_1166_; lean_object* v_j_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v_es_1164_ = lean_ctor_get(v_x_1159_, 0);
v___x_1165_ = ((size_t)31ULL);
v___x_1166_ = lean_usize_land(v_x_1160_, v___x_1165_);
v_j_1167_ = lean_usize_to_nat(v___x_1166_);
v___x_1168_ = lean_array_get_size(v_es_1164_);
v___x_1169_ = lean_nat_dec_lt(v_j_1167_, v___x_1168_);
if (v___x_1169_ == 0)
{
lean_dec(v_j_1167_);
lean_dec(v_x_1163_);
lean_dec(v_x_1162_);
return v_x_1159_;
}
else
{
lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1208_; 
lean_inc_ref(v_es_1164_);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_x_1159_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; 
v_unused_1209_ = lean_ctor_get(v_x_1159_, 0);
lean_dec(v_unused_1209_);
v___x_1171_ = v_x_1159_;
v_isShared_1172_ = v_isSharedCheck_1208_;
goto v_resetjp_1170_;
}
else
{
lean_dec(v_x_1159_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1208_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v_v_1173_; lean_object* v___x_1174_; lean_object* v_xs_x27_1175_; lean_object* v___y_1177_; 
v_v_1173_ = lean_array_fget(v_es_1164_, v_j_1167_);
v___x_1174_ = lean_box(0);
v_xs_x27_1175_ = lean_array_fset(v_es_1164_, v_j_1167_, v___x_1174_);
switch(lean_obj_tag(v_v_1173_))
{
case 0:
{
lean_object* v_key_1182_; lean_object* v_val_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1193_; 
v_key_1182_ = lean_ctor_get(v_v_1173_, 0);
v_val_1183_ = lean_ctor_get(v_v_1173_, 1);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_v_1173_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1185_ = v_v_1173_;
v_isShared_1186_ = v_isSharedCheck_1193_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_val_1183_);
lean_inc(v_key_1182_);
lean_dec(v_v_1173_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1193_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
uint8_t v___x_1187_; 
v___x_1187_ = l_Lean_instBEqMVarId_beq(v_x_1162_, v_key_1182_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_del_object(v___x_1185_);
v___x_1188_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1182_, v_val_1183_, v_x_1162_, v_x_1163_);
v___x_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
v___y_1177_ = v___x_1189_;
goto v___jp_1176_;
}
else
{
lean_object* v___x_1191_; 
lean_dec(v_val_1183_);
lean_dec(v_key_1182_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v_x_1163_);
lean_ctor_set(v___x_1185_, 0, v_x_1162_);
v___x_1191_ = v___x_1185_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_x_1162_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_x_1163_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
v___y_1177_ = v___x_1191_;
goto v___jp_1176_;
}
}
}
}
case 1:
{
lean_object* v_node_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1206_; 
v_node_1194_ = lean_ctor_get(v_v_1173_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_v_1173_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1196_ = v_v_1173_;
v_isShared_1197_ = v_isSharedCheck_1206_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_node_1194_);
lean_dec(v_v_1173_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1206_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
size_t v___x_1198_; size_t v___x_1199_; size_t v___x_1200_; size_t v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1198_ = ((size_t)5ULL);
v___x_1199_ = lean_usize_shift_right(v_x_1160_, v___x_1198_);
v___x_1200_ = ((size_t)1ULL);
v___x_1201_ = lean_usize_add(v_x_1161_, v___x_1200_);
v___x_1202_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_node_1194_, v___x_1199_, v___x_1201_, v_x_1162_, v_x_1163_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1202_);
v___x_1204_ = v___x_1196_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
v___y_1177_ = v___x_1204_;
goto v___jp_1176_;
}
}
}
default: 
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1207_, 0, v_x_1162_);
lean_ctor_set(v___x_1207_, 1, v_x_1163_);
v___y_1177_ = v___x_1207_;
goto v___jp_1176_;
}
}
v___jp_1176_:
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = lean_array_fset(v_xs_x27_1175_, v_j_1167_, v___y_1177_);
lean_dec(v_j_1167_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1178_);
v___x_1180_ = v___x_1171_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
else
{
lean_object* v_ks_1210_; lean_object* v_vs_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1231_; 
v_ks_1210_ = lean_ctor_get(v_x_1159_, 0);
v_vs_1211_ = lean_ctor_get(v_x_1159_, 1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_x_1159_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1213_ = v_x_1159_;
v_isShared_1214_ = v_isSharedCheck_1231_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_vs_1211_);
lean_inc(v_ks_1210_);
lean_dec(v_x_1159_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1231_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_ks_1210_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_vs_1211_);
v___x_1216_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v_newNode_1217_; uint8_t v___y_1219_; size_t v___x_1225_; uint8_t v___x_1226_; 
v_newNode_1217_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1216_, v_x_1162_, v_x_1163_);
v___x_1225_ = ((size_t)7ULL);
v___x_1226_ = lean_usize_dec_le(v___x_1225_, v_x_1161_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1227_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1217_);
v___x_1228_ = lean_unsigned_to_nat(4u);
v___x_1229_ = lean_nat_dec_lt(v___x_1227_, v___x_1228_);
lean_dec(v___x_1227_);
v___y_1219_ = v___x_1229_;
goto v___jp_1218_;
}
else
{
v___y_1219_ = v___x_1226_;
goto v___jp_1218_;
}
v___jp_1218_:
{
if (v___y_1219_ == 0)
{
lean_object* v_ks_1220_; lean_object* v_vs_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v_ks_1220_ = lean_ctor_get(v_newNode_1217_, 0);
lean_inc_ref(v_ks_1220_);
v_vs_1221_ = lean_ctor_get(v_newNode_1217_, 1);
lean_inc_ref(v_vs_1221_);
lean_dec_ref(v_newNode_1217_);
v___x_1222_ = lean_unsigned_to_nat(0u);
v___x_1223_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0);
v___x_1224_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1161_, v_ks_1220_, v_vs_1221_, v___x_1222_, v___x_1223_);
lean_dec_ref(v_vs_1221_);
lean_dec_ref(v_ks_1220_);
return v___x_1224_;
}
else
{
return v_newNode_1217_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1232_, lean_object* v_keys_1233_, lean_object* v_vals_1234_, lean_object* v_i_1235_, lean_object* v_entries_1236_){
_start:
{
lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1237_ = lean_array_get_size(v_keys_1233_);
v___x_1238_ = lean_nat_dec_lt(v_i_1235_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_dec(v_i_1235_);
return v_entries_1236_;
}
else
{
lean_object* v_k_1239_; lean_object* v_v_1240_; uint64_t v___x_1241_; size_t v_h_1242_; size_t v___x_1243_; lean_object* v___x_1244_; size_t v___x_1245_; size_t v___x_1246_; size_t v___x_1247_; size_t v_h_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_k_1239_ = lean_array_fget_borrowed(v_keys_1233_, v_i_1235_);
v_v_1240_ = lean_array_fget_borrowed(v_vals_1234_, v_i_1235_);
v___x_1241_ = l_Lean_instHashableMVarId_hash(v_k_1239_);
v_h_1242_ = lean_uint64_to_usize(v___x_1241_);
v___x_1243_ = ((size_t)5ULL);
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = ((size_t)1ULL);
v___x_1246_ = lean_usize_sub(v_depth_1232_, v___x_1245_);
v___x_1247_ = lean_usize_mul(v___x_1243_, v___x_1246_);
v_h_1248_ = lean_usize_shift_right(v_h_1242_, v___x_1247_);
v___x_1249_ = lean_nat_add(v_i_1235_, v___x_1244_);
lean_dec(v_i_1235_);
lean_inc(v_v_1240_);
lean_inc(v_k_1239_);
v___x_1250_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_entries_1236_, v_h_1248_, v_depth_1232_, v_k_1239_, v_v_1240_);
v_i_1235_ = v___x_1249_;
v_entries_1236_ = v___x_1250_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1252_, lean_object* v_keys_1253_, lean_object* v_vals_1254_, lean_object* v_i_1255_, lean_object* v_entries_1256_){
_start:
{
size_t v_depth_boxed_1257_; lean_object* v_res_1258_; 
v_depth_boxed_1257_ = lean_unbox_usize(v_depth_1252_);
lean_dec(v_depth_1252_);
v_res_1258_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1257_, v_keys_1253_, v_vals_1254_, v_i_1255_, v_entries_1256_);
lean_dec_ref(v_vals_1254_);
lean_dec_ref(v_keys_1253_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1259_, lean_object* v_x_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_, lean_object* v_x_1263_){
_start:
{
size_t v_x_2252__boxed_1264_; size_t v_x_2253__boxed_1265_; lean_object* v_res_1266_; 
v_x_2252__boxed_1264_ = lean_unbox_usize(v_x_1260_);
lean_dec(v_x_1260_);
v_x_2253__boxed_1265_ = lean_unbox_usize(v_x_1261_);
lean_dec(v_x_1261_);
v_res_1266_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_1259_, v_x_2252__boxed_1264_, v_x_2253__boxed_1265_, v_x_1262_, v_x_1263_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(lean_object* v_x_1267_, lean_object* v_x_1268_, lean_object* v_x_1269_){
_start:
{
uint64_t v___x_1270_; size_t v___x_1271_; size_t v___x_1272_; lean_object* v___x_1273_; 
v___x_1270_ = l_Lean_instHashableMVarId_hash(v_x_1268_);
v___x_1271_ = lean_uint64_to_usize(v___x_1270_);
v___x_1272_ = ((size_t)1ULL);
v___x_1273_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_1267_, v___x_1271_, v___x_1272_, v_x_1268_, v_x_1269_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(lean_object* v_mvarId_1274_, lean_object* v_val_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; lean_object* v_mctx_1279_; lean_object* v_cache_1280_; lean_object* v_zetaDeltaFVarIds_1281_; lean_object* v_postponed_1282_; lean_object* v_diag_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1312_; 
v___x_1278_ = lean_st_ref_take(v___y_1276_);
v_mctx_1279_ = lean_ctor_get(v___x_1278_, 0);
v_cache_1280_ = lean_ctor_get(v___x_1278_, 1);
v_zetaDeltaFVarIds_1281_ = lean_ctor_get(v___x_1278_, 2);
v_postponed_1282_ = lean_ctor_get(v___x_1278_, 3);
v_diag_1283_ = lean_ctor_get(v___x_1278_, 4);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1285_ = v___x_1278_;
v_isShared_1286_ = v_isSharedCheck_1312_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_diag_1283_);
lean_inc(v_postponed_1282_);
lean_inc(v_zetaDeltaFVarIds_1281_);
lean_inc(v_cache_1280_);
lean_inc(v_mctx_1279_);
lean_dec(v___x_1278_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1312_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_depth_1287_; lean_object* v_levelAssignDepth_1288_; lean_object* v_lmvarCounter_1289_; lean_object* v_mvarCounter_1290_; lean_object* v_lDecls_1291_; lean_object* v_decls_1292_; lean_object* v_userNames_1293_; lean_object* v_lAssignment_1294_; lean_object* v_eAssignment_1295_; lean_object* v_dAssignment_1296_; lean_object* v_instanceTypedMVars_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1311_; 
v_depth_1287_ = lean_ctor_get(v_mctx_1279_, 0);
v_levelAssignDepth_1288_ = lean_ctor_get(v_mctx_1279_, 1);
v_lmvarCounter_1289_ = lean_ctor_get(v_mctx_1279_, 2);
v_mvarCounter_1290_ = lean_ctor_get(v_mctx_1279_, 3);
v_lDecls_1291_ = lean_ctor_get(v_mctx_1279_, 4);
v_decls_1292_ = lean_ctor_get(v_mctx_1279_, 5);
v_userNames_1293_ = lean_ctor_get(v_mctx_1279_, 6);
v_lAssignment_1294_ = lean_ctor_get(v_mctx_1279_, 7);
v_eAssignment_1295_ = lean_ctor_get(v_mctx_1279_, 8);
v_dAssignment_1296_ = lean_ctor_get(v_mctx_1279_, 9);
v_instanceTypedMVars_1297_ = lean_ctor_get(v_mctx_1279_, 10);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_mctx_1279_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1299_ = v_mctx_1279_;
v_isShared_1300_ = v_isSharedCheck_1311_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_instanceTypedMVars_1297_);
lean_inc(v_dAssignment_1296_);
lean_inc(v_eAssignment_1295_);
lean_inc(v_lAssignment_1294_);
lean_inc(v_userNames_1293_);
lean_inc(v_decls_1292_);
lean_inc(v_lDecls_1291_);
lean_inc(v_mvarCounter_1290_);
lean_inc(v_lmvarCounter_1289_);
lean_inc(v_levelAssignDepth_1288_);
lean_inc(v_depth_1287_);
lean_dec(v_mctx_1279_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1311_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1301_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_eAssignment_1295_, v_mvarId_1274_, v_val_1275_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 8, v___x_1301_);
v___x_1303_ = v___x_1299_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_depth_1287_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_levelAssignDepth_1288_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v_lmvarCounter_1289_);
lean_ctor_set(v_reuseFailAlloc_1310_, 3, v_mvarCounter_1290_);
lean_ctor_set(v_reuseFailAlloc_1310_, 4, v_lDecls_1291_);
lean_ctor_set(v_reuseFailAlloc_1310_, 5, v_decls_1292_);
lean_ctor_set(v_reuseFailAlloc_1310_, 6, v_userNames_1293_);
lean_ctor_set(v_reuseFailAlloc_1310_, 7, v_lAssignment_1294_);
lean_ctor_set(v_reuseFailAlloc_1310_, 8, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1310_, 9, v_dAssignment_1296_);
lean_ctor_set(v_reuseFailAlloc_1310_, 10, v_instanceTypedMVars_1297_);
v___x_1303_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1305_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1303_);
v___x_1305_ = v___x_1285_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v_cache_1280_);
lean_ctor_set(v_reuseFailAlloc_1309_, 2, v_zetaDeltaFVarIds_1281_);
lean_ctor_set(v_reuseFailAlloc_1309_, 3, v_postponed_1282_);
lean_ctor_set(v_reuseFailAlloc_1309_, 4, v_diag_1283_);
v___x_1305_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_st_ref_put(v___y_1276_, v___x_1305_);
v___x_1307_ = lean_box(0);
v___x_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
return v___x_1308_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg___boxed(lean_object* v_mvarId_1313_, lean_object* v_val_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_1313_, v_val_1314_, v___y_1315_);
lean_dec(v___y_1315_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object* v_mvarId_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v___x_1326_; 
lean_inc(v_mvarId_1318_);
v___x_1326_ = l_Lean_MVarId_getDecl(v_mvarId_1318_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v_userName_1328_; lean_object* v_lctx_1329_; lean_object* v_type_1330_; lean_object* v_localInstances_1331_; lean_object* v___x_1332_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1326_, 1);
v_userName_1328_ = lean_ctor_get(v_a_1327_, 0);
lean_inc(v_userName_1328_);
v_lctx_1329_ = lean_ctor_get(v_a_1327_, 1);
lean_inc_ref(v_lctx_1329_);
v_type_1330_ = lean_ctor_get(v_a_1327_, 2);
lean_inc_ref(v_type_1330_);
v_localInstances_1331_ = lean_ctor_get(v_a_1327_, 4);
lean_inc_ref(v_localInstances_1331_);
lean_dec(v_a_1327_);
v___x_1332_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(v_lctx_1329_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1334_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
lean_dec_ref_known(v___x_1332_, 1);
v___x_1334_ = l_Lean_Meta_Sym_preprocessExpr(v_type_1330_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; uint8_t v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1335_);
lean_dec_ref_known(v___x_1334_, 1);
v___x_1336_ = 2;
v___x_1337_ = lean_unsigned_to_nat(0u);
v___x_1338_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_1333_, v_localInstances_1331_, v_a_1335_, v___x_1336_, v_userName_1328_, v___x_1337_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1348_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc_n(v_a_1339_, 2);
lean_dec_ref_known(v___x_1338_, 1);
v___x_1340_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_1318_, v_a_1339_, v_a_1322_);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1348_ == 0)
{
lean_object* v_unused_1349_; 
v_unused_1349_ = lean_ctor_get(v___x_1340_, 0);
lean_dec(v_unused_1349_);
v___x_1342_ = v___x_1340_;
v_isShared_1343_ = v_isSharedCheck_1348_;
goto v_resetjp_1341_;
}
else
{
lean_dec(v___x_1340_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1348_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1344_ = l_Lean_Expr_mvarId_x21(v_a_1339_);
lean_dec(v_a_1339_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1344_);
v___x_1346_ = v___x_1342_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec(v_mvarId_1318_);
v_a_1350_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1338_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1338_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec(v_a_1333_);
lean_dec_ref(v_localInstances_1331_);
lean_dec(v_userName_1328_);
lean_dec(v_mvarId_1318_);
v_a_1358_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1334_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1334_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec_ref(v_localInstances_1331_);
lean_dec_ref(v_type_1330_);
lean_dec(v_userName_1328_);
lean_dec(v_mvarId_1318_);
v_a_1366_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1332_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1332_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec(v_mvarId_1318_);
v_a_1374_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1326_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1326_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar___boxed(lean_object* v_mvarId_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_);
lean_dec(v_a_1388_);
lean_dec_ref(v_a_1387_);
lean_dec(v_a_1386_);
lean_dec_ref(v_a_1385_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(lean_object* v_mvarId_1391_, lean_object* v_val_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_1391_, v_val_1392_, v___y_1396_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___boxed(lean_object* v_mvarId_1401_, lean_object* v_val_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(v_mvarId_1401_, v_val_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0(lean_object* v_00_u03b2_1411_, lean_object* v_x_1412_, lean_object* v_x_1413_, lean_object* v_x_1414_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_x_1412_, v_x_1413_, v_x_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1416_, lean_object* v_x_1417_, size_t v_x_1418_, size_t v_x_1419_, lean_object* v_x_1420_, lean_object* v_x_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_1417_, v_x_1418_, v_x_1419_, v_x_1420_, v_x_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1423_, lean_object* v_x_1424_, lean_object* v_x_1425_, lean_object* v_x_1426_, lean_object* v_x_1427_, lean_object* v_x_1428_){
_start:
{
size_t v_x_2605__boxed_1429_; size_t v_x_2606__boxed_1430_; lean_object* v_res_1431_; 
v_x_2605__boxed_1429_ = lean_unbox_usize(v_x_1425_);
lean_dec(v_x_1425_);
v_x_2606__boxed_1430_ = lean_unbox_usize(v_x_1426_);
lean_dec(v_x_1426_);
v_res_1431_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(v_00_u03b2_1423_, v_x_1424_, v_x_2605__boxed_1429_, v_x_2606__boxed_1430_, v_x_1427_, v_x_1428_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1432_, lean_object* v_n_1433_, lean_object* v_k_1434_, lean_object* v_v_1435_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1433_, v_k_1434_, v_v_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1437_, size_t v_depth_1438_, lean_object* v_keys_1439_, lean_object* v_vals_1440_, lean_object* v_heq_1441_, lean_object* v_i_1442_, lean_object* v_entries_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1438_, v_keys_1439_, v_vals_1440_, v_i_1442_, v_entries_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1445_, lean_object* v_depth_1446_, lean_object* v_keys_1447_, lean_object* v_vals_1448_, lean_object* v_heq_1449_, lean_object* v_i_1450_, lean_object* v_entries_1451_){
_start:
{
size_t v_depth_boxed_1452_; lean_object* v_res_1453_; 
v_depth_boxed_1452_ = lean_unbox_usize(v_depth_1446_);
lean_dec(v_depth_1446_);
v_res_1453_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1445_, v_depth_boxed_1452_, v_keys_1447_, v_vals_1448_, v_heq_1449_, v_i_1450_, v_entries_1451_);
lean_dec_ref(v_vals_1448_);
lean_dec_ref(v_keys_1447_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1454_, lean_object* v_x_1455_, lean_object* v_x_1456_, lean_object* v_x_1457_, lean_object* v_x_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1455_, v_x_1456_, v_x_1457_, v_x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(lean_object* v_msgData_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___x_1466_; lean_object* v_env_1467_; lean_object* v___x_1468_; lean_object* v_mctx_1469_; lean_object* v_lctx_1470_; lean_object* v_options_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1466_ = lean_st_ref_get(v___y_1464_);
v_env_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc_ref(v_env_1467_);
lean_dec(v___x_1466_);
v___x_1468_ = lean_st_ref_get(v___y_1462_);
v_mctx_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc_ref(v_mctx_1469_);
lean_dec(v___x_1468_);
v_lctx_1470_ = lean_ctor_get(v___y_1461_, 2);
v_options_1471_ = lean_ctor_get(v___y_1463_, 2);
lean_inc_ref(v_options_1471_);
lean_inc_ref(v_lctx_1470_);
v___x_1472_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1472_, 0, v_env_1467_);
lean_ctor_set(v___x_1472_, 1, v_mctx_1469_);
lean_ctor_set(v___x_1472_, 2, v_lctx_1470_);
lean_ctor_set(v___x_1472_, 3, v_options_1471_);
v___x_1473_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
lean_ctor_set(v___x_1473_, 1, v_msgData_1460_);
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0___boxed(lean_object* v_msgData_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(v_msgData_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(lean_object* v_msg_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_ref_1488_; lean_object* v___x_1489_; lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1498_; 
v_ref_1488_ = lean_ctor_get(v___y_1485_, 5);
v___x_1489_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(v_msg_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1492_ = v___x_1489_;
v_isShared_1493_ = v_isSharedCheck_1498_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1489_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1498_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; lean_object* v___x_1496_; 
lean_inc(v_ref_1488_);
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v_ref_1488_);
lean_ctor_set(v___x_1494_, 1, v_a_1490_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set_tag(v___x_1492_, 1);
lean_ctor_set(v___x_1492_, 0, v___x_1494_);
v___x_1496_ = v___x_1492_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg___boxed(lean_object* v_msg_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
return v_res_1505_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0));
v___x_1508_ = l_Lean_stringToMessageData(v___x_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(lean_object* v_msg_1512_, lean_object* v_e_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v___y_1522_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1529_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2));
v___x_1530_ = lean_string_dec_eq(v_msg_1512_, v___x_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1531_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3));
v___x_1532_ = lean_string_append(v___x_1531_, v_msg_1512_);
lean_dec_ref(v_msg_1512_);
v___x_1533_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__4));
v___x_1534_ = lean_string_append(v___x_1532_, v___x_1533_);
v___y_1522_ = v___x_1534_;
goto v___jp_1521_;
}
else
{
v___y_1522_ = v_msg_1512_;
goto v___jp_1521_;
}
v___jp_1521_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1523_ = l_Lean_stringToMessageData(v___y_1522_);
v___x_1524_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1, &l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1);
v___x_1525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1523_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = l_Lean_indentExpr(v_e_1513_);
v___x_1527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1525_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
v___x_1528_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v___x_1527_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
return v___x_1528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___boxed(lean_object* v_msg_1535_, lean_object* v_e_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_1535_, v_e_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
lean_dec(v_a_1542_);
lean_dec_ref(v_a_1541_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
lean_dec(v_a_1538_);
lean_dec_ref(v_a_1537_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(lean_object* v_00_u03b1_1545_, lean_object* v_msg_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_1546_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___boxed(lean_object* v_00_u03b1_1555_, lean_object* v_msg_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(v_00_u03b1_1555_, v_msg_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1565_, lean_object* v_vals_1566_, lean_object* v_i_1567_, lean_object* v_k_1568_){
_start:
{
lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1569_ = lean_array_get_size(v_keys_1565_);
v___x_1570_ = lean_nat_dec_lt(v_i_1567_, v___x_1569_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; 
lean_dec(v_i_1567_);
v___x_1571_ = lean_box(0);
return v___x_1571_;
}
else
{
lean_object* v_k_x27_1572_; uint8_t v___x_1573_; 
v_k_x27_1572_ = lean_array_fget_borrowed(v_keys_1565_, v_i_1567_);
v___x_1573_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_1568_, v_k_x27_1572_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = lean_unsigned_to_nat(1u);
v___x_1575_ = lean_nat_add(v_i_1567_, v___x_1574_);
lean_dec(v_i_1567_);
v_i_1567_ = v___x_1575_;
goto _start;
}
else
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1577_ = lean_array_fget_borrowed(v_vals_1566_, v_i_1567_);
lean_dec(v_i_1567_);
lean_inc(v___x_1577_);
lean_inc(v_k_x27_1572_);
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v_k_x27_1572_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
return v___x_1579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1580_, lean_object* v_vals_1581_, lean_object* v_i_1582_, lean_object* v_k_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_1580_, v_vals_1581_, v_i_1582_, v_k_1583_);
lean_dec_ref(v_k_1583_);
lean_dec_ref(v_vals_1581_);
lean_dec_ref(v_keys_1580_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(lean_object* v_x_1585_, size_t v_x_1586_, lean_object* v_x_1587_){
_start:
{
if (lean_obj_tag(v_x_1585_) == 0)
{
lean_object* v_es_1588_; lean_object* v___x_1589_; size_t v___x_1590_; size_t v___x_1591_; lean_object* v_j_1592_; lean_object* v___x_1593_; 
v_es_1588_ = lean_ctor_get(v_x_1585_, 0);
v___x_1589_ = lean_box(2);
v___x_1590_ = ((size_t)31ULL);
v___x_1591_ = lean_usize_land(v_x_1586_, v___x_1590_);
v_j_1592_ = lean_usize_to_nat(v___x_1591_);
v___x_1593_ = lean_array_get_borrowed(v___x_1589_, v_es_1588_, v_j_1592_);
lean_dec(v_j_1592_);
switch(lean_obj_tag(v___x_1593_))
{
case 0:
{
lean_object* v_key_1594_; lean_object* v_val_1595_; uint8_t v___x_1596_; 
v_key_1594_ = lean_ctor_get(v___x_1593_, 0);
v_val_1595_ = lean_ctor_get(v___x_1593_, 1);
v___x_1596_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_1587_, v_key_1594_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_box(0);
return v___x_1597_;
}
else
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_inc(v_val_1595_);
lean_inc(v_key_1594_);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v_key_1594_);
lean_ctor_set(v___x_1598_, 1, v_val_1595_);
v___x_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
return v___x_1599_;
}
}
case 1:
{
lean_object* v_node_1600_; size_t v___x_1601_; size_t v___x_1602_; 
v_node_1600_ = lean_ctor_get(v___x_1593_, 0);
v___x_1601_ = ((size_t)5ULL);
v___x_1602_ = lean_usize_shift_right(v_x_1586_, v___x_1601_);
v_x_1585_ = v_node_1600_;
v_x_1586_ = v___x_1602_;
goto _start;
}
default: 
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_box(0);
return v___x_1604_;
}
}
}
else
{
lean_object* v_ks_1605_; lean_object* v_vs_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_ks_1605_ = lean_ctor_get(v_x_1585_, 0);
v_vs_1606_ = lean_ctor_get(v_x_1585_, 1);
v___x_1607_ = lean_unsigned_to_nat(0u);
v___x_1608_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_ks_1605_, v_vs_1606_, v___x_1607_, v_x_1587_);
return v___x_1608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_1609_, lean_object* v_x_1610_, lean_object* v_x_1611_){
_start:
{
size_t v_x_9483__boxed_1612_; lean_object* v_res_1613_; 
v_x_9483__boxed_1612_ = lean_unbox_usize(v_x_1610_);
lean_dec(v_x_1610_);
v_res_1613_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_1609_, v_x_9483__boxed_1612_, v_x_1611_);
lean_dec_ref(v_x_1611_);
lean_dec_ref(v_x_1609_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(lean_object* v_x_1614_, lean_object* v_x_1615_){
_start:
{
uint64_t v___x_1616_; size_t v___x_1617_; lean_object* v___x_1618_; 
v___x_1616_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_1615_);
v___x_1617_ = lean_uint64_to_usize(v___x_1616_);
v___x_1618_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_1614_, v___x_1617_, v_x_1615_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg___boxed(lean_object* v_x_1619_, lean_object* v_x_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_x_1619_, v_x_1620_);
lean_dec_ref(v_x_1620_);
lean_dec_ref(v_x_1619_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0(lean_object* v_msg_1622_, lean_object* v_e_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___y_1636_; lean_object* v___x_1645_; lean_object* v_share_1646_; lean_object* v___x_1647_; 
v___x_1645_ = lean_st_ref_get(v___y_1625_);
v_share_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc_ref(v_share_1646_);
lean_dec(v___x_1645_);
v___x_1647_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_share_1646_, v_e_1623_);
lean_dec_ref(v_share_1646_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v___x_1648_; 
v___x_1648_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_1622_, v_e_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
v___y_1636_ = v___x_1648_;
goto v___jp_1635_;
}
else
{
lean_object* v_val_1649_; lean_object* v_fst_1650_; size_t v___x_1651_; size_t v___x_1652_; uint8_t v___x_1653_; 
v_val_1649_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_val_1649_);
lean_dec_ref_known(v___x_1647_, 1);
v_fst_1650_ = lean_ctor_get(v_val_1649_, 0);
lean_inc(v_fst_1650_);
lean_dec(v_val_1649_);
v___x_1651_ = lean_ptr_addr(v_fst_1650_);
lean_dec(v_fst_1650_);
v___x_1652_ = lean_ptr_addr(v_e_1623_);
v___x_1653_ = lean_usize_dec_eq(v___x_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; 
v___x_1654_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_1622_, v_e_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
v___y_1636_ = v___x_1654_;
goto v___jp_1635_;
}
else
{
lean_dec_ref(v_e_1623_);
lean_dec_ref(v_msg_1622_);
goto v___jp_1631_;
}
}
v___jp_1631_:
{
uint8_t v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1632_ = 1;
v___x_1633_ = lean_box(v___x_1632_);
v___x_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
return v___x_1634_;
}
v___jp_1635_:
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
v_a_1637_ = lean_ctor_get(v___y_1636_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___y_1636_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___y_1636_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___y_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0___boxed(lean_object* v_msg_1655_, lean_object* v_e_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_Expr_checkMaxShared___lam__0(v_msg_1655_, v_e_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(lean_object* v_m_1665_, lean_object* v_query_1666_, lean_object* v_x_1667_, lean_object* v_x_1668_, lean_object* v_x_1669_){
_start:
{
lean_object* v_zero_1670_; uint8_t v_isZero_1671_; 
v_zero_1670_ = lean_unsigned_to_nat(0u);
v_isZero_1671_ = lean_nat_dec_eq(v_x_1668_, v_zero_1670_);
if (v_isZero_1671_ == 1)
{
lean_dec(v_x_1669_);
lean_dec(v_x_1668_);
if (lean_obj_tag(v_x_1667_) == 0)
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_box(2);
return v___x_1672_;
}
else
{
lean_object* v_val_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
v_val_1673_ = lean_ctor_get(v_x_1667_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_x_1667_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v_x_1667_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_val_1673_);
lean_dec(v_x_1667_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_val_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
else
{
lean_object* v_keyArray_1681_; lean_object* v_valueArray_1682_; lean_object* v___x_1683_; uint8_t v_isSome_1684_; 
v_keyArray_1681_ = lean_ctor_get(v_m_1665_, 1);
v_valueArray_1682_ = lean_ctor_get(v_m_1665_, 2);
v___x_1683_ = lean_array_fget_borrowed(v_keyArray_1681_, v_x_1669_);
v_isSome_1684_ = lean_noption_is_some(v___x_1683_);
if (v_isSome_1684_ == 0)
{
lean_dec(v_x_1668_);
if (lean_obj_tag(v_x_1667_) == 0)
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1685_, 0, v_x_1669_);
return v___x_1685_;
}
else
{
lean_object* v_val_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_x_1669_);
v_val_1686_ = lean_ctor_get(v_x_1667_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_x_1667_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v_x_1667_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_val_1686_);
lean_dec(v_x_1667_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_val_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
else
{
lean_object* v_one_1694_; lean_object* v_n_1695_; lean_object* v___y_1697_; 
v_one_1694_ = lean_unsigned_to_nat(1u);
v_n_1695_ = lean_nat_sub(v_x_1668_, v_one_1694_);
lean_dec(v_x_1668_);
if (v_isSome_1684_ == 0)
{
goto v___jp_1703_;
}
else
{
lean_object* v___x_1705_; uint8_t v_isSome_1706_; 
v___x_1705_ = lean_array_fget_borrowed(v_valueArray_1682_, v_x_1669_);
v_isSome_1706_ = lean_noption_is_some(v___x_1705_);
if (v_isSome_1706_ == 0)
{
goto v___jp_1703_;
}
else
{
lean_object* v_val_1707_; uint8_t v___x_1708_; 
lean_inc(v___x_1683_);
v_val_1707_ = lean_noption_get(v___x_1683_);
v___x_1708_ = lean_expr_eqv(v_val_1707_, v_query_1666_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; 
lean_dec(v_val_1707_);
v___x_1709_ = lean_array_get_size(v_keyArray_1681_);
v___x_1710_ = lean_nat_add(v_x_1669_, v_one_1694_);
lean_dec(v_x_1669_);
v___x_1711_ = lean_nat_dec_lt(v___x_1710_, v___x_1709_);
if (v___x_1711_ == 0)
{
lean_dec(v___x_1710_);
v_x_1668_ = v_n_1695_;
v_x_1669_ = v_zero_1670_;
goto _start;
}
else
{
v_x_1668_ = v_n_1695_;
v_x_1669_ = v___x_1710_;
goto _start;
}
}
else
{
lean_object* v_val_1714_; lean_object* v___x_1715_; 
lean_dec(v_n_1695_);
lean_dec(v_x_1667_);
lean_inc(v___x_1705_);
v_val_1714_ = lean_noption_get(v___x_1705_);
v___x_1715_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1715_, 0, v_x_1669_);
lean_ctor_set(v___x_1715_, 1, v_val_1707_);
lean_ctor_set(v___x_1715_, 2, v_val_1714_);
return v___x_1715_;
}
}
}
v___jp_1696_:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v___x_1698_ = lean_array_get_size(v_keyArray_1681_);
v___x_1699_ = lean_nat_add(v_x_1669_, v_one_1694_);
lean_dec(v_x_1669_);
v___x_1700_ = lean_nat_dec_lt(v___x_1699_, v___x_1698_);
if (v___x_1700_ == 0)
{
lean_dec(v___x_1699_);
v_x_1667_ = v___y_1697_;
v_x_1668_ = v_n_1695_;
v_x_1669_ = v_zero_1670_;
goto _start;
}
else
{
v_x_1667_ = v___y_1697_;
v_x_1668_ = v_n_1695_;
v_x_1669_ = v___x_1699_;
goto _start;
}
}
v___jp_1703_:
{
if (lean_obj_tag(v_x_1667_) == 0)
{
lean_object* v___x_1704_; 
lean_inc(v_x_1669_);
v___x_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1704_, 0, v_x_1669_);
v___y_1697_ = v___x_1704_;
goto v___jp_1696_;
}
else
{
v___y_1697_ = v_x_1667_;
goto v___jp_1696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_m_1716_, lean_object* v_query_1717_, lean_object* v_x_1718_, lean_object* v_x_1719_, lean_object* v_x_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_m_1716_, v_query_1717_, v_x_1718_, v_x_1719_, v_x_1720_);
lean_dec_ref(v_query_1717_);
lean_dec_ref(v_m_1716_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(lean_object* v_m_1722_, lean_object* v_query_1723_){
_start:
{
lean_object* v_keyArray_1724_; lean_object* v___x_1725_; uint64_t v___x_1726_; uint64_t v___x_1727_; uint64_t v___x_1728_; uint64_t v_fold_1729_; uint64_t v___x_1730_; uint64_t v___x_1731_; uint64_t v___x_1732_; size_t v___x_1733_; size_t v___x_1734_; size_t v___x_1735_; size_t v___x_1736_; size_t v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_keyArray_1724_ = lean_ctor_get(v_m_1722_, 1);
v___x_1725_ = lean_array_get_size(v_keyArray_1724_);
v___x_1726_ = l_Lean_Expr_hash(v_query_1723_);
v___x_1727_ = 32ULL;
v___x_1728_ = lean_uint64_shift_right(v___x_1726_, v___x_1727_);
v_fold_1729_ = lean_uint64_xor(v___x_1726_, v___x_1728_);
v___x_1730_ = 16ULL;
v___x_1731_ = lean_uint64_shift_right(v_fold_1729_, v___x_1730_);
v___x_1732_ = lean_uint64_xor(v_fold_1729_, v___x_1731_);
v___x_1733_ = lean_uint64_to_usize(v___x_1732_);
v___x_1734_ = lean_usize_of_nat(v___x_1725_);
v___x_1735_ = ((size_t)1ULL);
v___x_1736_ = lean_usize_sub(v___x_1734_, v___x_1735_);
v___x_1737_ = lean_usize_land(v___x_1733_, v___x_1736_);
v___x_1738_ = lean_usize_to_nat(v___x_1737_);
v___x_1739_ = lean_box(0);
v___x_1740_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_m_1722_, v_query_1723_, v___x_1739_, v___x_1725_, v___x_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg___boxed(lean_object* v_m_1741_, lean_object* v_query_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v_m_1741_, v_query_1742_);
lean_dec_ref(v_query_1742_);
lean_dec_ref(v_m_1741_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8_spec__9___redArg(lean_object* v_b_1744_, lean_object* v_acc_1745_, lean_object* v_i_1746_){
_start:
{
lean_object* v___y_1748_; lean_object* v_keyArray_1756_; lean_object* v_valueArray_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
v_keyArray_1756_ = lean_ctor_get(v_b_1744_, 1);
v_valueArray_1757_ = lean_ctor_get(v_b_1744_, 2);
v___x_1758_ = lean_array_get_size(v_keyArray_1756_);
v___x_1759_ = lean_nat_dec_lt(v_i_1746_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_dec(v_i_1746_);
return v_acc_1745_;
}
else
{
lean_object* v___x_1760_; uint8_t v_isSome_1761_; 
v___x_1760_ = lean_array_fget_borrowed(v_keyArray_1756_, v_i_1746_);
v_isSome_1761_ = lean_noption_is_some(v___x_1760_);
if (v_isSome_1761_ == 0)
{
goto v___jp_1752_;
}
else
{
lean_object* v___x_1762_; uint8_t v_isSome_1763_; 
v___x_1762_ = lean_array_fget_borrowed(v_valueArray_1757_, v_i_1746_);
v_isSome_1763_ = lean_noption_is_some(v___x_1762_);
if (v_isSome_1763_ == 0)
{
goto v___jp_1752_;
}
else
{
lean_object* v_val_1764_; lean_object* v_val_1765_; lean_object* v_i_1767_; lean_object* v___x_1772_; 
lean_inc(v___x_1760_);
v_val_1764_ = lean_noption_get(v___x_1760_);
lean_inc(v___x_1762_);
v_val_1765_ = lean_noption_get(v___x_1762_);
v___x_1772_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v_acc_1745_, v_val_1764_);
switch(lean_obj_tag(v___x_1772_))
{
case 0:
{
lean_object* v_index_1773_; lean_object* v_size_1774_; lean_object* v___x_1775_; 
v_index_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_index_1773_);
lean_dec_ref_known(v___x_1772_, 3);
v_size_1774_ = lean_ctor_get(v_acc_1745_, 0);
lean_inc(v_size_1774_);
v___x_1775_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1745_, v_size_1774_, v_index_1773_, v_val_1764_, v_val_1765_);
lean_dec(v_index_1773_);
v___y_1748_ = v___x_1775_;
goto v___jp_1747_;
}
case 1:
{
lean_object* v_index_1776_; 
v_index_1776_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_index_1776_);
lean_dec_ref_known(v___x_1772_, 1);
v_i_1767_ = v_index_1776_;
goto v___jp_1766_;
}
default: 
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = lean_unsigned_to_nat(0u);
v___x_1778_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1745_, v___x_1777_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_index_1779_; 
v_index_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_index_1779_);
lean_dec_ref_known(v___x_1778_, 1);
v_i_1767_ = v_index_1779_;
goto v___jp_1766_;
}
else
{
lean_dec(v_val_1765_);
lean_dec(v_val_1764_);
v___y_1748_ = v_acc_1745_;
goto v___jp_1747_;
}
}
}
v___jp_1766_:
{
lean_object* v_size_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_size_1768_ = lean_ctor_get(v_acc_1745_, 0);
v___x_1769_ = lean_unsigned_to_nat(1u);
v___x_1770_ = lean_nat_add(v_size_1768_, v___x_1769_);
v___x_1771_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1745_, v___x_1770_, v_i_1767_, v_val_1764_, v_val_1765_);
lean_dec(v_i_1767_);
v___y_1748_ = v___x_1771_;
goto v___jp_1747_;
}
}
}
}
v___jp_1747_:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = lean_unsigned_to_nat(1u);
v___x_1750_ = lean_nat_add(v_i_1746_, v___x_1749_);
lean_dec(v_i_1746_);
v_acc_1745_ = v___y_1748_;
v_i_1746_ = v___x_1750_;
goto _start;
}
v___jp_1752_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = lean_unsigned_to_nat(1u);
v___x_1754_ = lean_nat_add(v_i_1746_, v___x_1753_);
lean_dec(v_i_1746_);
v_i_1746_ = v___x_1754_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8_spec__9___redArg___boxed(lean_object* v_b_1780_, lean_object* v_acc_1781_, lean_object* v_i_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8_spec__9___redArg(v_b_1780_, v_acc_1781_, v_i_1782_);
lean_dec_ref(v_b_1780_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8___redArg(lean_object* v_init_1784_, lean_object* v_b_1785_){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = lean_unsigned_to_nat(0u);
v___x_1787_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8_spec__9___redArg(v_b_1785_, v_init_1784_, v___x_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_init_1788_, lean_object* v_b_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8___redArg(v_init_1788_, v_b_1789_);
lean_dec_ref(v_b_1789_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4___redArg(lean_object* v_m_1791_){
_start:
{
lean_object* v_keyArray_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v_cellCount_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v_target_1799_; lean_object* v___x_1800_; 
v_keyArray_1792_ = lean_ctor_get(v_m_1791_, 1);
v___x_1793_ = lean_array_get_size(v_keyArray_1792_);
v___x_1794_ = lean_unsigned_to_nat(2u);
v_cellCount_1795_ = lean_nat_mul(v___x_1793_, v___x_1794_);
v___x_1796_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1795_);
v___x_1797_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1795_);
v___x_1798_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1795_);
v_target_1799_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1799_, 0, v___x_1796_);
lean_ctor_set(v_target_1799_, 1, v___x_1797_);
lean_ctor_set(v_target_1799_, 2, v___x_1798_);
v___x_1800_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8___redArg(v_target_1799_, v_m_1791_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4___redArg___boxed(lean_object* v_m_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4___redArg(v_m_1801_);
lean_dec_ref(v_m_1801_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(lean_object* v_m_1803_, lean_object* v_query_1804_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v_m_1803_, v_query_1804_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_index_1806_; lean_object* v_key_1807_; lean_object* v_value_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
v_index_1806_ = lean_ctor_get(v___x_1805_, 0);
v_key_1807_ = lean_ctor_get(v___x_1805_, 1);
v_value_1808_ = lean_ctor_get(v___x_1805_, 2);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1805_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_value_1808_);
lean_inc(v_key_1807_);
lean_inc(v_index_1806_);
lean_dec(v___x_1805_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_index_1806_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_key_1807_);
lean_ctor_set(v_reuseFailAlloc_1814_, 2, v_value_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
else
{
lean_object* v___x_1816_; 
lean_dec(v___x_1805_);
v___x_1816_ = lean_box(1);
return v___x_1816_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_m_1817_, lean_object* v_query_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_m_1817_, v_query_1818_);
lean_dec_ref(v_query_1818_);
lean_dec_ref(v_m_1817_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(lean_object* v_m_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_m_1820_, v_a_1821_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_value_1823_; lean_object* v___x_1824_; 
v_value_1823_ = lean_ctor_get(v___x_1822_, 2);
lean_inc(v_value_1823_);
lean_dec_ref_known(v___x_1822_, 3);
v___x_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1824_, 0, v_value_1823_);
return v___x_1824_;
}
else
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_box(0);
return v___x_1825_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg___boxed(lean_object* v_m_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_1826_, v_a_1827_);
lean_dec_ref(v_a_1827_);
lean_dec_ref(v_m_1826_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(lean_object* v_g_1829_, lean_object* v_e_1830_, lean_object* v_a_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v_i_1847_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v_i_1866_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v_a_1884_; lean_object* v___y_1917_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = lean_st_ref_get(v_a_1831_);
v___x_1920_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v___x_1919_, v_e_1830_);
lean_dec(v___x_1919_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v___x_1921_; 
lean_inc_ref(v_g_1829_);
lean_inc(v___y_1837_);
lean_inc_ref(v___y_1836_);
lean_inc(v___y_1835_);
lean_inc_ref(v___y_1834_);
lean_inc(v___y_1833_);
lean_inc_ref(v___y_1832_);
lean_inc_ref(v_e_1830_);
v___x_1921_ = lean_apply_8(v_g_1829_, v_e_1830_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, lean_box(0));
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v_d_1924_; lean_object* v_b_1925_; lean_object* v___y_1926_; uint8_t v___x_1929_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
v___x_1929_ = lean_unbox(v_a_1922_);
lean_dec(v_a_1922_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; 
lean_dec_ref(v_g_1829_);
v___x_1930_ = lean_box(0);
v_a_1884_ = v___x_1930_;
goto v___jp_1883_;
}
else
{
switch(lean_obj_tag(v_e_1830_))
{
case 7:
{
lean_object* v_binderType_1931_; lean_object* v_body_1932_; 
v_binderType_1931_ = lean_ctor_get(v_e_1830_, 1);
v_body_1932_ = lean_ctor_get(v_e_1830_, 2);
lean_inc_ref(v_body_1932_);
lean_inc_ref(v_binderType_1931_);
v_d_1924_ = v_binderType_1931_;
v_b_1925_ = v_body_1932_;
v___y_1926_ = v_a_1831_;
goto v___jp_1923_;
}
case 6:
{
lean_object* v_binderType_1933_; lean_object* v_body_1934_; 
v_binderType_1933_ = lean_ctor_get(v_e_1830_, 1);
v_body_1934_ = lean_ctor_get(v_e_1830_, 2);
lean_inc_ref(v_body_1934_);
lean_inc_ref(v_binderType_1933_);
v_d_1924_ = v_binderType_1933_;
v_b_1925_ = v_body_1934_;
v___y_1926_ = v_a_1831_;
goto v___jp_1923_;
}
case 8:
{
lean_object* v_type_1935_; lean_object* v_value_1936_; lean_object* v_body_1937_; lean_object* v___x_1938_; 
v_type_1935_ = lean_ctor_get(v_e_1830_, 1);
v_value_1936_ = lean_ctor_get(v_e_1830_, 2);
v_body_1937_ = lean_ctor_get(v_e_1830_, 3);
lean_inc_ref(v_type_1935_);
lean_inc_ref(v_g_1829_);
v___x_1938_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1829_, v_type_1935_, v_a_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v___x_1939_; 
lean_dec_ref_known(v___x_1938_, 1);
lean_inc_ref(v_value_1936_);
lean_inc_ref(v_g_1829_);
v___x_1939_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1829_, v_value_1936_, v_a_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v___x_1940_; 
lean_dec_ref_known(v___x_1939_, 1);
lean_inc_ref(v_body_1937_);
v___x_1940_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1829_, v_body_1937_, v_a_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
v___y_1917_ = v___x_1940_;
goto v___jp_1916_;
}
else
{
lean_dec_ref(v_g_1829_);
v___y_1917_ = v___x_1939_;
goto v___jp_1916_;
}
}
else
{
lean_dec_ref(v_g_1829_);
v___y_1917_ = v___x_1938_;
goto v___jp_1916_;
}
}
case 5:
{
lean_object* v_fn_1941_; lean_object* v_arg_1942_; lean_object* v___x_1943_; 
v_fn_1941_ = lean_ctor_get(v_e_1830_, 0);
v_arg_1942_ = lean_ctor_get(v_e_1830_, 1);
lean_inc_ref(v_fn_1941_);
lean_inc_ref(v_g_1829_);
v___x_1943_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1829_, v_fn_1941_, v_a_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v___x_1944_; 
lean_dec_ref_known(v___x_1943_, 1);
lean_inc_ref(v_arg_1942_);
v___x_1944_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1829_, v_arg_1942_, v_a_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
v___y_1917_ = v___x_1944_;
goto v___jp_1916_;
}
else
{
lean_dec_ref(v_g_1829_);
v___y_1917_ = v___x_1943_;
goto v___jp_1916_;
}
}
case 10:
{
lean_object* v_expr_1945_; lean_object* v___x_1946_; 
v_expr_1945_ = lean_ctor_get(v_e_1830_, 1);
lean_inc_ref(v_expr_1945_);
v___x_1946_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1829_, v_expr_1945_, v_a_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
v___y_1917_ = v___x_1946_;
goto v___jp_1916_;
}
case 11:
{
lean_object* v_struct_1947_; lean_object* v___x_1948_; 
v_struct_1947_ = lean_ctor_get(v_e_1830_, 2);
lean_inc_ref(v_struct_1947_);
v___x_1948_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1829_, v_struct_1947_, v_a_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
v___y_1917_ = v___x_1948_;
goto v___jp_1916_;
}
default: 
{
lean_object* v___x_1949_; 
lean_dec_ref(v_g_1829_);
v___x_1949_ = lean_box(0);
v_a_1884_ = v___x_1949_;
goto v___jp_1883_;
}
}
}
v___jp_1923_:
{
lean_object* v___x_1927_; 
lean_inc_ref(v_g_1829_);
v___x_1927_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1829_, v_d_1924_, v___y_1926_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v___x_1928_; 
lean_dec_ref_known(v___x_1927_, 1);
v___x_1928_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1829_, v_b_1925_, v___y_1926_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
v___y_1917_ = v___x_1928_;
goto v___jp_1916_;
}
else
{
lean_dec_ref(v_b_1925_);
lean_dec_ref(v_g_1829_);
v___y_1917_ = v___x_1927_;
goto v___jp_1916_;
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec_ref(v_e_1830_);
lean_dec_ref(v_g_1829_);
v_a_1950_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1921_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1921_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
else
{
lean_object* v_val_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec_ref(v_e_1830_);
lean_dec_ref(v_g_1829_);
v_val_1958_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1920_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_val_1958_);
lean_dec(v___x_1920_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set_tag(v___x_1960_, 0);
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_val_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
v___jp_1839_:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = lean_st_ref_put(v_a_1831_, v___y_1841_);
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v___y_1840_);
return v___x_1843_;
}
v___jp_1844_:
{
lean_object* v_size_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v_size_1848_ = lean_ctor_get(v___y_1846_, 0);
v___x_1849_ = lean_unsigned_to_nat(1u);
v___x_1850_ = lean_nat_add(v_size_1848_, v___x_1849_);
v___x_1851_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1846_, v___x_1850_, v_i_1847_, v_e_1830_, v___y_1845_);
lean_dec(v_i_1847_);
v___y_1840_ = v___y_1845_;
v___y_1841_ = v___x_1851_;
goto v___jp_1839_;
}
v___jp_1852_:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v___y_1854_, v_e_1830_);
switch(lean_obj_tag(v___x_1855_))
{
case 0:
{
lean_object* v_index_1856_; lean_object* v_size_1857_; lean_object* v___x_1858_; 
v_index_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_index_1856_);
lean_dec_ref_known(v___x_1855_, 3);
v_size_1857_ = lean_ctor_get(v___y_1854_, 0);
lean_inc(v_size_1857_);
v___x_1858_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1854_, v_size_1857_, v_index_1856_, v_e_1830_, v___y_1853_);
lean_dec(v_index_1856_);
v___y_1840_ = v___y_1853_;
v___y_1841_ = v___x_1858_;
goto v___jp_1839_;
}
case 1:
{
lean_object* v_index_1859_; 
v_index_1859_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_index_1859_);
lean_dec_ref_known(v___x_1855_, 1);
v___y_1845_ = v___y_1853_;
v___y_1846_ = v___y_1854_;
v_i_1847_ = v_index_1859_;
goto v___jp_1844_;
}
default: 
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_unsigned_to_nat(0u);
v___x_1861_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1854_, v___x_1860_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_index_1862_; 
v_index_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_index_1862_);
lean_dec_ref_known(v___x_1861_, 1);
v___y_1845_ = v___y_1853_;
v___y_1846_ = v___y_1854_;
v_i_1847_ = v_index_1862_;
goto v___jp_1844_;
}
else
{
lean_dec_ref(v_e_1830_);
v___y_1840_ = v___y_1853_;
v___y_1841_ = v___y_1854_;
goto v___jp_1839_;
}
}
}
}
v___jp_1863_:
{
lean_object* v_size_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v_size_1867_ = lean_ctor_get(v___y_1865_, 0);
v___x_1868_ = lean_unsigned_to_nat(1u);
v___x_1869_ = lean_nat_add(v_size_1867_, v___x_1868_);
v___x_1870_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1865_, v___x_1869_, v_i_1866_, v_e_1830_, v___y_1864_);
lean_dec(v_i_1866_);
v___y_1840_ = v___y_1864_;
v___y_1841_ = v___x_1870_;
goto v___jp_1839_;
}
v___jp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4___redArg(v___y_1873_);
lean_dec_ref(v___y_1873_);
v___x_1875_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v___x_1874_, v_e_1830_);
switch(lean_obj_tag(v___x_1875_))
{
case 0:
{
lean_object* v_index_1876_; lean_object* v_size_1877_; lean_object* v___x_1878_; 
v_index_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_index_1876_);
lean_dec_ref_known(v___x_1875_, 3);
v_size_1877_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_size_1877_);
v___x_1878_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1874_, v_size_1877_, v_index_1876_, v_e_1830_, v___y_1872_);
lean_dec(v_index_1876_);
v___y_1840_ = v___y_1872_;
v___y_1841_ = v___x_1878_;
goto v___jp_1839_;
}
case 1:
{
lean_object* v_index_1879_; 
v_index_1879_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_index_1879_);
lean_dec_ref_known(v___x_1875_, 1);
v___y_1864_ = v___y_1872_;
v___y_1865_ = v___x_1874_;
v_i_1866_ = v_index_1879_;
goto v___jp_1863_;
}
default: 
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_unsigned_to_nat(0u);
v___x_1881_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1874_, v___x_1880_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_index_1882_; 
v_index_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_index_1882_);
lean_dec_ref_known(v___x_1881_, 1);
v___y_1864_ = v___y_1872_;
v___y_1865_ = v___x_1874_;
v_i_1866_ = v_index_1882_;
goto v___jp_1863_;
}
else
{
lean_dec_ref(v_e_1830_);
v___y_1840_ = v___y_1872_;
v___y_1841_ = v___x_1874_;
goto v___jp_1839_;
}
}
}
}
v___jp_1883_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = lean_st_ref_take(v_a_1831_);
v___x_1886_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v___x_1885_, v_e_1830_);
switch(lean_obj_tag(v___x_1886_))
{
case 0:
{
lean_object* v_index_1887_; lean_object* v_size_1888_; lean_object* v___x_1889_; 
v_index_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_index_1887_);
lean_dec_ref_known(v___x_1886_, 3);
v_size_1888_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_size_1888_);
v___x_1889_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1885_, v_size_1888_, v_index_1887_, v_e_1830_, v_a_1884_);
lean_dec(v_index_1887_);
v___y_1840_ = v_a_1884_;
v___y_1841_ = v___x_1889_;
goto v___jp_1839_;
}
case 1:
{
lean_object* v_index_1890_; lean_object* v_size_1891_; lean_object* v_keyArray_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; 
v_index_1890_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_index_1890_);
lean_dec_ref_known(v___x_1886_, 1);
v_size_1891_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_size_1891_);
v_keyArray_1892_ = lean_ctor_get(v___x_1885_, 1);
lean_inc_ref(v_keyArray_1892_);
v___x_1893_ = lean_unsigned_to_nat(1u);
v___x_1894_ = lean_nat_add(v_size_1891_, v___x_1893_);
lean_dec(v_size_1891_);
v___x_1895_ = lean_array_get_size(v_keyArray_1892_);
lean_dec_ref(v_keyArray_1892_);
v___x_1896_ = lean_nat_dec_lt(v___x_1894_, v___x_1895_);
if (v___x_1896_ == 0)
{
lean_dec(v___x_1894_);
lean_dec(v_index_1890_);
v___y_1872_ = v_a_1884_;
v___y_1873_ = v___x_1885_;
goto v___jp_1871_;
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1897_ = lean_unsigned_to_nat(4u);
v___x_1898_ = lean_nat_mul(v___x_1894_, v___x_1897_);
v___x_1899_ = lean_unsigned_to_nat(3u);
v___x_1900_ = lean_nat_mul(v___x_1895_, v___x_1899_);
v___x_1901_ = lean_nat_dec_le(v___x_1898_, v___x_1900_);
lean_dec(v___x_1900_);
lean_dec(v___x_1898_);
if (v___x_1901_ == 0)
{
lean_dec(v___x_1894_);
lean_dec(v_index_1890_);
v___y_1872_ = v_a_1884_;
v___y_1873_ = v___x_1885_;
goto v___jp_1871_;
}
else
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1885_, v___x_1894_, v_index_1890_, v_e_1830_, v_a_1884_);
lean_dec(v_index_1890_);
v___y_1840_ = v_a_1884_;
v___y_1841_ = v___x_1902_;
goto v___jp_1839_;
}
}
}
default: 
{
lean_object* v_size_1903_; lean_object* v_keyArray_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; 
v_size_1903_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_size_1903_);
v_keyArray_1904_ = lean_ctor_get(v___x_1885_, 1);
lean_inc_ref(v_keyArray_1904_);
v___x_1905_ = lean_unsigned_to_nat(1u);
v___x_1906_ = lean_nat_add(v_size_1903_, v___x_1905_);
lean_dec(v_size_1903_);
v___x_1907_ = lean_array_get_size(v_keyArray_1904_);
lean_dec_ref(v_keyArray_1904_);
v___x_1908_ = lean_nat_dec_lt(v___x_1906_, v___x_1907_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; 
lean_dec(v___x_1906_);
v___x_1909_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4___redArg(v___x_1885_);
lean_dec(v___x_1885_);
v___y_1853_ = v_a_1884_;
v___y_1854_ = v___x_1909_;
goto v___jp_1852_;
}
else
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v___x_1910_ = lean_unsigned_to_nat(4u);
v___x_1911_ = lean_nat_mul(v___x_1906_, v___x_1910_);
lean_dec(v___x_1906_);
v___x_1912_ = lean_unsigned_to_nat(3u);
v___x_1913_ = lean_nat_mul(v___x_1907_, v___x_1912_);
v___x_1914_ = lean_nat_dec_le(v___x_1911_, v___x_1913_);
lean_dec(v___x_1913_);
lean_dec(v___x_1911_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4___redArg(v___x_1885_);
lean_dec(v___x_1885_);
v___y_1853_ = v_a_1884_;
v___y_1854_ = v___x_1915_;
goto v___jp_1852_;
}
else
{
v___y_1853_ = v_a_1884_;
v___y_1854_ = v___x_1885_;
goto v___jp_1852_;
}
}
}
}
}
v___jp_1916_:
{
if (lean_obj_tag(v___y_1917_) == 0)
{
lean_object* v_a_1918_; 
v_a_1918_ = lean_ctor_get(v___y_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___y_1917_, 1);
v_a_1884_ = v_a_1918_;
goto v___jp_1883_;
}
else
{
lean_dec_ref(v_e_1830_);
return v___y_1917_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1___boxed(lean_object* v_g_1966_, lean_object* v_e_1967_, lean_object* v_a_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1966_, v_e_1967_, v_a_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v_a_1968_);
return v_res_1976_;
}
}
static lean_object* _init_l_Lean_Expr_checkMaxShared___closed__0(void){
_start:
{
lean_object* v_cellCount_1977_; lean_object* v___x_1978_; 
v_cellCount_1977_ = lean_unsigned_to_nat(16u);
v___x_1978_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1977_);
return v___x_1978_;
}
}
static lean_object* _init_l_Lean_Expr_checkMaxShared___closed__1(void){
_start:
{
lean_object* v_cellCount_1979_; lean_object* v___x_1980_; 
v_cellCount_1979_ = lean_unsigned_to_nat(16u);
v___x_1980_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1979_);
return v___x_1980_;
}
}
static lean_object* _init_l_Lean_Expr_checkMaxShared___closed__2(void){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1981_ = lean_obj_once(&l_Lean_Expr_checkMaxShared___closed__1, &l_Lean_Expr_checkMaxShared___closed__1_once, _init_l_Lean_Expr_checkMaxShared___closed__1);
v___x_1982_ = lean_obj_once(&l_Lean_Expr_checkMaxShared___closed__0, &l_Lean_Expr_checkMaxShared___closed__0_once, _init_l_Lean_Expr_checkMaxShared___closed__0);
v___x_1983_ = lean_unsigned_to_nat(0u);
v___x_1984_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
lean_ctor_set(v___x_1984_, 1, v___x_1982_);
lean_ctor_set(v___x_1984_, 2, v___x_1981_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared(lean_object* v_e_1985_, lean_object* v_msg_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___f_1996_; lean_object* v___x_1997_; 
v___x_1994_ = lean_obj_once(&l_Lean_Expr_checkMaxShared___closed__2, &l_Lean_Expr_checkMaxShared___closed__2_once, _init_l_Lean_Expr_checkMaxShared___closed__2);
v___x_1995_ = lean_st_mk_ref(v___x_1994_);
v___f_1996_ = lean_alloc_closure((void*)(l_Lean_Expr_checkMaxShared___lam__0___boxed), 9, 1);
lean_closure_set(v___f_1996_, 0, v_msg_1986_);
v___x_1997_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v___f_1996_, v_e_1985_, v___x_1995_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2006_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2000_ = v___x_1997_;
v_isShared_2001_ = v_isSharedCheck_2006_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1997_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2006_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2004_; 
v___x_2002_ = lean_st_ref_get(v___x_1995_);
lean_dec(v___x_1995_);
lean_dec(v___x_2002_);
if (v_isShared_2001_ == 0)
{
v___x_2004_ = v___x_2000_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1998_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
else
{
lean_dec(v___x_1995_);
return v___x_1997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___boxed(lean_object* v_e_2007_, lean_object* v_msg_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_Expr_checkMaxShared(v_e_2007_, v_msg_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
lean_dec(v_a_2014_);
lean_dec_ref(v_a_2013_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(lean_object* v_00_u03b2_2017_, lean_object* v_x_2018_, lean_object* v_x_2019_){
_start:
{
lean_object* v___x_2020_; 
v___x_2020_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_x_2018_, v_x_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___boxed(lean_object* v_00_u03b2_2021_, lean_object* v_x_2022_, lean_object* v_x_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(v_00_u03b2_2021_, v_x_2022_, v_x_2023_);
lean_dec_ref(v_x_2023_);
lean_dec_ref(v_x_2022_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(lean_object* v_00_u03b2_2025_, lean_object* v_x_2026_, size_t v_x_2027_, lean_object* v_x_2028_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_2026_, v_x_2027_, v_x_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2030_, lean_object* v_x_2031_, lean_object* v_x_2032_, lean_object* v_x_2033_){
_start:
{
size_t v_x_10156__boxed_2034_; lean_object* v_res_2035_; 
v_x_10156__boxed_2034_ = lean_unbox_usize(v_x_2032_);
lean_dec(v_x_2032_);
v_res_2035_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(v_00_u03b2_2030_, v_x_2031_, v_x_10156__boxed_2034_, v_x_2033_);
lean_dec_ref(v_x_2033_);
lean_dec_ref(v_x_2031_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(lean_object* v_00_u03b2_2036_, lean_object* v_m_2037_, lean_object* v_a_2038_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_2037_, v_a_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2040_, lean_object* v_m_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(v_00_u03b2_2040_, v_m_2041_, v_a_2042_);
lean_dec_ref(v_a_2042_);
lean_dec_ref(v_m_2041_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3(lean_object* v_00_u03b2_2044_, lean_object* v_m_2045_, lean_object* v_query_2046_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v_m_2045_, v_query_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2048_, lean_object* v_m_2049_, lean_object* v_query_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3(v_00_u03b2_2048_, v_m_2049_, v_query_2050_);
lean_dec_ref(v_query_2050_);
lean_dec_ref(v_m_2049_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4(lean_object* v_00_u03b2_2052_, lean_object* v_m_2053_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4___redArg(v_m_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2055_, lean_object* v_m_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4(v_00_u03b2_2055_, v_m_2056_);
lean_dec_ref(v_m_2056_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2058_, lean_object* v_keys_2059_, lean_object* v_vals_2060_, lean_object* v_heq_2061_, lean_object* v_i_2062_, lean_object* v_k_2063_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_2059_, v_vals_2060_, v_i_2062_, v_k_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2065_, lean_object* v_keys_2066_, lean_object* v_vals_2067_, lean_object* v_heq_2068_, lean_object* v_i_2069_, lean_object* v_k_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(v_00_u03b2_2065_, v_keys_2066_, v_vals_2067_, v_heq_2068_, v_i_2069_, v_k_2070_);
lean_dec_ref(v_k_2070_);
lean_dec_ref(v_vals_2067_);
lean_dec_ref(v_keys_2066_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2072_, lean_object* v_m_2073_, lean_object* v_query_2074_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_m_2073_, v_query_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2076_, lean_object* v_m_2077_, lean_object* v_query_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(v_00_u03b2_2076_, v_m_2077_, v_query_2078_);
lean_dec_ref(v_query_2078_);
lean_dec_ref(v_m_2077_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2080_, lean_object* v_m_2081_, lean_object* v_query_2082_, lean_object* v_x_2083_, lean_object* v_x_2084_, lean_object* v_x_2085_, lean_object* v_x_2086_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_m_2081_, v_query_2082_, v_x_2083_, v_x_2084_, v_x_2085_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2088_, lean_object* v_m_2089_, lean_object* v_query_2090_, lean_object* v_x_2091_, lean_object* v_x_2092_, lean_object* v_x_2093_, lean_object* v_x_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(v_00_u03b2_2088_, v_m_2089_, v_query_2090_, v_x_2091_, v_x_2092_, v_x_2093_, v_x_2094_);
lean_dec_ref(v_query_2090_);
lean_dec_ref(v_m_2089_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_2096_, lean_object* v_init_2097_, lean_object* v_b_2098_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8___redArg(v_init_2097_, v_b_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2100_, lean_object* v_init_2101_, lean_object* v_b_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8(v_00_u03b2_2100_, v_init_2101_, v_b_2102_);
lean_dec_ref(v_b_2102_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8_spec__9(lean_object* v_00_u03b2_2104_, lean_object* v_b_2105_, lean_object* v_acc_2106_, lean_object* v_i_2107_){
_start:
{
lean_object* v___x_2108_; 
v___x_2108_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8_spec__9___redArg(v_b_2105_, v_acc_2106_, v_i_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8_spec__9___boxed(lean_object* v_00_u03b2_2109_, lean_object* v_b_2110_, lean_object* v_acc_2111_, lean_object* v_i_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__4_spec__8_spec__9(v_00_u03b2_2109_, v_b_2110_, v_acc_2111_, v_i_2112_);
lean_dec_ref(v_b_2110_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared(lean_object* v_mvarId_2114_, lean_object* v_msg_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_MVarId_getDecl(v_mvarId_2114_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v_type_2125_; lean_object* v___x_2126_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2123_, 1);
v_type_2125_ = lean_ctor_get(v_a_2124_, 2);
lean_inc_ref(v_type_2125_);
lean_dec(v_a_2124_);
v___x_2126_ = l_Lean_Expr_checkMaxShared(v_type_2125_, v_msg_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
return v___x_2126_;
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec_ref(v_msg_2115_);
v_a_2127_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2123_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2123_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared___boxed(lean_object* v_mvarId_2135_, lean_object* v_msg_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_MVarId_checkMaxShared(v_mvarId_2135_, v_msg_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
return v_res_2144_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(lean_object* v_x_2145_){
_start:
{
if (lean_obj_tag(v_x_2145_) == 0)
{
uint8_t v___x_2146_; 
v___x_2146_ = 0;
return v___x_2146_;
}
else
{
lean_object* v_head_2147_; lean_object* v_tail_2148_; uint8_t v___x_2149_; 
v_head_2147_ = lean_ctor_get(v_x_2145_, 0);
v_tail_2148_ = lean_ctor_get(v_x_2145_, 1);
v___x_2149_ = l_Lean_Level_isAlreadyNormalizedCheap(v_head_2147_);
if (v___x_2149_ == 0)
{
uint8_t v___x_2150_; 
v___x_2150_ = 1;
return v___x_2150_;
}
else
{
v_x_2145_ = v_tail_2148_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0___boxed(lean_object* v_x_2152_){
_start:
{
uint8_t v_res_2153_; lean_object* v_r_2154_; 
v_res_2153_ = l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(v_x_2152_);
lean_dec(v_x_2152_);
v_r_2154_ = lean_box(v_res_2153_);
return v_r_2154_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(lean_object* v_x_2155_){
_start:
{
switch(lean_obj_tag(v_x_2155_))
{
case 4:
{
lean_object* v_us_2156_; uint8_t v___x_2157_; 
v_us_2156_ = lean_ctor_get(v_x_2155_, 1);
v___x_2157_ = l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(v_us_2156_);
return v___x_2157_;
}
case 3:
{
lean_object* v_u_2158_; uint8_t v___x_2159_; 
v_u_2158_ = lean_ctor_get(v_x_2155_, 0);
v___x_2159_ = l_Lean_Level_isAlreadyNormalizedCheap(v_u_2158_);
if (v___x_2159_ == 0)
{
uint8_t v___x_2160_; 
v___x_2160_ = 1;
return v___x_2160_;
}
else
{
uint8_t v___x_2161_; 
v___x_2161_ = 0;
return v___x_2161_;
}
}
default: 
{
uint8_t v___x_2162_; 
v___x_2162_ = 0;
return v___x_2162_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0___boxed(lean_object* v_x_2163_){
_start:
{
uint8_t v_res_2164_; lean_object* v_r_2165_; 
v_res_2164_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(v_x_2163_);
lean_dec_ref(v_x_2163_);
v_r_2165_ = lean_box(v_res_2164_);
return v_r_2165_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(lean_object* v_e_2167_){
_start:
{
lean_object* v___f_2168_; lean_object* v___x_2169_; 
v___f_2168_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0));
v___x_2169_ = lean_find_expr(v___f_2168_, v_e_2167_);
if (lean_obj_tag(v___x_2169_) == 0)
{
uint8_t v___x_2170_; 
v___x_2170_ = 1;
return v___x_2170_;
}
else
{
uint8_t v___x_2171_; 
lean_dec_ref_known(v___x_2169_, 1);
v___x_2171_ = 0;
return v___x_2171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___boxed(lean_object* v_e_2172_){
_start:
{
uint8_t v_res_2173_; lean_object* v_r_2174_; 
v_res_2173_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_2172_);
lean_dec_ref(v_e_2172_);
v_r_2174_ = lean_box(v_res_2173_);
return v_r_2174_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(lean_object* v_a_2175_, lean_object* v_a_2176_){
_start:
{
if (lean_obj_tag(v_a_2175_) == 0)
{
lean_object* v___x_2177_; 
v___x_2177_ = l_List_reverse___redArg(v_a_2176_);
return v___x_2177_;
}
else
{
lean_object* v_head_2178_; lean_object* v_tail_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2188_; 
v_head_2178_ = lean_ctor_get(v_a_2175_, 0);
v_tail_2179_ = lean_ctor_get(v_a_2175_, 1);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_a_2175_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2181_ = v_a_2175_;
v_isShared_2182_ = v_isSharedCheck_2188_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_tail_2179_);
lean_inc(v_head_2178_);
lean_dec(v_a_2175_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2188_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2183_ = l_Lean_Level_normalize(v_head_2178_);
lean_dec(v_head_2178_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 1, v_a_2176_);
lean_ctor_set(v___x_2181_, 0, v___x_2183_);
v___x_2185_ = v___x_2181_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2183_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_a_2176_);
v___x_2185_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
v_a_2175_ = v_tail_2179_;
v_a_2176_ = v___x_2185_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0(lean_object* v_e_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___y_2196_; lean_object* v___y_2200_; 
switch(lean_obj_tag(v_e_2191_))
{
case 3:
{
lean_object* v_u_2203_; lean_object* v___x_2204_; size_t v___x_2205_; size_t v___x_2206_; uint8_t v___x_2207_; 
v_u_2203_ = lean_ctor_get(v_e_2191_, 0);
v___x_2204_ = l_Lean_Level_normalize(v_u_2203_);
v___x_2205_ = lean_ptr_addr(v_u_2203_);
v___x_2206_ = lean_ptr_addr(v___x_2204_);
v___x_2207_ = lean_usize_dec_eq(v___x_2205_, v___x_2206_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; 
lean_dec_ref_known(v_e_2191_, 1);
v___x_2208_ = l_Lean_Expr_sort___override(v___x_2204_);
v___y_2196_ = v___x_2208_;
goto v___jp_2195_;
}
else
{
lean_dec(v___x_2204_);
v___y_2196_ = v_e_2191_;
goto v___jp_2195_;
}
}
case 4:
{
lean_object* v_declName_2209_; lean_object* v_us_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; uint8_t v___x_2213_; 
v_declName_2209_ = lean_ctor_get(v_e_2191_, 0);
v_us_2210_ = lean_ctor_get(v_e_2191_, 1);
v___x_2211_ = lean_box(0);
lean_inc(v_us_2210_);
v___x_2212_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(v_us_2210_, v___x_2211_);
v___x_2213_ = l_ptrEqList___redArg(v_us_2210_, v___x_2212_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; 
lean_inc(v_declName_2209_);
lean_dec_ref_known(v_e_2191_, 2);
v___x_2214_ = l_Lean_Expr_const___override(v_declName_2209_, v___x_2212_);
v___y_2200_ = v___x_2214_;
goto v___jp_2199_;
}
else
{
lean_dec(v___x_2212_);
v___y_2200_ = v_e_2191_;
goto v___jp_2199_;
}
}
default: 
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_dec_ref(v_e_2191_);
v___x_2215_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___lam__0___closed__0));
v___x_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
return v___x_2216_;
}
}
v___jp_2195_:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___y_2196_);
v___x_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
return v___x_2198_;
}
v___jp_2199_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___y_2200_);
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
return v___x_2202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0___boxed(lean_object* v_e_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lean_Meta_Sym_normalizeLevels___lam__0(v_e_2217_, v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1(lean_object* v_e_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v_e_2222_);
v___x_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1___boxed(lean_object* v_e_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_Meta_Sym_normalizeLevels___lam__1(v_e_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_object* v_00_u03b1_2233_, lean_object* v_x_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = lean_apply_1(v_x_2234_, lean_box(0));
v___x_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2240_, lean_object* v_x_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(v_00_u03b1_2240_, v_x_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
return v_res_2245_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = l_Lean_maxRecDepthErrorMessage;
v___x_2252_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
return v___x_2252_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__3);
v___x_2254_ = l_Lean_MessageData_ofFormat(v___x_2253_);
return v___x_2254_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2255_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__4);
v___x_2256_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__2));
v___x_2257_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
lean_ctor_set(v___x_2257_, 1, v___x_2255_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_ref_2258_){
_start:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2260_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__5);
v___x_2261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2261_, 0, v_ref_2258_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_ref_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_2263_);
return v_res_2265_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2266_ = lean_box(0);
v___x_2267_ = l_Lean_interruptExceptionId;
v___x_2268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
lean_ctor_set(v___x_2268_, 1, v___x_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg(){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2270_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___closed__0);
v___x_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___boxed(lean_object* v___y_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg();
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg(lean_object* v_x_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___y_2280_; lean_object* v___y_2290_; lean_object* v___y_2291_; uint8_t v___y_2292_; lean_object* v___y_2293_; uint8_t v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v_fileName_2310_; lean_object* v_fileMap_2311_; lean_object* v_options_2312_; lean_object* v_currRecDepth_2313_; lean_object* v_maxRecDepth_2314_; lean_object* v_ref_2315_; lean_object* v_currNamespace_2316_; lean_object* v_openDecls_2317_; lean_object* v_initHeartbeats_2318_; lean_object* v_maxHeartbeats_2319_; lean_object* v_quotContext_2320_; lean_object* v_currMacroScope_2321_; uint8_t v_diag_2322_; lean_object* v_cancelTk_x3f_2323_; uint8_t v_suppressElabErrors_2324_; lean_object* v_inheritedTraceOptions_2325_; 
v_fileName_2310_ = lean_ctor_get(v___y_2276_, 0);
v_fileMap_2311_ = lean_ctor_get(v___y_2276_, 1);
v_options_2312_ = lean_ctor_get(v___y_2276_, 2);
v_currRecDepth_2313_ = lean_ctor_get(v___y_2276_, 3);
v_maxRecDepth_2314_ = lean_ctor_get(v___y_2276_, 4);
v_ref_2315_ = lean_ctor_get(v___y_2276_, 5);
v_currNamespace_2316_ = lean_ctor_get(v___y_2276_, 6);
v_openDecls_2317_ = lean_ctor_get(v___y_2276_, 7);
v_initHeartbeats_2318_ = lean_ctor_get(v___y_2276_, 8);
v_maxHeartbeats_2319_ = lean_ctor_get(v___y_2276_, 9);
v_quotContext_2320_ = lean_ctor_get(v___y_2276_, 10);
v_currMacroScope_2321_ = lean_ctor_get(v___y_2276_, 11);
v_diag_2322_ = lean_ctor_get_uint8(v___y_2276_, sizeof(void*)*14);
v_cancelTk_x3f_2323_ = lean_ctor_get(v___y_2276_, 12);
v_suppressElabErrors_2324_ = lean_ctor_get_uint8(v___y_2276_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2325_ = lean_ctor_get(v___y_2276_, 13);
if (lean_obj_tag(v_cancelTk_x3f_2323_) == 1)
{
lean_object* v_val_2331_; uint8_t v___x_2332_; 
v_val_2331_ = lean_ctor_get(v_cancelTk_x3f_2323_, 0);
v___x_2332_ = l_IO_CancelToken_isSet(v_val_2331_);
if (v___x_2332_ == 0)
{
goto v___jp_2326_;
}
else
{
lean_object* v___x_2333_; lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec_ref(v_x_2274_);
v___x_2333_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg();
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
else
{
goto v___jp_2326_;
}
v___jp_2279_:
{
if (lean_obj_tag(v___y_2280_) == 0)
{
return v___y_2280_;
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
v_a_2281_ = lean_ctor_get(v___y_2280_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___y_2280_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___y_2280_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___y_2280_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
v___jp_2289_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2306_ = lean_unsigned_to_nat(1u);
v___x_2307_ = lean_nat_add(v___y_2295_, v___x_2306_);
lean_inc_ref(v___y_2305_);
lean_inc(v___y_2290_);
lean_inc(v___y_2298_);
lean_inc(v___y_2303_);
lean_inc(v___y_2293_);
lean_inc(v___y_2299_);
lean_inc(v___y_2302_);
lean_inc(v___y_2296_);
lean_inc(v___y_2297_);
lean_inc_ref(v___y_2300_);
lean_inc_ref(v___y_2291_);
lean_inc_ref(v___y_2304_);
v___x_2308_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2308_, 0, v___y_2304_);
lean_ctor_set(v___x_2308_, 1, v___y_2291_);
lean_ctor_set(v___x_2308_, 2, v___y_2300_);
lean_ctor_set(v___x_2308_, 3, v___x_2307_);
lean_ctor_set(v___x_2308_, 4, v___y_2297_);
lean_ctor_set(v___x_2308_, 5, v___y_2301_);
lean_ctor_set(v___x_2308_, 6, v___y_2296_);
lean_ctor_set(v___x_2308_, 7, v___y_2302_);
lean_ctor_set(v___x_2308_, 8, v___y_2299_);
lean_ctor_set(v___x_2308_, 9, v___y_2293_);
lean_ctor_set(v___x_2308_, 10, v___y_2303_);
lean_ctor_set(v___x_2308_, 11, v___y_2298_);
lean_ctor_set(v___x_2308_, 12, v___y_2290_);
lean_ctor_set(v___x_2308_, 13, v___y_2305_);
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*14, v___y_2294_);
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*14 + 1, v___y_2292_);
lean_inc(v___y_2277_);
lean_inc(v___y_2275_);
v___x_2309_ = lean_apply_4(v_x_2274_, v___y_2275_, v___x_2308_, v___y_2277_, lean_box(0));
v___y_2280_ = v___x_2309_;
goto v___jp_2279_;
}
v___jp_2326_:
{
lean_object* v___x_2327_; uint8_t v___x_2328_; 
v___x_2327_ = lean_unsigned_to_nat(0u);
v___x_2328_ = lean_nat_dec_eq(v_maxRecDepth_2314_, v___x_2327_);
if (v___x_2328_ == 0)
{
uint8_t v___x_2329_; 
v___x_2329_ = lean_nat_dec_eq(v_currRecDepth_2313_, v_maxRecDepth_2314_);
if (v___x_2329_ == 0)
{
lean_inc(v_ref_2315_);
v___y_2290_ = v_cancelTk_x3f_2323_;
v___y_2291_ = v_fileMap_2311_;
v___y_2292_ = v_suppressElabErrors_2324_;
v___y_2293_ = v_maxHeartbeats_2319_;
v___y_2294_ = v_diag_2322_;
v___y_2295_ = v_currRecDepth_2313_;
v___y_2296_ = v_currNamespace_2316_;
v___y_2297_ = v_maxRecDepth_2314_;
v___y_2298_ = v_currMacroScope_2321_;
v___y_2299_ = v_initHeartbeats_2318_;
v___y_2300_ = v_options_2312_;
v___y_2301_ = v_ref_2315_;
v___y_2302_ = v_openDecls_2317_;
v___y_2303_ = v_quotContext_2320_;
v___y_2304_ = v_fileName_2310_;
v___y_2305_ = v_inheritedTraceOptions_2325_;
goto v___jp_2289_;
}
else
{
lean_object* v___x_2330_; 
lean_dec_ref(v_x_2274_);
lean_inc(v_ref_2315_);
v___x_2330_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_2315_);
v___y_2280_ = v___x_2330_;
goto v___jp_2279_;
}
}
else
{
lean_inc(v_ref_2315_);
v___y_2290_ = v_cancelTk_x3f_2323_;
v___y_2291_ = v_fileMap_2311_;
v___y_2292_ = v_suppressElabErrors_2324_;
v___y_2293_ = v_maxHeartbeats_2319_;
v___y_2294_ = v_diag_2322_;
v___y_2295_ = v_currRecDepth_2313_;
v___y_2296_ = v_currNamespace_2316_;
v___y_2297_ = v_maxRecDepth_2314_;
v___y_2298_ = v_currMacroScope_2321_;
v___y_2299_ = v_initHeartbeats_2318_;
v___y_2300_ = v_options_2312_;
v___y_2301_ = v_ref_2315_;
v___y_2302_ = v_openDecls_2317_;
v___y_2303_ = v_quotContext_2320_;
v___y_2304_ = v_fileName_2310_;
v___y_2305_ = v_inheritedTraceOptions_2325_;
goto v___jp_2289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_x_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg(v_x_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg(lean_object* v_m_2348_, lean_object* v_query_2349_, lean_object* v_x_2350_, lean_object* v_x_2351_, lean_object* v_x_2352_){
_start:
{
lean_object* v_zero_2353_; uint8_t v_isZero_2354_; 
v_zero_2353_ = lean_unsigned_to_nat(0u);
v_isZero_2354_ = lean_nat_dec_eq(v_x_2351_, v_zero_2353_);
if (v_isZero_2354_ == 1)
{
lean_dec(v_x_2352_);
lean_dec(v_x_2351_);
if (lean_obj_tag(v_x_2350_) == 0)
{
lean_object* v___x_2355_; 
v___x_2355_ = lean_box(2);
return v___x_2355_;
}
else
{
lean_object* v_val_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
v_val_2356_ = lean_ctor_get(v_x_2350_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v_x_2350_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v_x_2350_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_val_2356_);
lean_dec(v_x_2350_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_val_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
else
{
lean_object* v_keyArray_2364_; lean_object* v_valueArray_2365_; lean_object* v___x_2366_; uint8_t v_isSome_2367_; 
v_keyArray_2364_ = lean_ctor_get(v_m_2348_, 1);
v_valueArray_2365_ = lean_ctor_get(v_m_2348_, 2);
v___x_2366_ = lean_array_fget_borrowed(v_keyArray_2364_, v_x_2352_);
v_isSome_2367_ = lean_noption_is_some(v___x_2366_);
if (v_isSome_2367_ == 0)
{
lean_dec(v_x_2351_);
if (lean_obj_tag(v_x_2350_) == 0)
{
lean_object* v___x_2368_; 
v___x_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2368_, 0, v_x_2352_);
return v___x_2368_;
}
else
{
lean_object* v_val_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
lean_dec(v_x_2352_);
v_val_2369_ = lean_ctor_get(v_x_2350_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_x_2350_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v_x_2350_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_val_2369_);
lean_dec(v_x_2350_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_val_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
else
{
lean_object* v_one_2377_; lean_object* v_n_2378_; lean_object* v___y_2380_; 
v_one_2377_ = lean_unsigned_to_nat(1u);
v_n_2378_ = lean_nat_sub(v_x_2351_, v_one_2377_);
lean_dec(v_x_2351_);
if (v_isSome_2367_ == 0)
{
goto v___jp_2386_;
}
else
{
lean_object* v___x_2388_; uint8_t v_isSome_2389_; 
v___x_2388_ = lean_array_fget_borrowed(v_valueArray_2365_, v_x_2352_);
v_isSome_2389_ = lean_noption_is_some(v___x_2388_);
if (v_isSome_2389_ == 0)
{
goto v___jp_2386_;
}
else
{
lean_object* v_val_2390_; uint8_t v___x_2391_; 
lean_inc(v___x_2366_);
v_val_2390_ = lean_noption_get(v___x_2366_);
v___x_2391_ = l_Lean_ExprStructEq_beq(v_val_2390_, v_query_2349_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; lean_object* v___x_2393_; uint8_t v___x_2394_; 
lean_dec(v_val_2390_);
v___x_2392_ = lean_array_get_size(v_keyArray_2364_);
v___x_2393_ = lean_nat_add(v_x_2352_, v_one_2377_);
lean_dec(v_x_2352_);
v___x_2394_ = lean_nat_dec_lt(v___x_2393_, v___x_2392_);
if (v___x_2394_ == 0)
{
lean_dec(v___x_2393_);
v_x_2351_ = v_n_2378_;
v_x_2352_ = v_zero_2353_;
goto _start;
}
else
{
v_x_2351_ = v_n_2378_;
v_x_2352_ = v___x_2393_;
goto _start;
}
}
else
{
lean_object* v_val_2397_; lean_object* v___x_2398_; 
lean_dec(v_n_2378_);
lean_dec(v_x_2350_);
lean_inc(v___x_2388_);
v_val_2397_ = lean_noption_get(v___x_2388_);
v___x_2398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2398_, 0, v_x_2352_);
lean_ctor_set(v___x_2398_, 1, v_val_2390_);
lean_ctor_set(v___x_2398_, 2, v_val_2397_);
return v___x_2398_;
}
}
}
v___jp_2379_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; uint8_t v___x_2383_; 
v___x_2381_ = lean_array_get_size(v_keyArray_2364_);
v___x_2382_ = lean_nat_add(v_x_2352_, v_one_2377_);
lean_dec(v_x_2352_);
v___x_2383_ = lean_nat_dec_lt(v___x_2382_, v___x_2381_);
if (v___x_2383_ == 0)
{
lean_dec(v___x_2382_);
v_x_2350_ = v___y_2380_;
v_x_2351_ = v_n_2378_;
v_x_2352_ = v_zero_2353_;
goto _start;
}
else
{
v_x_2350_ = v___y_2380_;
v_x_2351_ = v_n_2378_;
v_x_2352_ = v___x_2382_;
goto _start;
}
}
v___jp_2386_:
{
if (lean_obj_tag(v_x_2350_) == 0)
{
lean_object* v___x_2387_; 
lean_inc(v_x_2352_);
v___x_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2387_, 0, v_x_2352_);
v___y_2380_ = v___x_2387_;
goto v___jp_2379_;
}
else
{
v___y_2380_ = v_x_2350_;
goto v___jp_2379_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg___boxed(lean_object* v_m_2399_, lean_object* v_query_2400_, lean_object* v_x_2401_, lean_object* v_x_2402_, lean_object* v_x_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg(v_m_2399_, v_query_2400_, v_x_2401_, v_x_2402_, v_x_2403_);
lean_dec_ref(v_query_2400_);
lean_dec_ref(v_m_2399_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg(lean_object* v_m_2405_, lean_object* v_query_2406_){
_start:
{
lean_object* v_keyArray_2407_; lean_object* v___x_2408_; uint64_t v___x_2409_; uint64_t v___x_2410_; uint64_t v___x_2411_; uint64_t v_fold_2412_; uint64_t v___x_2413_; uint64_t v___x_2414_; uint64_t v___x_2415_; size_t v___x_2416_; size_t v___x_2417_; size_t v___x_2418_; size_t v___x_2419_; size_t v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v_keyArray_2407_ = lean_ctor_get(v_m_2405_, 1);
v___x_2408_ = lean_array_get_size(v_keyArray_2407_);
v___x_2409_ = l_Lean_ExprStructEq_hash(v_query_2406_);
v___x_2410_ = 32ULL;
v___x_2411_ = lean_uint64_shift_right(v___x_2409_, v___x_2410_);
v_fold_2412_ = lean_uint64_xor(v___x_2409_, v___x_2411_);
v___x_2413_ = 16ULL;
v___x_2414_ = lean_uint64_shift_right(v_fold_2412_, v___x_2413_);
v___x_2415_ = lean_uint64_xor(v_fold_2412_, v___x_2414_);
v___x_2416_ = lean_uint64_to_usize(v___x_2415_);
v___x_2417_ = lean_usize_of_nat(v___x_2408_);
v___x_2418_ = ((size_t)1ULL);
v___x_2419_ = lean_usize_sub(v___x_2417_, v___x_2418_);
v___x_2420_ = lean_usize_land(v___x_2416_, v___x_2419_);
v___x_2421_ = lean_usize_to_nat(v___x_2420_);
v___x_2422_ = lean_box(0);
v___x_2423_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg(v_m_2405_, v_query_2406_, v___x_2422_, v___x_2408_, v___x_2421_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg___boxed(lean_object* v_m_2424_, lean_object* v_query_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg(v_m_2424_, v_query_2425_);
lean_dec_ref(v_query_2425_);
lean_dec_ref(v_m_2424_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13_spec__14___redArg(lean_object* v_b_2427_, lean_object* v_acc_2428_, lean_object* v_i_2429_){
_start:
{
lean_object* v___y_2431_; lean_object* v_keyArray_2439_; lean_object* v_valueArray_2440_; lean_object* v___x_2441_; uint8_t v___x_2442_; 
v_keyArray_2439_ = lean_ctor_get(v_b_2427_, 1);
v_valueArray_2440_ = lean_ctor_get(v_b_2427_, 2);
v___x_2441_ = lean_array_get_size(v_keyArray_2439_);
v___x_2442_ = lean_nat_dec_lt(v_i_2429_, v___x_2441_);
if (v___x_2442_ == 0)
{
lean_dec(v_i_2429_);
return v_acc_2428_;
}
else
{
lean_object* v___x_2443_; uint8_t v_isSome_2444_; 
v___x_2443_ = lean_array_fget_borrowed(v_keyArray_2439_, v_i_2429_);
v_isSome_2444_ = lean_noption_is_some(v___x_2443_);
if (v_isSome_2444_ == 0)
{
goto v___jp_2435_;
}
else
{
lean_object* v___x_2445_; uint8_t v_isSome_2446_; 
v___x_2445_ = lean_array_fget_borrowed(v_valueArray_2440_, v_i_2429_);
v_isSome_2446_ = lean_noption_is_some(v___x_2445_);
if (v_isSome_2446_ == 0)
{
goto v___jp_2435_;
}
else
{
lean_object* v_val_2447_; lean_object* v_val_2448_; lean_object* v_i_2450_; lean_object* v___x_2455_; 
lean_inc(v___x_2443_);
v_val_2447_ = lean_noption_get(v___x_2443_);
lean_inc(v___x_2445_);
v_val_2448_ = lean_noption_get(v___x_2445_);
v___x_2455_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg(v_acc_2428_, v_val_2447_);
switch(lean_obj_tag(v___x_2455_))
{
case 0:
{
lean_object* v_index_2456_; lean_object* v_size_2457_; lean_object* v___x_2458_; 
v_index_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_index_2456_);
lean_dec_ref_known(v___x_2455_, 3);
v_size_2457_ = lean_ctor_get(v_acc_2428_, 0);
lean_inc(v_size_2457_);
v___x_2458_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2428_, v_size_2457_, v_index_2456_, v_val_2447_, v_val_2448_);
lean_dec(v_index_2456_);
v___y_2431_ = v___x_2458_;
goto v___jp_2430_;
}
case 1:
{
lean_object* v_index_2459_; 
v_index_2459_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_index_2459_);
lean_dec_ref_known(v___x_2455_, 1);
v_i_2450_ = v_index_2459_;
goto v___jp_2449_;
}
default: 
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = lean_unsigned_to_nat(0u);
v___x_2461_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_2428_, v___x_2460_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_index_2462_; 
v_index_2462_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_index_2462_);
lean_dec_ref_known(v___x_2461_, 1);
v_i_2450_ = v_index_2462_;
goto v___jp_2449_;
}
else
{
lean_dec(v_val_2448_);
lean_dec(v_val_2447_);
v___y_2431_ = v_acc_2428_;
goto v___jp_2430_;
}
}
}
v___jp_2449_:
{
lean_object* v_size_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v_size_2451_ = lean_ctor_get(v_acc_2428_, 0);
v___x_2452_ = lean_unsigned_to_nat(1u);
v___x_2453_ = lean_nat_add(v_size_2451_, v___x_2452_);
v___x_2454_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2428_, v___x_2453_, v_i_2450_, v_val_2447_, v_val_2448_);
lean_dec(v_i_2450_);
v___y_2431_ = v___x_2454_;
goto v___jp_2430_;
}
}
}
}
v___jp_2430_:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = lean_unsigned_to_nat(1u);
v___x_2433_ = lean_nat_add(v_i_2429_, v___x_2432_);
lean_dec(v_i_2429_);
v_acc_2428_ = v___y_2431_;
v_i_2429_ = v___x_2433_;
goto _start;
}
v___jp_2435_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = lean_unsigned_to_nat(1u);
v___x_2437_ = lean_nat_add(v_i_2429_, v___x_2436_);
lean_dec(v_i_2429_);
v_i_2429_ = v___x_2437_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13_spec__14___redArg___boxed(lean_object* v_b_2463_, lean_object* v_acc_2464_, lean_object* v_i_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13_spec__14___redArg(v_b_2463_, v_acc_2464_, v_i_2465_);
lean_dec_ref(v_b_2463_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13___redArg(lean_object* v_init_2467_, lean_object* v_b_2468_){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = lean_unsigned_to_nat(0u);
v___x_2470_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13_spec__14___redArg(v_b_2468_, v_init_2467_, v___x_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13___redArg___boxed(lean_object* v_init_2471_, lean_object* v_b_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13___redArg(v_init_2471_, v_b_2472_);
lean_dec_ref(v_b_2472_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8___redArg(lean_object* v_m_2474_){
_start:
{
lean_object* v_keyArray_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v_cellCount_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v_target_2482_; lean_object* v___x_2483_; 
v_keyArray_2475_ = lean_ctor_get(v_m_2474_, 1);
v___x_2476_ = lean_array_get_size(v_keyArray_2475_);
v___x_2477_ = lean_unsigned_to_nat(2u);
v_cellCount_2478_ = lean_nat_mul(v___x_2476_, v___x_2477_);
v___x_2479_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_2478_);
v___x_2480_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2478_);
v___x_2481_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2478_);
v_target_2482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_2482_, 0, v___x_2479_);
lean_ctor_set(v_target_2482_, 1, v___x_2480_);
lean_ctor_set(v_target_2482_, 2, v___x_2481_);
v___x_2483_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13___redArg(v_target_2482_, v_m_2474_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8___redArg___boxed(lean_object* v_m_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8___redArg(v_m_2484_);
lean_dec_ref(v_m_2484_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2(lean_object* v_a_2486_, lean_object* v_e_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___y_2493_; lean_object* v___y_2496_; lean_object* v_i_2497_; lean_object* v___y_2513_; lean_object* v_i_2514_; lean_object* v___y_2520_; lean_object* v___x_2529_; 
v___x_2490_ = lean_st_ref_take(v_a_2486_);
v___x_2491_ = lean_box(0);
v___x_2529_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg(v___x_2490_, v_e_2487_);
switch(lean_obj_tag(v___x_2529_))
{
case 0:
{
lean_object* v_index_2530_; lean_object* v_size_2531_; lean_object* v___x_2532_; 
v_index_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_index_2530_);
lean_dec_ref_known(v___x_2529_, 3);
v_size_2531_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_size_2531_);
v___x_2532_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2490_, v_size_2531_, v_index_2530_, v_e_2487_, v_a_2488_);
lean_dec(v_index_2530_);
v___y_2493_ = v___x_2532_;
goto v___jp_2492_;
}
case 1:
{
lean_object* v_index_2533_; lean_object* v_size_2534_; lean_object* v_keyArray_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; 
v_index_2533_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_index_2533_);
lean_dec_ref_known(v___x_2529_, 1);
v_size_2534_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_size_2534_);
v_keyArray_2535_ = lean_ctor_get(v___x_2490_, 1);
lean_inc_ref(v_keyArray_2535_);
v___x_2536_ = lean_unsigned_to_nat(1u);
v___x_2537_ = lean_nat_add(v_size_2534_, v___x_2536_);
lean_dec(v_size_2534_);
v___x_2538_ = lean_array_get_size(v_keyArray_2535_);
lean_dec_ref(v_keyArray_2535_);
v___x_2539_ = lean_nat_dec_lt(v___x_2537_, v___x_2538_);
if (v___x_2539_ == 0)
{
lean_dec(v___x_2537_);
lean_dec(v_index_2533_);
goto v___jp_2502_;
}
else
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
v___x_2540_ = lean_unsigned_to_nat(4u);
v___x_2541_ = lean_nat_mul(v___x_2537_, v___x_2540_);
v___x_2542_ = lean_unsigned_to_nat(3u);
v___x_2543_ = lean_nat_mul(v___x_2538_, v___x_2542_);
v___x_2544_ = lean_nat_dec_le(v___x_2541_, v___x_2543_);
lean_dec(v___x_2543_);
lean_dec(v___x_2541_);
if (v___x_2544_ == 0)
{
lean_dec(v___x_2537_);
lean_dec(v_index_2533_);
goto v___jp_2502_;
}
else
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2490_, v___x_2537_, v_index_2533_, v_e_2487_, v_a_2488_);
lean_dec(v_index_2533_);
v___y_2493_ = v___x_2545_;
goto v___jp_2492_;
}
}
}
default: 
{
lean_object* v_size_2546_; lean_object* v_keyArray_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; 
v_size_2546_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_size_2546_);
v_keyArray_2547_ = lean_ctor_get(v___x_2490_, 1);
lean_inc_ref(v_keyArray_2547_);
v___x_2548_ = lean_unsigned_to_nat(1u);
v___x_2549_ = lean_nat_add(v_size_2546_, v___x_2548_);
lean_dec(v_size_2546_);
v___x_2550_ = lean_array_get_size(v_keyArray_2547_);
lean_dec_ref(v_keyArray_2547_);
v___x_2551_ = lean_nat_dec_lt(v___x_2549_, v___x_2550_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; 
lean_dec(v___x_2549_);
v___x_2552_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8___redArg(v___x_2490_);
lean_dec(v___x_2490_);
v___y_2520_ = v___x_2552_;
goto v___jp_2519_;
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; uint8_t v___x_2557_; 
v___x_2553_ = lean_unsigned_to_nat(4u);
v___x_2554_ = lean_nat_mul(v___x_2549_, v___x_2553_);
lean_dec(v___x_2549_);
v___x_2555_ = lean_unsigned_to_nat(3u);
v___x_2556_ = lean_nat_mul(v___x_2550_, v___x_2555_);
v___x_2557_ = lean_nat_dec_le(v___x_2554_, v___x_2556_);
lean_dec(v___x_2556_);
lean_dec(v___x_2554_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8___redArg(v___x_2490_);
lean_dec(v___x_2490_);
v___y_2520_ = v___x_2558_;
goto v___jp_2519_;
}
else
{
v___y_2520_ = v___x_2490_;
goto v___jp_2519_;
}
}
}
}
v___jp_2492_:
{
lean_object* v___x_2494_; 
v___x_2494_ = lean_st_ref_put(v_a_2486_, v___y_2493_);
return v___x_2491_;
}
v___jp_2495_:
{
lean_object* v_size_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v_size_2498_ = lean_ctor_get(v___y_2496_, 0);
v___x_2499_ = lean_unsigned_to_nat(1u);
v___x_2500_ = lean_nat_add(v_size_2498_, v___x_2499_);
v___x_2501_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2496_, v___x_2500_, v_i_2497_, v_e_2487_, v_a_2488_);
lean_dec(v_i_2497_);
v___y_2493_ = v___x_2501_;
goto v___jp_2492_;
}
v___jp_2502_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8___redArg(v___x_2490_);
lean_dec(v___x_2490_);
v___x_2504_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg(v___x_2503_, v_e_2487_);
switch(lean_obj_tag(v___x_2504_))
{
case 0:
{
lean_object* v_index_2505_; lean_object* v_size_2506_; lean_object* v___x_2507_; 
v_index_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_index_2505_);
lean_dec_ref_known(v___x_2504_, 3);
v_size_2506_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_size_2506_);
v___x_2507_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2503_, v_size_2506_, v_index_2505_, v_e_2487_, v_a_2488_);
lean_dec(v_index_2505_);
v___y_2493_ = v___x_2507_;
goto v___jp_2492_;
}
case 1:
{
lean_object* v_index_2508_; 
v_index_2508_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_index_2508_);
lean_dec_ref_known(v___x_2504_, 1);
v___y_2496_ = v___x_2503_;
v_i_2497_ = v_index_2508_;
goto v___jp_2495_;
}
default: 
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = lean_unsigned_to_nat(0u);
v___x_2510_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2503_, v___x_2509_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_index_2511_; 
v_index_2511_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_index_2511_);
lean_dec_ref_known(v___x_2510_, 1);
v___y_2496_ = v___x_2503_;
v_i_2497_ = v_index_2511_;
goto v___jp_2495_;
}
else
{
lean_dec_ref(v_a_2488_);
lean_dec_ref(v_e_2487_);
v___y_2493_ = v___x_2503_;
goto v___jp_2492_;
}
}
}
}
v___jp_2512_:
{
lean_object* v_size_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v_size_2515_ = lean_ctor_get(v___y_2513_, 0);
v___x_2516_ = lean_unsigned_to_nat(1u);
v___x_2517_ = lean_nat_add(v_size_2515_, v___x_2516_);
v___x_2518_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2513_, v___x_2517_, v_i_2514_, v_e_2487_, v_a_2488_);
lean_dec(v_i_2514_);
v___y_2493_ = v___x_2518_;
goto v___jp_2492_;
}
v___jp_2519_:
{
lean_object* v___x_2521_; 
v___x_2521_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg(v___y_2520_, v_e_2487_);
switch(lean_obj_tag(v___x_2521_))
{
case 0:
{
lean_object* v_index_2522_; lean_object* v_size_2523_; lean_object* v___x_2524_; 
v_index_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_index_2522_);
lean_dec_ref_known(v___x_2521_, 3);
v_size_2523_ = lean_ctor_get(v___y_2520_, 0);
lean_inc(v_size_2523_);
v___x_2524_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2520_, v_size_2523_, v_index_2522_, v_e_2487_, v_a_2488_);
lean_dec(v_index_2522_);
v___y_2493_ = v___x_2524_;
goto v___jp_2492_;
}
case 1:
{
lean_object* v_index_2525_; 
v_index_2525_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_index_2525_);
lean_dec_ref_known(v___x_2521_, 1);
v___y_2513_ = v___y_2520_;
v_i_2514_ = v_index_2525_;
goto v___jp_2512_;
}
default: 
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = lean_unsigned_to_nat(0u);
v___x_2527_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2520_, v___x_2526_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_index_2528_; 
v_index_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_index_2528_);
lean_dec_ref_known(v___x_2527_, 1);
v___y_2513_ = v___y_2520_;
v_i_2514_ = v_index_2528_;
goto v___jp_2512_;
}
else
{
lean_dec_ref(v_a_2488_);
lean_dec_ref(v_e_2487_);
v___y_2493_ = v___y_2520_;
goto v___jp_2492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2559_, lean_object* v_e_2560_, lean_object* v_a_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2(v_a_2559_, v_e_2560_, v_a_2561_);
lean_dec(v_a_2559_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg(lean_object* v_m_2564_, lean_object* v_query_2565_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg(v_m_2564_, v_query_2565_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_index_2567_; lean_object* v_key_2568_; lean_object* v_value_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
v_index_2567_ = lean_ctor_get(v___x_2566_, 0);
v_key_2568_ = lean_ctor_get(v___x_2566_, 1);
v_value_2569_ = lean_ctor_get(v___x_2566_, 2);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2566_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_value_2569_);
lean_inc(v_key_2568_);
lean_inc(v_index_2567_);
lean_dec(v___x_2566_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_index_2567_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_key_2568_);
lean_ctor_set(v_reuseFailAlloc_2575_, 2, v_value_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
else
{
lean_object* v___x_2577_; 
lean_dec(v___x_2566_);
v___x_2577_ = lean_box(1);
return v___x_2577_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg___boxed(lean_object* v_m_2578_, lean_object* v_query_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg(v_m_2578_, v_query_2579_);
lean_dec_ref(v_query_2579_);
lean_dec_ref(v_m_2578_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg(lean_object* v_m_2581_, lean_object* v_a_2582_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg(v_m_2581_, v_a_2582_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_value_2584_; lean_object* v___x_2585_; 
v_value_2584_ = lean_ctor_get(v___x_2583_, 2);
lean_inc(v_value_2584_);
lean_dec_ref_known(v___x_2583_, 3);
v___x_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2585_, 0, v_value_2584_);
return v___x_2585_;
}
else
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_box(0);
return v___x_2586_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_m_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg(v_m_2587_, v_a_2588_);
lean_dec_ref(v_a_2588_);
lean_dec_ref(v_m_2587_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2590_, lean_object* v_x_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2595_ = lean_apply_1(v_x_2591_, lean_box(0));
v___x_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2597_, lean_object* v_x_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(v_00_u03b1_2597_, v_x_2598_, v___y_2599_, v___y_2600_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
return v_res_2602_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2604_; lean_object* v_dummy_2605_; 
v___x_2604_ = lean_box(0);
v_dummy_2605_ = l_Lean_Expr_sort___override(v___x_2604_);
return v_dummy_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(lean_object* v_pre_2606_, lean_object* v_post_2607_, size_t v_sz_2608_, size_t v_i_2609_, lean_object* v_bs_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
uint8_t v___x_2615_; 
v___x_2615_ = lean_usize_dec_lt(v_i_2609_, v_sz_2608_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; 
lean_dec_ref(v_post_2607_);
lean_dec_ref(v_pre_2606_);
v___x_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2616_, 0, v_bs_2610_);
return v___x_2616_;
}
else
{
lean_object* v_v_2617_; lean_object* v___x_2618_; 
v_v_2617_ = lean_array_uget_borrowed(v_bs_2610_, v_i_2609_);
lean_inc(v_v_2617_);
lean_inc_ref(v_post_2607_);
lean_inc_ref(v_pre_2606_);
v___x_2618_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2606_, v_post_2607_, v_v_2617_, v___y_2611_, v___y_2612_, v___y_2613_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2620_; lean_object* v_bs_x27_2621_; size_t v___x_2622_; size_t v___x_2623_; lean_object* v___x_2624_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2618_, 1);
v___x_2620_ = lean_unsigned_to_nat(0u);
v_bs_x27_2621_ = lean_array_uset(v_bs_2610_, v_i_2609_, v___x_2620_);
v___x_2622_ = ((size_t)1ULL);
v___x_2623_ = lean_usize_add(v_i_2609_, v___x_2622_);
v___x_2624_ = lean_array_uset(v_bs_x27_2621_, v_i_2609_, v_a_2619_);
v_i_2609_ = v___x_2623_;
v_bs_2610_ = v___x_2624_;
goto _start;
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
lean_dec_ref(v_bs_2610_);
lean_dec_ref(v_post_2607_);
lean_dec_ref(v_pre_2606_);
v_a_2626_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2618_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2618_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(lean_object* v_pre_2634_, lean_object* v_post_2635_, lean_object* v_x_2636_, lean_object* v_x_2637_, lean_object* v_x_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
if (lean_obj_tag(v_x_2636_) == 5)
{
lean_object* v_fn_2643_; lean_object* v_arg_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v_fn_2643_ = lean_ctor_get(v_x_2636_, 0);
lean_inc_ref(v_fn_2643_);
v_arg_2644_ = lean_ctor_get(v_x_2636_, 1);
lean_inc_ref(v_arg_2644_);
lean_dec_ref_known(v_x_2636_, 2);
v___x_2645_ = lean_array_set(v_x_2637_, v_x_2638_, v_arg_2644_);
v___x_2646_ = lean_unsigned_to_nat(1u);
v___x_2647_ = lean_nat_sub(v_x_2638_, v___x_2646_);
lean_dec(v_x_2638_);
v_x_2636_ = v_fn_2643_;
v_x_2637_ = v___x_2645_;
v_x_2638_ = v___x_2647_;
goto _start;
}
else
{
lean_object* v___x_2649_; 
lean_dec(v_x_2638_);
lean_inc_ref(v_post_2635_);
lean_inc_ref(v_pre_2634_);
v___x_2649_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2634_, v_post_2635_, v_x_2636_, v___y_2639_, v___y_2640_, v___y_2641_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; size_t v_sz_2651_; size_t v___x_2652_; lean_object* v___x_2653_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref_known(v___x_2649_, 1);
v_sz_2651_ = lean_array_size(v_x_2637_);
v___x_2652_ = ((size_t)0ULL);
lean_inc_ref(v_post_2635_);
lean_inc_ref(v_pre_2634_);
v___x_2653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_2634_, v_post_2635_, v_sz_2651_, v___x_2652_, v_x_2637_, v___y_2639_, v___y_2640_, v___y_2641_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___x_2653_, 1);
v___x_2655_ = l_Lean_mkAppN(v_a_2650_, v_a_2654_);
lean_dec(v_a_2654_);
v___x_2656_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2634_, v_post_2635_, v___x_2655_, v___y_2639_, v___y_2640_, v___y_2641_);
return v___x_2656_;
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
lean_dec(v_a_2650_);
lean_dec_ref(v_post_2635_);
lean_dec_ref(v_pre_2634_);
v_a_2657_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2653_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2653_);
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
else
{
lean_dec_ref(v_x_2637_);
lean_dec_ref(v_post_2635_);
lean_dec_ref(v_pre_2634_);
return v___x_2649_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(lean_object* v___x_2665_, lean_object* v_pre_2666_, lean_object* v_e_2667_, lean_object* v_post_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v___y_2674_; uint8_t v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; uint8_t v___y_2681_; lean_object* v___y_2691_; uint8_t v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; uint8_t v___y_2696_; uint8_t v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; uint8_t v___y_2709_; lean_object* v___x_2716_; 
v___x_2716_ = l_Lean_Core_checkSystem(v___x_2665_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v___x_2717_; 
lean_dec_ref_known(v___x_2716_, 1);
lean_inc_ref(v_pre_2666_);
lean_inc(v___y_2671_);
lean_inc_ref(v___y_2670_);
lean_inc_ref(v_e_2667_);
v___x_2717_ = lean_apply_4(v_pre_2666_, v_e_2667_, v___y_2670_, v___y_2671_, lean_box(0));
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2807_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2720_ = v___x_2717_;
v_isShared_2721_ = v_isSharedCheck_2807_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2807_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___y_2723_; 
switch(lean_obj_tag(v_a_2718_))
{
case 0:
{
lean_object* v_e_2797_; lean_object* v___x_2799_; 
lean_dec_ref(v_post_2668_);
lean_dec_ref(v_e_2667_);
lean_dec_ref(v_pre_2666_);
v_e_2797_ = lean_ctor_get(v_a_2718_, 0);
lean_inc_ref(v_e_2797_);
lean_dec_ref_known(v_a_2718_, 1);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v_e_2797_);
v___x_2799_ = v___x_2720_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_e_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
case 1:
{
lean_object* v_e_2801_; lean_object* v___x_2802_; 
lean_del_object(v___x_2720_);
lean_dec_ref(v_e_2667_);
v_e_2801_ = lean_ctor_get(v_a_2718_, 0);
lean_inc_ref(v_e_2801_);
lean_dec_ref_known(v_a_2718_, 1);
lean_inc_ref(v_post_2668_);
lean_inc_ref(v_pre_2666_);
v___x_2802_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2666_, v_post_2668_, v_e_2801_, v___y_2669_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2804_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2802_, 1);
v___x_2804_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2666_, v_post_2668_, v_a_2803_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2804_;
}
else
{
lean_dec_ref(v_post_2668_);
lean_dec_ref(v_pre_2666_);
return v___x_2802_;
}
}
default: 
{
lean_object* v_e_x3f_2805_; 
lean_del_object(v___x_2720_);
v_e_x3f_2805_ = lean_ctor_get(v_a_2718_, 0);
lean_inc(v_e_x3f_2805_);
lean_dec_ref_known(v_a_2718_, 1);
if (lean_obj_tag(v_e_x3f_2805_) == 0)
{
v___y_2723_ = v_e_2667_;
goto v___jp_2722_;
}
else
{
lean_object* v_val_2806_; 
lean_dec_ref(v_e_2667_);
v_val_2806_ = lean_ctor_get(v_e_x3f_2805_, 0);
lean_inc(v_val_2806_);
lean_dec_ref_known(v_e_x3f_2805_, 1);
v___y_2723_ = v_val_2806_;
goto v___jp_2722_;
}
}
}
v___jp_2722_:
{
switch(lean_obj_tag(v___y_2723_))
{
case 7:
{
lean_object* v_binderName_2724_; lean_object* v_binderType_2725_; lean_object* v_body_2726_; uint8_t v_binderInfo_2727_; lean_object* v___x_2728_; 
v_binderName_2724_ = lean_ctor_get(v___y_2723_, 0);
lean_inc(v_binderName_2724_);
v_binderType_2725_ = lean_ctor_get(v___y_2723_, 1);
v_body_2726_ = lean_ctor_get(v___y_2723_, 2);
v_binderInfo_2727_ = lean_ctor_get_uint8(v___y_2723_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2725_);
lean_inc_ref(v_post_2668_);
lean_inc_ref(v_pre_2666_);
v___x_2728_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2666_, v_post_2668_, v_binderType_2725_, v___y_2669_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v_a_2729_; lean_object* v___x_2730_; 
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_a_2729_);
lean_dec_ref_known(v___x_2728_, 1);
lean_inc_ref(v_body_2726_);
lean_inc_ref(v_post_2668_);
lean_inc_ref(v_pre_2666_);
v___x_2730_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2666_, v_post_2668_, v_body_2726_, v___y_2669_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; size_t v___x_2732_; size_t v___x_2733_; uint8_t v___x_2734_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___x_2730_, 1);
v___x_2732_ = lean_ptr_addr(v_binderType_2725_);
v___x_2733_ = lean_ptr_addr(v_a_2729_);
v___x_2734_ = lean_usize_dec_eq(v___x_2732_, v___x_2733_);
if (v___x_2734_ == 0)
{
v___y_2704_ = v_binderInfo_2727_;
v___y_2705_ = v_binderName_2724_;
v___y_2706_ = v_a_2729_;
v___y_2707_ = v___y_2723_;
v___y_2708_ = v_a_2731_;
v___y_2709_ = v___x_2734_;
goto v___jp_2703_;
}
else
{
size_t v___x_2735_; size_t v___x_2736_; uint8_t v___x_2737_; 
v___x_2735_ = lean_ptr_addr(v_body_2726_);
v___x_2736_ = lean_ptr_addr(v_a_2731_);
v___x_2737_ = lean_usize_dec_eq(v___x_2735_, v___x_2736_);
v___y_2704_ = v_binderInfo_2727_;
v___y_2705_ = v_binderName_2724_;
v___y_2706_ = v_a_2729_;
v___y_2707_ = v___y_2723_;
v___y_2708_ = v_a_2731_;
v___y_2709_ = v___x_2737_;
goto v___jp_2703_;
}
}
else
{
lean_dec(v_a_2729_);
lean_dec_ref_known(v___y_2723_, 3);
lean_dec(v_binderName_2724_);
lean_dec_ref(v_post_2668_);
lean_dec_ref(v_pre_2666_);
return v___x_2730_;
}
}
else
{
lean_dec_ref_known(v___y_2723_, 3);
lean_dec(v_binderName_2724_);
lean_dec_ref(v_post_2668_);
lean_dec_ref(v_pre_2666_);
return v___x_2728_;
}
}
case 6:
{
lean_object* v_binderName_2738_; lean_object* v_binderType_2739_; lean_object* v_body_2740_; uint8_t v_binderInfo_2741_; lean_object* v___x_2742_; 
v_binderName_2738_ = lean_ctor_get(v___y_2723_, 0);
lean_inc(v_binderName_2738_);
v_binderType_2739_ = lean_ctor_get(v___y_2723_, 1);
v_body_2740_ = lean_ctor_get(v___y_2723_, 2);
v_binderInfo_2741_ = lean_ctor_get_uint8(v___y_2723_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2739_);
lean_inc_ref(v_post_2668_);
lean_inc_ref(v_pre_2666_);
v___x_2742_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2666_, v_post_2668_, v_binderType_2739_, v___y_2669_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2744_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref_known(v___x_2742_, 1);
lean_inc_ref(v_body_2740_);
lean_inc_ref(v_post_2668_);
lean_inc_ref(v_pre_2666_);
v___x_2744_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2666_, v_post_2668_, v_body_2740_, v___y_2669_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; size_t v___x_2746_; size_t v___x_2747_; uint8_t v___x_2748_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref_known(v___x_2744_, 1);
v___x_2746_ = lean_ptr_addr(v_binderType_2739_);
v___x_2747_ = lean_ptr_addr(v_a_2743_);
v___x_2748_ = lean_usize_dec_eq(v___x_2746_, v___x_2747_);
if (v___x_2748_ == 0)
{
v___y_2691_ = v_a_2745_;
v___y_2692_ = v_binderInfo_2741_;
v___y_2693_ = v_binderName_2738_;
v___y_2694_ = v_a_2743_;
v___y_2695_ = v___y_2723_;
v___y_2696_ = v___x_2748_;
goto v___jp_2690_;
}
else
{
size_t v___x_2749_; size_t v___x_2750_; uint8_t v___x_2751_; 
v___x_2749_ = lean_ptr_addr(v_body_2740_);
v___x_2750_ = lean_ptr_addr(v_a_2745_);
v___x_2751_ = lean_usize_dec_eq(v___x_2749_, v___x_2750_);
v___y_2691_ = v_a_2745_;
v___y_2692_ = v_binderInfo_2741_;
v___y_2693_ = v_binderName_2738_;
v___y_2694_ = v_a_2743_;
v___y_2695_ = v___y_2723_;
v___y_2696_ = v___x_2751_;
goto v___jp_2690_;
}
}
else
{
lean_dec(v_a_2743_);
lean_dec(v_binderName_2738_);
lean_dec_ref_known(v___y_2723_, 3);
lean_dec_ref(v_post_2668_);
lean_dec_ref(v_pre_2666_);
return v___x_2744_;
}
}
else
{
lean_dec_ref_known(v___y_2723_, 3);
lean_dec(v_binderName_2738_);
lean_dec_ref(v_post_2668_);
lean_dec_ref(v_pre_2666_);
return v___x_2742_;
}
}
case 8:
{
lean_object* v_declName_2752_; lean_object* v_type_2753_; lean_object* v_value_2754_; lean_object* v_body_2755_; uint8_t v_nondep_2756_; lean_object* v___x_2757_; 
v_declName_2752_ = lean_ctor_get(v___y_2723_, 0);
lean_inc(v_declName_2752_);
v_type_2753_ = lean_ctor_get(v___y_2723_, 1);
v_value_2754_ = lean_ctor_get(v___y_2723_, 2);
v_body_2755_ = lean_ctor_get(v___y_2723_, 3);
lean_inc_ref(v_body_2755_);
v_nondep_2756_ = lean_ctor_get_uint8(v___y_2723_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2753_);
lean_inc_ref(v_post_2668_);
lean_inc_ref(v_pre_2666_);
v___x_2757_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2666_, v_post_2668_, v_type_2753_, v___y_2669_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v___x_2759_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_a_2758_);
lean_dec_ref_known(v___x_2757_, 1);
lean_inc_ref(v_value_2754_);
lean_inc_ref(v_post_2668_);
lean_inc_ref(v_pre_2666_);
v___x_2759_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2666_, v_post_2668_, v_value_2754_, v___y_2669_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2761_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2759_, 1);
lean_inc_ref(v_body_2755_);
lean_inc_ref(v_post_2668_);
lean_inc_ref(v_pre_2666_);
v___x_2761_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2666_, v_post_2668_, v_body_2755_, v___y_2669_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; size_t v___x_2763_; size_t v___x_2764_; uint8_t v___x_2765_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2762_);
lean_dec_ref_known(v___x_2761_, 1);
v___x_2763_ = lean_ptr_addr(v_type_2753_);
v___x_2764_ = lean_ptr_addr(v_a_2758_);
v___x_2765_ = lean_usize_dec_eq(v___x_2763_, v___x_2764_);
if (v___x_2765_ == 0)
{
v___y_2674_ = v_a_2762_;
v___y_2675_ = v_nondep_2756_;
v___y_2676_ = v_body_2755_;
v___y_2677_ = v___y_2723_;
v___y_2678_ = v_a_2758_;
v___y_2679_ = v_a_2760_;
v___y_2680_ = v_declName_2752_;
v___y_2681_ = v___x_2765_;
goto v___jp_2673_;
}
else
{
size_t v___x_2766_; size_t v___x_2767_; uint8_t v___x_2768_; 
v___x_2766_ = lean_ptr_addr(v_value_2754_);
v___x_2767_ = lean_ptr_addr(v_a_2760_);
v___x_2768_ = lean_usize_dec_eq(v___x_2766_, v___x_2767_);
v___y_2674_ = v_a_2762_;
v___y_2675_ = v_nondep_2756_;
v___y_2676_ = v_body_2755_;
v___y_2677_ = v___y_2723_;
v___y_2678_ = v_a_2758_;
v___y_2679_ = v_a_2760_;
v___y_2680_ = v_declName_2752_;
v___y_2681_ = v___x_2768_;
goto v___jp_2673_;
}
}
else
{
lean_dec(v_a_2760_);
lean_dec(v_a_2758_);
lean_dec_ref(v_body_2755_);
lean_dec_ref_known(v___y_2723_, 4);
lean_dec(v_declName_2752_);
lean_dec_ref(v_post_2668_);
lean_dec_ref(v_pre_2666_);
return v___x_2761_;
}
}
else
{
lean_dec(v_a_2758_);
lean_dec_ref(v_body_2755_);
lean_dec_ref_known(v___y_2723_, 4);
lean_dec(v_declName_2752_);
lean_dec_ref(v_post_2668_);
lean_dec_ref(v_pre_2666_);
return v___x_2759_;
}
}
else
{
lean_dec_ref(v_body_2755_);
lean_dec_ref_known(v___y_2723_, 4);
lean_dec(v_declName_2752_);
lean_dec_ref(v_post_2668_);
lean_dec_ref(v_pre_2666_);
return v___x_2757_;
}
}
case 5:
{
lean_object* v_dummy_2769_; lean_object* v_nargs_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v_dummy_2769_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0);
v_nargs_2770_ = l_Lean_Expr_getAppNumArgs(v___y_2723_);
lean_inc(v_nargs_2770_);
v___x_2771_ = lean_mk_array(v_nargs_2770_, v_dummy_2769_);
v___x_2772_ = lean_unsigned_to_nat(1u);
v___x_2773_ = lean_nat_sub(v_nargs_2770_, v___x_2772_);
lean_dec(v_nargs_2770_);
v___x_2774_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(v_pre_2666_, v_post_2668_, v___y_2723_, v___x_2771_, v___x_2773_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2774_;
}
case 10:
{
lean_object* v_data_2775_; lean_object* v_expr_2776_; lean_object* v___x_2777_; 
v_data_2775_ = lean_ctor_get(v___y_2723_, 0);
v_expr_2776_ = lean_ctor_get(v___y_2723_, 1);
lean_inc_ref(v_expr_2776_);
lean_inc_ref(v_post_2668_);
lean_inc_ref(v_pre_2666_);
v___x_2777_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2666_, v_post_2668_, v_expr_2776_, v___y_2669_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; size_t v___x_2779_; size_t v___x_2780_; uint8_t v___x_2781_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2778_);
lean_dec_ref_known(v___x_2777_, 1);
v___x_2779_ = lean_ptr_addr(v_expr_2776_);
v___x_2780_ = lean_ptr_addr(v_a_2778_);
v___x_2781_ = lean_usize_dec_eq(v___x_2779_, v___x_2780_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
lean_inc(v_data_2775_);
lean_dec_ref_known(v___y_2723_, 2);
v___x_2782_ = l_Lean_Expr_mdata___override(v_data_2775_, v_a_2778_);
v___x_2783_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2666_, v_post_2668_, v___x_2782_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2783_;
}
else
{
lean_object* v___x_2784_; 
lean_dec(v_a_2778_);
v___x_2784_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2666_, v_post_2668_, v___y_2723_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2784_;
}
}
else
{
lean_dec_ref_known(v___y_2723_, 2);
lean_dec_ref(v_post_2668_);
lean_dec_ref(v_pre_2666_);
return v___x_2777_;
}
}
case 11:
{
lean_object* v_typeName_2785_; lean_object* v_idx_2786_; lean_object* v_struct_2787_; lean_object* v___x_2788_; 
v_typeName_2785_ = lean_ctor_get(v___y_2723_, 0);
v_idx_2786_ = lean_ctor_get(v___y_2723_, 1);
v_struct_2787_ = lean_ctor_get(v___y_2723_, 2);
lean_inc_ref(v_struct_2787_);
lean_inc_ref(v_post_2668_);
lean_inc_ref(v_pre_2666_);
v___x_2788_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2666_, v_post_2668_, v_struct_2787_, v___y_2669_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; size_t v___x_2790_; size_t v___x_2791_; uint8_t v___x_2792_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2788_, 1);
v___x_2790_ = lean_ptr_addr(v_struct_2787_);
v___x_2791_ = lean_ptr_addr(v_a_2789_);
v___x_2792_ = lean_usize_dec_eq(v___x_2790_, v___x_2791_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
lean_inc(v_idx_2786_);
lean_inc(v_typeName_2785_);
lean_dec_ref_known(v___y_2723_, 3);
v___x_2793_ = l_Lean_Expr_proj___override(v_typeName_2785_, v_idx_2786_, v_a_2789_);
v___x_2794_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2666_, v_post_2668_, v___x_2793_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2794_;
}
else
{
lean_object* v___x_2795_; 
lean_dec(v_a_2789_);
v___x_2795_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2666_, v_post_2668_, v___y_2723_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2795_;
}
}
else
{
lean_dec_ref_known(v___y_2723_, 3);
lean_dec_ref(v_post_2668_);
lean_dec_ref(v_pre_2666_);
return v___x_2788_;
}
}
default: 
{
lean_object* v___x_2796_; 
v___x_2796_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2666_, v_post_2668_, v___y_2723_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2796_;
}
}
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_dec_ref(v_post_2668_);
lean_dec_ref(v_e_2667_);
lean_dec_ref(v_pre_2666_);
v_a_2808_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2717_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2717_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
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
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec_ref(v_post_2668_);
lean_dec_ref(v_e_2667_);
lean_dec_ref(v_pre_2666_);
v_a_2816_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2716_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2716_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
v___jp_2673_:
{
if (v___y_2681_ == 0)
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
lean_dec_ref(v___y_2677_);
lean_dec_ref(v___y_2676_);
v___x_2682_ = l_Lean_Expr_letE___override(v___y_2680_, v___y_2678_, v___y_2679_, v___y_2674_, v___y_2675_);
v___x_2683_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2666_, v_post_2668_, v___x_2682_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2683_;
}
else
{
size_t v___x_2684_; size_t v___x_2685_; uint8_t v___x_2686_; 
v___x_2684_ = lean_ptr_addr(v___y_2676_);
lean_dec_ref(v___y_2676_);
v___x_2685_ = lean_ptr_addr(v___y_2674_);
v___x_2686_ = lean_usize_dec_eq(v___x_2684_, v___x_2685_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
lean_dec_ref(v___y_2677_);
v___x_2687_ = l_Lean_Expr_letE___override(v___y_2680_, v___y_2678_, v___y_2679_, v___y_2674_, v___y_2675_);
v___x_2688_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2666_, v_post_2668_, v___x_2687_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2688_;
}
else
{
lean_object* v___x_2689_; 
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec_ref(v___y_2674_);
v___x_2689_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2666_, v_post_2668_, v___y_2677_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2689_;
}
}
}
v___jp_2690_:
{
if (v___y_2696_ == 0)
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
lean_dec_ref(v___y_2695_);
v___x_2697_ = l_Lean_Expr_lam___override(v___y_2693_, v___y_2694_, v___y_2691_, v___y_2692_);
v___x_2698_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2666_, v_post_2668_, v___x_2697_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2698_;
}
else
{
uint8_t v___x_2699_; 
v___x_2699_ = l_Lean_instBEqBinderInfo_beq(v___y_2692_, v___y_2692_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
lean_dec_ref(v___y_2695_);
v___x_2700_ = l_Lean_Expr_lam___override(v___y_2693_, v___y_2694_, v___y_2691_, v___y_2692_);
v___x_2701_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2666_, v_post_2668_, v___x_2700_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2701_;
}
else
{
lean_object* v___x_2702_; 
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2691_);
v___x_2702_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2666_, v_post_2668_, v___y_2695_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2702_;
}
}
}
v___jp_2703_:
{
if (v___y_2709_ == 0)
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
lean_dec_ref(v___y_2707_);
v___x_2710_ = l_Lean_Expr_forallE___override(v___y_2705_, v___y_2706_, v___y_2708_, v___y_2704_);
v___x_2711_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2666_, v_post_2668_, v___x_2710_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2711_;
}
else
{
uint8_t v___x_2712_; 
v___x_2712_ = l_Lean_instBEqBinderInfo_beq(v___y_2704_, v___y_2704_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
lean_dec_ref(v___y_2707_);
v___x_2713_ = l_Lean_Expr_forallE___override(v___y_2705_, v___y_2706_, v___y_2708_, v___y_2704_);
v___x_2714_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2666_, v_post_2668_, v___x_2713_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2714_;
}
else
{
lean_object* v___x_2715_; 
lean_dec_ref(v___y_2708_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
v___x_2715_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2666_, v_post_2668_, v___y_2707_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed(lean_object* v___x_2824_, lean_object* v_pre_2825_, lean_object* v_e_2826_, lean_object* v_post_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(v___x_2824_, v_pre_2825_, v_e_2826_, v_post_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v___y_2828_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(lean_object* v_pre_2833_, lean_object* v_post_2834_, lean_object* v_e_2835_, lean_object* v_a_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
lean_inc(v_a_2836_);
v___x_2840_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2840_, 0, lean_box(0));
lean_closure_set(v___x_2840_, 1, lean_box(0));
lean_closure_set(v___x_2840_, 2, v_a_2836_);
v___x_2841_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v___x_2840_, v___y_2837_, v___y_2838_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2873_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2844_ = v___x_2841_;
v_isShared_2845_ = v_isSharedCheck_2873_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2841_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2873_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg(v_a_2842_, v_e_2835_);
lean_dec(v_a_2842_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v___x_2847_; lean_object* v___f_2848_; lean_object* v___x_2849_; 
lean_del_object(v___x_2844_);
v___x_2847_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___closed__0));
lean_inc_ref(v_e_2835_);
v___f_2848_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed), 8, 4);
lean_closure_set(v___f_2848_, 0, v___x_2847_);
lean_closure_set(v___f_2848_, 1, v_pre_2833_);
lean_closure_set(v___f_2848_, 2, v_e_2835_);
lean_closure_set(v___f_2848_, 3, v_post_2834_);
v___x_2849_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg(v___f_2848_, v_a_2836_, v___y_2837_, v___y_2838_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___f_2851_; lean_object* v___x_2852_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc_n(v_a_2850_, 2);
lean_dec_ref_known(v___x_2849_, 1);
lean_inc(v_a_2836_);
v___f_2851_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2851_, 0, v_a_2836_);
lean_closure_set(v___f_2851_, 1, v_e_2835_);
lean_closure_set(v___f_2851_, 2, v_a_2850_);
v___x_2852_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v___f_2851_, v___y_2837_, v___y_2838_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2859_ == 0)
{
lean_object* v_unused_2860_; 
v_unused_2860_ = lean_ctor_get(v___x_2852_, 0);
lean_dec(v_unused_2860_);
v___x_2854_ = v___x_2852_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_dec(v___x_2852_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 0, v_a_2850_);
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2850_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
lean_dec(v_a_2850_);
v_a_2861_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___x_2852_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2852_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
else
{
lean_dec_ref(v_e_2835_);
return v___x_2849_;
}
}
else
{
lean_object* v_val_2869_; lean_object* v___x_2871_; 
lean_dec_ref(v_e_2835_);
lean_dec_ref(v_post_2834_);
lean_dec_ref(v_pre_2833_);
v_val_2869_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_val_2869_);
lean_dec_ref_known(v___x_2846_, 1);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v_val_2869_);
v___x_2871_ = v___x_2844_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_val_2869_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec_ref(v_e_2835_);
lean_dec_ref(v_post_2834_);
lean_dec_ref(v_pre_2833_);
v_a_2874_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2841_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2841_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(lean_object* v_pre_2882_, lean_object* v_post_2883_, lean_object* v_e_2884_, lean_object* v_a_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v___x_2889_; 
lean_inc_ref(v_post_2883_);
lean_inc(v___y_2887_);
lean_inc_ref(v___y_2886_);
lean_inc_ref(v_e_2884_);
v___x_2889_ = lean_apply_4(v_post_2883_, v_e_2884_, v___y_2886_, v___y_2887_, lean_box(0));
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2908_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2892_ = v___x_2889_;
v_isShared_2893_ = v_isSharedCheck_2908_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2889_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2908_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
switch(lean_obj_tag(v_a_2890_))
{
case 0:
{
lean_object* v_e_2894_; lean_object* v___x_2896_; 
lean_dec_ref(v_e_2884_);
lean_dec_ref(v_post_2883_);
lean_dec_ref(v_pre_2882_);
v_e_2894_ = lean_ctor_get(v_a_2890_, 0);
lean_inc_ref(v_e_2894_);
lean_dec_ref_known(v_a_2890_, 1);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v_e_2894_);
v___x_2896_ = v___x_2892_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_e_2894_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
case 1:
{
lean_object* v_e_2898_; lean_object* v___x_2899_; 
lean_del_object(v___x_2892_);
lean_dec_ref(v_e_2884_);
v_e_2898_ = lean_ctor_get(v_a_2890_, 0);
lean_inc_ref(v_e_2898_);
lean_dec_ref_known(v_a_2890_, 1);
v___x_2899_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2882_, v_post_2883_, v_e_2898_, v_a_2885_, v___y_2886_, v___y_2887_);
return v___x_2899_;
}
default: 
{
lean_object* v_e_x3f_2900_; 
lean_dec_ref(v_post_2883_);
lean_dec_ref(v_pre_2882_);
v_e_x3f_2900_ = lean_ctor_get(v_a_2890_, 0);
lean_inc(v_e_x3f_2900_);
lean_dec_ref_known(v_a_2890_, 1);
if (lean_obj_tag(v_e_x3f_2900_) == 0)
{
lean_object* v___x_2902_; 
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v_e_2884_);
v___x_2902_ = v___x_2892_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_e_2884_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
else
{
lean_object* v_val_2904_; lean_object* v___x_2906_; 
lean_dec_ref(v_e_2884_);
v_val_2904_ = lean_ctor_get(v_e_x3f_2900_, 0);
lean_inc(v_val_2904_);
lean_dec_ref_known(v_e_x3f_2900_, 1);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v_val_2904_);
v___x_2906_ = v___x_2892_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_val_2904_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
}
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
lean_dec_ref(v_e_2884_);
lean_dec_ref(v_post_2883_);
lean_dec_ref(v_pre_2882_);
v_a_2909_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2889_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2889_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_2917_, lean_object* v_post_2918_, lean_object* v_e_2919_, lean_object* v_a_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2917_, v_post_2918_, v_e_2919_, v_a_2920_, v___y_2921_, v___y_2922_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v_a_2920_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_2925_, lean_object* v_post_2926_, lean_object* v_sz_2927_, lean_object* v_i_2928_, lean_object* v_bs_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
size_t v_sz_boxed_2934_; size_t v_i_boxed_2935_; lean_object* v_res_2936_; 
v_sz_boxed_2934_ = lean_unbox_usize(v_sz_2927_);
lean_dec(v_sz_2927_);
v_i_boxed_2935_ = lean_unbox_usize(v_i_2928_);
lean_dec(v_i_2928_);
v_res_2936_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_2925_, v_post_2926_, v_sz_boxed_2934_, v_i_boxed_2935_, v_bs_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_2937_, lean_object* v_post_2938_, lean_object* v_x_2939_, lean_object* v_x_2940_, lean_object* v_x_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(v_pre_2937_, v_post_2938_, v_x_2939_, v_x_2940_, v_x_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___boxed(lean_object* v_pre_2947_, lean_object* v_post_2948_, lean_object* v_e_2949_, lean_object* v_a_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2947_, v_post_2948_, v_e_2949_, v_a_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_a_2950_);
return v_res_2954_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0(void){
_start:
{
lean_object* v_cellCount_2955_; lean_object* v___x_2956_; 
v_cellCount_2955_ = lean_unsigned_to_nat(16u);
v___x_2956_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2955_);
return v___x_2956_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2957_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0);
v___x_2958_ = lean_obj_once(&l_Lean_Expr_checkMaxShared___closed__0, &l_Lean_Expr_checkMaxShared___closed__0_once, _init_l_Lean_Expr_checkMaxShared___closed__0);
v___x_2959_ = lean_unsigned_to_nat(0u);
v___x_2960_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
lean_ctor_set(v___x_2960_, 1, v___x_2958_);
lean_ctor_set(v___x_2960_, 2, v___x_2957_);
return v___x_2960_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2961_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__1);
v___x_2962_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2962_, 0, lean_box(0));
lean_closure_set(v___x_2962_, 1, lean_box(0));
lean_closure_set(v___x_2962_, 2, v___x_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(lean_object* v_input_2963_, lean_object* v_pre_2964_, lean_object* v_post_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v_a_2971_; lean_object* v___x_2972_; 
v___x_2969_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__2);
v___x_2970_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v___x_2969_, v___y_2966_, v___y_2967_);
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_a_2971_);
lean_dec_ref(v___x_2970_);
v___x_2972_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2964_, v_post_2965_, v_input_2963_, v_a_2971_, v___y_2966_, v___y_2967_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_a_2973_);
lean_dec_ref_known(v___x_2972_, 1);
v___x_2974_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2974_, 0, lean_box(0));
lean_closure_set(v___x_2974_, 1, lean_box(0));
lean_closure_set(v___x_2974_, 2, v_a_2971_);
v___x_2975_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v___x_2974_, v___y_2966_, v___y_2967_);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_2982_ == 0)
{
lean_object* v_unused_2983_; 
v_unused_2983_ = lean_ctor_get(v___x_2975_, 0);
lean_dec(v_unused_2983_);
v___x_2977_ = v___x_2975_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_dec(v___x_2975_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 0, v_a_2973_);
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2973_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
else
{
lean_dec(v_a_2971_);
return v___x_2972_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___boxed(lean_object* v_input_2984_, lean_object* v_pre_2985_, lean_object* v_post_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_input_2984_, v_pre_2985_, v_post_2986_, v___y_2987_, v___y_2988_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels(lean_object* v_e_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
uint8_t v___x_2997_; 
v___x_2997_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_2993_);
if (v___x_2997_ == 0)
{
lean_object* v_pre_2998_; lean_object* v___f_2999_; lean_object* v___x_3000_; 
v_pre_2998_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___closed__0));
v___f_2999_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___closed__1));
v___x_3000_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_e_2993_, v_pre_2998_, v___f_2999_, v_a_2994_, v_a_2995_);
return v___x_3000_;
}
else
{
lean_object* v___x_3001_; 
v___x_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3001_, 0, v_e_2993_);
return v___x_3001_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___boxed(lean_object* v_e_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Lean_Meta_Sym_normalizeLevels(v_e_3002_, v_a_3003_, v_a_3004_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_3007_, lean_object* v_m_3008_, lean_object* v_a_3009_){
_start:
{
lean_object* v___x_3010_; 
v___x_3010_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg(v_m_3008_, v_a_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3011_, lean_object* v_m_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_00_u03b2_3011_, v_m_3012_, v_a_3013_);
lean_dec_ref(v_a_3013_);
lean_dec_ref(v_m_3012_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_3015_, lean_object* v_ref_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_3016_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3021_, lean_object* v_ref_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_3021_, v_ref_3022_, v___y_3023_, v___y_3024_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9(lean_object* v_00_u03b1_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg();
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___boxed(lean_object* v_00_u03b1_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9(v_00_u03b1_3032_, v___y_3033_, v___y_3034_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6(lean_object* v_00_u03b1_3037_, lean_object* v_x_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
lean_object* v___x_3043_; 
v___x_3043_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg(v_x_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3044_, lean_object* v_x_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6(v_00_u03b1_3044_, v_x_3045_, v___y_3046_, v___y_3047_, v___y_3048_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec(v___y_3046_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7(lean_object* v_00_u03b2_3051_, lean_object* v_m_3052_, lean_object* v_query_3053_){
_start:
{
lean_object* v___x_3054_; 
v___x_3054_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg(v_m_3052_, v_query_3053_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___boxed(lean_object* v_00_u03b2_3055_, lean_object* v_m_3056_, lean_object* v_query_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7(v_00_u03b2_3055_, v_m_3056_, v_query_3057_);
lean_dec_ref(v_query_3057_);
lean_dec_ref(v_m_3056_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8(lean_object* v_00_u03b2_3059_, lean_object* v_m_3060_){
_start:
{
lean_object* v___x_3061_; 
v___x_3061_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8___redArg(v_m_3060_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8___boxed(lean_object* v_00_u03b2_3062_, lean_object* v_m_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8(v_00_u03b2_3062_, v_m_3063_);
lean_dec_ref(v_m_3063_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_3065_, lean_object* v_m_3066_, lean_object* v_query_3067_){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg(v_m_3066_, v_query_3067_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___boxed(lean_object* v_00_u03b2_3069_, lean_object* v_m_3070_, lean_object* v_query_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5(v_00_u03b2_3069_, v_m_3070_, v_query_3071_);
lean_dec_ref(v_query_3071_);
lean_dec_ref(v_m_3070_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11(lean_object* v_00_u03b2_3073_, lean_object* v_m_3074_, lean_object* v_query_3075_, lean_object* v_x_3076_, lean_object* v_x_3077_, lean_object* v_x_3078_, lean_object* v_x_3079_){
_start:
{
lean_object* v___x_3080_; 
v___x_3080_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg(v_m_3074_, v_query_3075_, v_x_3076_, v_x_3077_, v_x_3078_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3081_, lean_object* v_m_3082_, lean_object* v_query_3083_, lean_object* v_x_3084_, lean_object* v_x_3085_, lean_object* v_x_3086_, lean_object* v_x_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11(v_00_u03b2_3081_, v_m_3082_, v_query_3083_, v_x_3084_, v_x_3085_, v_x_3086_, v_x_3087_);
lean_dec_ref(v_query_3083_);
lean_dec_ref(v_m_3082_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13(lean_object* v_00_u03b2_3089_, lean_object* v_init_3090_, lean_object* v_b_3091_){
_start:
{
lean_object* v___x_3092_; 
v___x_3092_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13___redArg(v_init_3090_, v_b_3091_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13___boxed(lean_object* v_00_u03b2_3093_, lean_object* v_init_3094_, lean_object* v_b_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13(v_00_u03b2_3093_, v_init_3094_, v_b_3095_);
lean_dec_ref(v_b_3095_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13_spec__14(lean_object* v_00_u03b2_3097_, lean_object* v_b_3098_, lean_object* v_acc_3099_, lean_object* v_i_3100_){
_start:
{
lean_object* v___x_3101_; 
v___x_3101_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13_spec__14___redArg(v_b_3098_, v_acc_3099_, v_i_3100_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13_spec__14___boxed(lean_object* v_00_u03b2_3102_, lean_object* v_b_3103_, lean_object* v_acc_3104_, lean_object* v_i_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__8_spec__13_spec__14(v_00_u03b2_3102_, v_b_3103_, v_acc_3104_, v_i_3105_);
lean_dec_ref(v_b_3103_);
return v_res_3106_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ForEachExpr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Util(builtin);
}
#ifdef __cplusplus
}
#endif
